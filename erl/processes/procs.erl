-module(procs).
-export([empty_box/0, init_state/0, eval_procs/3, eval_procs/1]).

% Initial data sturctures
init_state() ->
    #{ module => '#none', pid => {pid, 0}}.

empty_box() ->
    {[], []}.

% Processes is a map from Pid to Process
% Process is one of
%  - {exec, {init, ProcState, ASTs}, Inbox}
%  - {term, {ok, ExitValue, Bindings, Out}}
%  - {term, {error, Exception, Out}}
%  - {block, {yield, Bindings, Out, ProcState, K}, Inbox}

% Network is a list of messages  
% inbox is list of messages, first in first out

eval_procs(Processes, Network, World) ->
    All_Terminated = terminated(Processes),
    All_Blocked = blocked(Processes),
    if
        All_Terminated ->
            {ok, Processes};
        All_Blocked andalso Network == [] ->
            {deadlock, Processes};
        true ->
            run(Processes, Network, World)
    end.

eval_procs(Processes) ->
    eval_procs(Processes, [], world:world_init()).

terminated(Processes) ->
    lists:foldl(
        fun(Proc, AccIn) ->
            case Proc of
                {term, _} ->
                    AccIn;
                _ ->
                    false
            end
        end,
        true,
        Processes
    ).

blocked(Processes) ->
    lists:foldl(
        fun(Proc, AccIn) ->
            case Proc of
                {block, _, _}->
                    AccIn;
                {term, _} ->
                    AccIn;
                _ ->
                    false
            end
        end,
        true,
        Processes
    ).

run(Processes, Network, World) ->
    % io:format("\nDelivering Network: ~p", [Network]),
    Delivered = deliverNetwork(Processes, Network),
    % io:format("\nExecuting Processes: ~p", [Delivered]),
    Executed = lists:map(
        fun(Process) ->
            case Process of
                {exec, {init, ProcState, ASTs}, Inbox} ->
                    Result = eval:eval_exprs(ASTs, [], ProcState, World),
                    case Result of
                        {ok, _, _, _} ->
                            {term, Result};
                        {error, _, _} ->
                            {term, Result};
                        {yield, _, _, _, _} ->
                            {block, Result, Inbox}
                    end;
                {term, _} ->
                    Process;
                {block, Kont, Inbox} ->
                    {yield, Bindings, Out, ProcState, K} = Kont,
                    {NewInbox, Result} = attempt_receive(Inbox, Bindings, Out, ProcState, K, World),
                    case Result of
                       {ok, _, _, _} ->
                            {term, Result};
                        {error, _, _} ->
                            {term, Result};
                        {yield, _, _, _, _} ->
                            {block, Result, NewInbox}
                    end
            end
        end,
        Delivered
    ),
    % io:format("\nObtained: ~p", [Executed]),
    {NewProcesses, NewNetwork} = exctractNework(Executed),
    % io:format("\nExtracted Network: ~p", [NewNetwork]),
    eval_procs(NewProcesses, NewNetwork, World).

% returns NewInbox Result
attempt_receive([], Bindings, Out, ProcState, K, _) ->
    {[], {yield, Bindings, Out, ProcState, K}};
attempt_receive(Inbox, Bindings, Out, ProcState, K, World) ->
    Attempt = cps:applyK(hd(Inbox), Bindings, Out, ProcState, World, K),
    case Attempt of
        {ok, _, _, _} ->
            {tl(Inbox), Attempt};
        {yield, _, _, _, _} ->
            {tl(Inbox), Attempt};
        {error, {case_clause, _}, Out} -> % handle this properly at some point
            {NewInbox, Result} = attempt_receive(tl(Inbox), Bindings, Out, ProcState, World, K),
            {[hd(Inbox) | NewInbox], Result}
    end.

% return listof Process
deliverNetwork(Processes, []) -> Processes;
deliverNetwork(Processes, Netwok) ->
    {Pid, Message} = hd(Netwok),
    NewProcesses = deliverMessage(Pid, Message, Processes),
    deliverNetwork(NewProcesses, tl(Netwok)).

% return listof Process
deliverMessage(_, _Message, []) -> 
    % io:format("\n Failed to deliver Message: ~p", [Message]),
    [];
deliverMessage(Pid, Message, Processes) ->
    case hd(Processes) of
        {block, {yield, Bindings, Out, ProcState, K}, Inbox} ->
            % io:format("\nSent to: ~p", [Pid]),
            % io:format("\nAttempt: ~p", [maps:get(pid, ProcState)]),
            case maps:get(pid, ProcState) of
                Pid ->
                    % io:format("\n Delivering Message: ~p", [Message]),
                    [{block, {yield, Bindings, Out, ProcState, K}, Inbox ++ [Message]} | tl(Processes)];
                _ ->
                    [hd(Processes) | deliverMessage(Pid, Message, tl(Processes))]
            end;
        _ ->
            [hd(Processes) | deliverMessage(Pid, Message, tl(Processes))]
    end.


% return {NewProcesses, NewNetwork}
% also handle spawn here
exctractNework([]) ->
    {[], []};
exctractNework(Processes) ->
    {NewProcesses, NewNetwork} = exctractNework(tl(Processes)),
    case hd(Processes) of
        {exec, _, _} ->
            {[hd(Processes) | NewProcesses], NewNetwork};
        {term, {ok, ExitValue, Bindings, {Sent, _Spawned}}} ->
            {
                [{term, {ok, ExitValue, Bindings, empty_box()}} | NewProcesses], 
                lists:append(Sent, NewNetwork)
            };
        {term, {error, Exception, {Sent, _Spawned}}} ->
            {
                [{term, {error, Exception, empty_box()}} | NewProcesses], 
                lists:append(Sent, NewNetwork)
            };

        {block, Kont, Inbox} ->
            {yield, Bindings, {Sent, _Spawned}, ProcState, K} = Kont,
            NewKont = {yield, Bindings, empty_box(), ProcState, K},
            {
                [{block, NewKont, Inbox} | NewProcesses], 
                lists:append(Sent, NewNetwork)
            } 
    end.