-module(procs).
-export([empty_box/0, init_state/0, eval_procs/3]).

% Initial data sturctures
init_state() ->
    #{ module => '#none', pid => {pid, '<0.0.0>'}}.

empty_box() ->
    {[], []}.

% Processes is a map from Pid to Process
% Process is one of
%  - {exec, {init, ProcState, AST}, Inbox}
%  - {term, {ok, ExitValue, Bindings, Out}}
%  - {term, {error, Exception, Out}}
%  - {block, {yield, Bindings, Out, ProcState, K}, Inbox}

% Network is a map from pid to messages sent   

eval_procs(Processes, Network, World) ->
    Terminated = terminated(Processes),
    Blocked = blocked(Processes),
    if
        Terminated ->
            {ok, Processes};
        Blocked andalso Network == #{} ->
            {deadlock, Processes};
        Blocked ->
            run(Processes, Network, World);
        true ->
            {error, Processes}
    end.

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
                {block, _}->
                    AccIn;
                _ ->
                    false
            end
        end,
        true,
        Processes
    ).

run(Processes, Network, World) ->
    Delivered = deliverNetwork(Processes, Network),
    Executed = lists:map(
        fun(Process) ->
            case Process of
                {exec, {init, ProcState, AST}, Inbox} ->
                    case eval:eval(AST, [], ProcState, World) of
                        {ok, Value, Bindings, Out} ->
                            {term, {ok, Value, Bindings, Out}};
                        {error, Exception, Out} ->
                            {term, {error, Exception, Out}};
                        {yield, Bindings, Out, ProcState, K} ->
                            {block, {yield, Bindings, Out, ProcState, K}, Inbox}
                    end;
                {term, _} ->
                    Process;
                {block, Kont, Inbox} ->
                    receive_and_run(Kont, Inbox, World)
            end
        end,
        Delivered
    ),
    {NewProcesses, NewNetwork} = createNework(Executed),
    eval_procs(NewProcesses, NewNetwork, World).

receive_and_run(_Kont, _Inbox, _World) ->
    todo.

deliverNetwork(_Processes, _Netwok) ->
    todo.

createNework(_Processes) ->
    todo.