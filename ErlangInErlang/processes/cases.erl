-module(cases).
-export([eval_guards/5, eval_if/5, eval_case/6]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Guards/if/case/try
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a list of guards: return true if every expression evaluates to true.
% Guards cannot have matches, send, or function calls except BIFs.
% REMARK: guards cannot make matches or send messages. or spwan
% TODO: set the box to empty, and the module to none before calling this function.
% somehow assure it cannot call illegal stuff
eval_guards([], _, _, _, _) -> true;
eval_guards([Guard | Rest], Bindings, OutBox, ProcState, World) ->
    GuardResult = eval:eval_expr(Guard, Bindings, OutBox, ProcState, World),
    case GuardResult of
        {ok, {atom, true}, Bindings, OutBox} -> 
            eval_guards(Rest, Bindings, OutBox, ProcState, World);
        {ok, {atom, false}, Bindings, OutBox} ->
            false;
        {yield, _, _, _} ->
            {error, illegal_guard, OutBox};
        _ -> 
            {error, illegal_guard, OutBox}
    end.

% Evaluate an if clause by recursively checking if the guards hold
eval_if([], _, OutBox, _, _) -> {error, if_clause, OutBox};
eval_if([HdClause | TlClauses], Bindings, OutBox, ProcState, World) ->
    {clause, _Line, [], [Guards], Body} = HdClause,
    EvalGuards = eval_guards(Guards, Bindings, procs:empty_box(), ProcState, world:world_init()),
    if 
        EvalGuards ->
            eval:eval_exprs(Body, Bindings, OutBox, ProcState, World);
        true -> 
            eval_if(TlClauses, Bindings, OutBox, ProcState, World)
    end.

% Evaluate a case expression by recursively checking if the match
% and the guards hold.
% receive is not allowed in LHS
% TODO: are you allowed to send messages on a case clause??
eval_case(Value, [], _, OutBox, _, _) -> {error, {case_clause, Value}, OutBox};
eval_case(Value, [HdClause | TlClauses], Bindings, OutBox, ProcState, World) ->
    {clause, _Line, [Case], Guards, Body} = HdClause,
    TryMatch = match:eval_match(Case, Value, Bindings, OutBox, ProcState,  World),
    case TryMatch of
        {ok, _Result, NewBindings, NewOutBox} ->
            GuardResult = 
                case Guards of
                    [] ->
                        true;
                    [GuardList] ->
                        eval_guards(
                            GuardList,
                            NewBindings,
                            procs:empty_box(),
                            ProcState,
                            world:world_init()
                        );
                    _ ->
                        {error, illegal_guard}
                end,
            if
                GuardResult ->
                    eval:eval_exprs(Body, NewBindings, NewOutBox, ProcState, World);
                true ->
                    eval_case(Value, TlClauses, Bindings, OutBox, ProcState, World)
            end;
        {yield, _, _, _} ->
            {error, illegal_pattern};
        {error, {badmatch, Value}, _} ->
            eval_case(Value, TlClauses, Bindings, OutBox, ProcState, World);
        _ ->
            TryMatch
    end.