-module(cases).
-export([eval_guards/3, eval_if/3, eval_case/4, eval_try/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Guards/if/case/try
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a list of guards: return true if every expression evaluates to true.
% Guards cannot have matches, send, or function calls except BIFs.
eval_guards([], _, _) -> true;
eval_guards([Guard | Rest], Bindings, World) ->
    GuardResult = eval:eval_expr(Guard, Bindings, World),
    case GuardResult of
        {ok, {atom, true}, Bindings} -> 
            eval_guards(Rest, Bindings, World);
        {ok, {atom, false}, Bindings} -> 
            false;
        {yield, _Kont, _Out} ->
            yield_todo;
        _ -> 
            {error, illegal_guard}
    end.

% Evaluate an if clause by recursively checking if the guards hold
eval_if([], _, _) -> {error, if_clause};
eval_if([HdClause | TlClauses], Bindings, World) ->
    {clause, _Line, [], [Guards], Body} = HdClause,
    EvalGuards = eval_guards(Guards, Bindings, world:world_init()),
    if 
        EvalGuards ->
            eval:eval_exprs(Body, Bindings, World);
        true -> 
            eval_if(TlClauses, Bindings, World)
    end.

% Evaluate a case expression by recursively checking if the match
% and the guards hold.
eval_case(Value, [], _, _) -> {error, {case_clause, Value}};
eval_case(Value, [HdClause | TlClauses], Bindings, World) ->
    {clause, _Line, [Case], Guards, Body} = HdClause,
    TryMatch = match:eval_match(Case, Value, Bindings, World),
    case TryMatch of
        {ok, _Result, NewBindings} ->
            GuardResult = case Guards of
                            [] ->
                                true;
                            [GuardList] ->
                                eval_guards(
                                    GuardList,
                                    NewBindings,
                                    world:world_init()
                                );
                            _ ->
                                {error, illegal_guard}
                            end,
            if
                GuardResult ->
                    eval:eval_exprs(Body, NewBindings, World);
                true ->
                    eval_case(Value, TlClauses, Bindings, World)
            end;
        {yield, _Kont, _Out} ->
            yield_todo;
        {error, {badmatch, Value}} ->
            eval_case(Value, TlClauses, Bindings, World);
        _ ->
            TryMatch
    end.

% Evaluate a try catch expression (incomplete)
eval_try(Exprs, [], _, Bindings, World) ->
    Eval_Result = eval:eval_exprs(Exprs, Bindings, World),
    case Eval_Result of
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings};
        {yield, _Kont, _Out} -> yield_todo;
        {error, _} -> {ok, {atom, false}, Bindings}
    end.