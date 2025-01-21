-module(cases).
-export([eval_guards/6, eval_if/6, eval_case/7]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Guards/if/case/try
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a list of guards: return true if every expression evaluates to true.
% Guards cannot have matches, send, or function calls except BIFs.
% TODO: illegal guard expressions shoul not be allowed
eval_guards([], Bindings, Out, ProcState, World, K) -> 
    cps:applyK(
        {atom, true},
        Bindings,
        Out,
        ProcState,
        World,
        K
    );
eval_guards([Guard | Rest], Bindings, Out, ProcState, World, K) ->
    eval:eval_expr(
        Guard,
        Bindings,
        Out,
        ProcState,
        World,
        {guard_k, Rest, Bindings, K} 
    ).

% Evaluate an if clause by checking if the guards hold
eval_if([], _, Out, ProcState, World, K) -> 
    cps:errorK(if_clause, Out, ProcState, World, K);
eval_if([HdClause | TlClauses], Bindings, Out, ProcState, World, K) ->
    {clause, _Line, [], [Guards], Body} = HdClause,
    eval_guards(
        Guards,
        Bindings, 
        Out,
        ProcState,
        World,
        {if_k, Body, Bindings, TlClauses, K}).

% % Evaluate a case expression by recursively checking if the match
% % and the guards hold.
% TODO: LHS must be a pattern (no receive, no fun)
eval_case(Value, [], _, Out, ProcState, World, K) -> 
    cps:errorK({case_clause, Value}, Out, ProcState, World, K);
eval_case(Value, [HdCl | TlCls], Bindings, Out, ProcState, World, K) -> 
    {clause, _Line, [Case], Guards, Body} = HdCl,
    match:eval_match(
        Case,
        Value,
        Bindings,
        Out,
        ProcState,
        World,
        {case_match_k, Value, Guards, Body, Bindings, TlCls, K}).