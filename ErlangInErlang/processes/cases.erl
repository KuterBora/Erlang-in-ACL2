-module(cases).
-export([eval_guards/4, eval_if/4, eval_case/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Guards/if/case/try
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a list of guards: return true if every expression evaluates to true.
% Guards cannot have matches, send, or function calls except BIFs.
% TODO: illegal guard expressions shoul not be allowed
eval_guards([], Bindings, World, K) -> 
    cps:applyK(
        {atom, true},
        Bindings,
        World,
        K
    );
eval_guards([Guard | Rest], Bindings, World, K) ->
    eval:eval_expr(
        Guard,
        Bindings,
        World,
        {guard_k, Rest, Bindings, K} 
    ).

% Evaluate an if clause by checking if the guards hold
eval_if([], _, World, K) -> 
    cps:errorK(if_clause, World, K);
eval_if([HdClause | TlClauses], Bindings, World, K) ->
    {clause, _Line, [], [Guards], Body} = HdClause,
    eval_guards(
        Guards,
        Bindings, 
        World,
        {if_k, Body, Bindings, TlClauses, K}).

% % Evaluate a case expression by recursively checking if the match
% % and the guards hold.
% TODO: LHS must be a pattern (no receive, no fun)
eval_case(Value, [], _, World, K) -> 
    cps:errorK({case_clause, Value}, World, K);
eval_case(Value, [HdClause | TlClauses], Bindings, World, K) -> 
    {clause, _Line, [Case], Guards, Body} = HdClause,
    match:eval_match(
        Case,
        Value,
        Bindings,
        World,
        {case_match_k, Value, Guards, Body, Bindings, TlClauses, K}).