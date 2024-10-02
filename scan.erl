-module(scan).

-export([evaluate/2, getAST/1, testEvaluate/0]).
 
expressionAsString() -> 
    %"A = Y == 2, B = X == 1, Result = A and B.".
    "Z = X + Y, F = fun(R) -> R * 2 end, F(Z).".

getAST(Str) ->
    {ok, Tokens, CurrentLineNumber} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_exprs(Tokens),
    AST.

evaluate(AST, Bindings) ->
    {value, Result, NewBindings} = erl_eval:exprs(AST, Bindings),
    Result.

testEvaluate() ->
    AST = getAST(expressionAsString()),
    Bindings = [{'X', 1}, {'Y', 2}],
evaluate(AST, Bindings).
