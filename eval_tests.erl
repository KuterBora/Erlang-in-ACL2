-module(eval_tests).
-export([test_world/0, test_eval/0]).
-include_lib("eunit/include/eunit.hrl").


% Tests for evaluating function calls/guards
test_world() ->
  SimpleFun_temp1 = eval:module_add_function_string(#{}, greater, 2, "greater(X, Y) -> X > Y."),
  SimpleFun_temp2 = eval:module_add_function_string(SimpleFun_temp1, sum, 2, "sum(X, Y) -> X + Y."),
  SimpleFun_temp3 = eval:module_add_function_string(SimpleFun_temp2, sum, 3, "sum(X, Y, Z) -> X + Y + Z."),
  SimpleFun = eval:module_add_function_string(SimpleFun_temp3, concat, 2, "concat(X, Y) -> X ++ Y."),
  SimpleWorld = eval:world_add_module(#{}, simpleFun, SimpleFun),

  ?assertEqual({ok, true, []}, eval:eval_world("simpleFun:greater(10, 5).", [], SimpleWorld)),
  ?assertEqual({ok, 9, []}, eval:eval_world("simpleFun:sum(5, 4).", [], SimpleWorld)),
  ?assertEqual({ok, 15, []}, eval:eval_world("simpleFun:sum(5, 4, 6).", [], SimpleWorld)),
  ?assertEqual({ok, [1, 2, 3, 4], []}, eval:eval_world("simpleFun:concat([1, 2], [3, 4]).", [], SimpleWorld)),
  ?assertEqual({ok, 10, [{'X', 3}, {'Y', 7}]}, 
    eval:eval_world("simpleFun:sum(X, Y).", [{'X', 3}, {'Y', 7}], SimpleWorld)),
  
  GuardFun = eval:module_add_function_string(#{}, zero , 1,
    "zero(X) when X < 0 -> lesser;
     zero(X) when X == 0 -> zero;
     zero(X) when X > 0 -> greater."),
  GuardWorld = eval:world_add_module(SimpleWorld, guard_fun, GuardFun),

  ?assertEqual({ok, lesser, []}, eval:eval_world("guard_fun:zero(-5).", [], GuardWorld)),
  ?assertEqual({ok, zero, []}, eval:eval_world("guard_fun:zero(0).", [], GuardWorld)),
  ?assertEqual({ok, greater, []}, eval:eval_world("guard_fun:zero(6).", [], GuardWorld)),


% General Tests for the evalution of basic erlang statements/operations 
test_eval() ->
  ?assertEqual({ok, 29, []}, eval:eval_string("29.", [])),
  ?assertEqual({ok, 7, []},  eval:eval_string("4 + 3.", [])),
  ?assertEqual({ok, -29, []}, eval:eval_string("-29.", [])),
  ?assertEqual({ok, 7, []},  eval:eval_string("9 - 2.", [])),
  ?assertEqual({ok, 10, []}, eval:eval_string("19 - 25 + 4 - 5 + 17.", [])),
  ?assertEqual({ok, 24, []}, eval:eval_string("8 * 3.", [])),
  ?assertEqual({ok, 10, []}, eval:eval_string("20 div 2.", [])),
  ?assertEqual({ok, 92, []}, eval:eval_string("8 * (3 + 9) - (9 div 3 + 1).", [])),
  ?assertEqual({ok, 6, [{'X', 6}]}, eval:eval_string("X.", [{'X', 6}])),
  ?assertEqual({ok, 41, [{'X', 6}, {'Y', 5}, {'Z', 13}]}, 
    eval:eval_string("X + Y * (Z - X).", [{'X', 6}, {'Y', 5}, {'Z', 13}])),
  ?assertEqual({ok, 3, []}, eval:eval_string("1 + 2, 3.", [])),
  ?assertEqual({ok, 1, [{'X', 1}]}, eval:eval_string("X = 1.", [])),
  ?assertEqual({ok, 2, [{'X', 2}]}, eval:eval_string("X = 2.", [{'X', 2}])),
  ?assertEqual({ok, 2, []}, eval:eval_string("2 = 2.", [])),
  ?assertEqual({ok, 5, [{'X', 5}]}, eval:eval_string("X = 2 + 3.", [])),
  ?assertEqual({ok, 5, [{'X', 2}, {'Y', 3}]}, eval:eval_string("X = 2, Y = 3, X + Y.", [{'X', 2}])),
  ?assertEqual({ok, [1, 2, 3, 4], []}, eval:eval_string("[1, 2, 3, 4].", [])),
  ?assertEqual({ok, [1, 2, 3, 4, 5], [{'X', 5}]}, eval:eval_string("[1, 2, 3, 4, X].", [{'X', 5}])),
  ?assertEqual({ok, [1, 2, 3, 4], []}, eval:eval_string("[1, 2] ++ [3, 4].", [])),
  ?assertEqual({ok, [1, 2, 3], []}, eval:eval_string("[1 | [2, 3]].", [])),
  ?assertEqual({ok, here_is_an_atom, []}, eval:eval_string("here_is_an_atom.", [])),
  ?assertEqual({ok, "here is a string", []}, eval:eval_string("\"here is a string\".", [])),
  ?assertEqual({ok, "concat strings", []}, eval:eval_string("\"concat \" ++ \"strings\".", [])),
  ?assertEqual({ok, [1, 2, 3], []}, eval:eval_string("[1 | [2, 3]].", [])),
  ?assertEqual({ok, false, []}, eval:eval_string("5 > 6.", [])),
  ?assertEqual({ok, true, []}, eval:eval_string("atom1 == atom1.", [])),
  ?assertEqual({ok, true, []}, eval:eval_string("(true and false) or true.", [])),
  ?assertEqual({ok, true, [{'Bool1',true},{'Bool2',true},{'X',1},{'Y',2}]},
    eval:eval_string("Bool1 = X == 1, Bool2 = Y == 2, Bool1 and Bool2.", [{'X', 1}, {'Y', 2}])),
  ?assertEqual({ok, true, []}, eval:eval_string("if true -> true end.", [])),
  ?assertEqual({ok, 35, [{'X', 3}]}, eval:eval_string("if X == 1 -> 4; X == 3, X > 2 -> 35; true -> 2 end.", [{'X', 3}])),
  ?assertEqual({error, "No match of right hand side value."}, eval:eval_string("X = 2, X = 3.", [])),
  ?assertEqual({error, "Operation with given arguments is not recognized by the evaluator."}, 
    eval:eval_string("1 rem 2.", [])),               % should be allowed eventually.
  ?assertEqual({error, "Language in the AST is not recognized by the evaluator."}, 
    eval:eval_string("fun(_) -> 2 end, 1.", [])).  % should be allowed eventually.