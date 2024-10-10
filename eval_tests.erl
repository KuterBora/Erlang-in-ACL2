-module(eval_tests).
-export([test_world/0, test_eval/0, test_matches/0, test_all/0]).
-include_lib("eunit/include/eunit.hrl").

% Run all tests
test_all() ->
  test_eval(),
  test_world(),
  test_matches().

% Tests for evaluating match for lists and tuples as well as Pattern Matching
test_matches() ->
  ?assertEqual({ok, [7, 8, 9, abc], [{'X', [7, 8, 9, abc]}]}, eval:eval_string("X = [7, 8, 9, abc].", [])),
  ?assertEqual({ok, [a, b, c], [{'H', a}, {'T', [b, c]}]}, eval:eval_string("[H | T] = [a, b, c].", [{'H', a}, {'T', [b, c]}])),
  ?assertEqual({ok, [a, b, c], [{'H', a}, {'T', [b, c]}]}, eval:eval_string("[H | T] = [a, b, c].", [{'H', a}])),
  ?assertEqual({ok, [a, b, c], [{'H', a}, {'T', [b, c]}]}, eval:eval_string("[H | T] = [a, b, c].", [{'T', [b, c]}])),
  ?assertEqual({ok, [a, b, c], [{'H', a}, {'T', [b, c]}]}, eval:eval_string("[H | T] = [a, b, c].", [])),
  ?assertEqual({ok, [a, b, c], [{'H', a}]}, eval:eval_string("[H | [b, c]] = [a, b, c].", [])),
  ?assertEqual({ok, [a, b, c], [{'T', [b, c]}]}, eval:eval_string("[a | T] = [a, b, c].", [])).

% Tests for evaluating function calls/guards
test_world() ->
  % world_init
  ?assertEqual({ok, true, [{'X', 5}]}, eval:eval_world("is_integer(X).", [{'X', 5}], world:world_init())),
  ?assertEqual({ok, false, []}, eval:eval_world("is_integer(abc).", [], world:world_init())),
  % ?assertEqual({ok, head, []}, eval:eval_world("hd([head, tail]).", [], world:world_init())),
  % ?assertEqual({ok, tail, []}, eval:eval_world("tl([head, tail]).", [], world:world_init())),

  % simple functions
  SimpleModule_temp1 = world:module_add_function_string(#{}, greater, 2, "greater(X, Y) -> X > Y."),
  SimpleModule_temp2 = world:module_add_function_string(SimpleModule_temp1, sum, 2, "sum(X, Y) -> X + Y."),
  SimpleModule_temp3 = world:module_add_function_string(SimpleModule_temp2, sum, 3, "sum(X, Y, Z) -> X + Y + Z."),
  SimpleModule = world:module_add_function_string(SimpleModule_temp3, concat, 2, "concat(X, Y) -> X ++ Y."),
  SimpleWorld = world:world_add_module(world:world_init(), simple_module, SimpleModule),

  ?assertEqual({ok, true, []}, eval:eval_world("simple_module:greater(10, 5).", [], SimpleWorld)),
  ?assertEqual({ok, 9, []}, eval:eval_world("simple_module:sum(5, 4).", [], SimpleWorld)),
  ?assertEqual({ok, 15, []}, eval:eval_world("simple_module:sum(5, 4, 6).", [], SimpleWorld)),
  ?assertEqual({ok, [1, 2, 3, 4], []}, eval:eval_world("simple_module:concat([1, 2], [3, 4]).", [], SimpleWorld)),
  ?assertEqual({ok, 10, [{'X', 3}, {'Y', 7}]}, 
    eval:eval_world("simple_module:sum(X, Y).", [{'X', 3}, {'Y', 7}], SimpleWorld)),
  
  % functions with guards
  GuardModule = world:module_add_function_string(#{}, zero , 1,
    "zero(X) when X < 0 -> lesser;
     zero(X) when X == 0 -> zero;
     zero(X) when X > 0 -> greater."),
  GuardWorld = world:world_add_module(SimpleWorld, guard_module, GuardModule),

  ?assertEqual({ok, lesser, []}, eval:eval_world("guard_module:zero(-5).", [], GuardWorld)),
  ?assertEqual({ok, zero, []}, eval:eval_world("guard_module:zero(0).", [], GuardWorld)),
  ?assertEqual({ok, greater, []}, eval:eval_world("guard_module:zero(6).", [], GuardWorld)),

  % recursive functions
  RecursiveModule = world:module_add_function_string(#{}, guarded_fac, 1,
    "guarded_fac(N) when N == 0 -> 1;\nguarded_fac(N) when is_integer(N), 0 < N -> N * guarded_fac(N-1).\n"),
  RecursiveWorld = world:world_add_module(GuardWorld, recursive_module, RecursiveModule),

  ?assertEqual({ok, 1, []}, eval:eval_world("recursive_module:guarded_fac(0).", [], RecursiveWorld)),
  ?assertEqual({ok, 6, []}, eval:eval_world("recursive_module:guarded_fac(3).", [], RecursiveWorld)),
  ?assertEqual({ok, 5040, []}, eval:eval_world("recursive_module:guarded_fac(7).", [], RecursiveWorld)),
  ?assertEqual({error, "no function matching given arguments."}, 
    eval:eval_world("recursive_module:guarded_fac(-2).", [], RecursiveWorld)),

  % purging a module
  PurgedWorld = world:world_purge_module(RecursiveWorld, recursive_module),
  
  % Factorial at Last
  FactorialModule = world:module_add_function_string(RecursiveModule, fac, 1,
    "fac(0) -> 1;\n fac(N) when is_integer(N), 0 < N -> N * fac(N-1).\n"),
  FactorialWorld = world:world_add_module(PurgedWorld, factorial_module, FactorialModule),

  ?assertEqual({ok, 1, []}, eval:eval_world("factorial_module:fac(0).", [], FactorialWorld)),
  ?assertEqual({ok, 6, []}, eval:eval_world("factorial_module:fac(3).", [], FactorialWorld)),
  ?assertEqual({ok, 5040, []}, eval:eval_world("factorial_module:fac(7).", [], FactorialWorld)),
  ?assertEqual({error, "no function matching given arguments."}, 
    eval:eval_world("factorial_module:fac(-2).", [], FactorialWorld)).

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
  ?assertEqual({ok, true, [{'X', 1}]}, eval:eval_string("try X =:= X div 1 catch error:E -> false end.", [{'X', 1}])),
  ?assertEqual({ok, false, [{'X', 2.0}]}, eval:eval_string("try X =:= X div 1 catch error:E -> false end.", [{'X', 2.0}])),
  ?assertEqual({ok, false, [{'X', "abc"}]}, eval:eval_string("try X =:= X div 1 catch error:E -> false end.", [{'X', "abc"}])),
  ?assertEqual({ok, true, [{'X', 3}]}, eval:eval_string("is_integer(X).", [{'X', 3}])),
  ?assertEqual({ok, {1, 2, abc, 4}, [{'X', 4}]}, eval:eval_string("{1, 2, abc, X}.", [{'X', 4}])),
  ?assertEqual({ok, {1, 2, 3}, [{'X', {1, 2, 3}}]}, eval:eval_string("X = {1, 2, 3}.", [])),
  ?assertEqual({error, "No match of right hand side value."}, eval:eval_string("X = 2, X = 3.", [])),
  ?assertEqual({error, "Operation with given arguments is not recognized by the evaluator."}, 
    eval:eval_string("1 rem 2.", [])),               % should be allowed eventually.
  ?assertEqual({error, "Language in the AST is not recognized by the evaluator."}, 
    eval:eval_string("fun(_) -> 2 end, 1.", [])).  % should be allowed eventually.