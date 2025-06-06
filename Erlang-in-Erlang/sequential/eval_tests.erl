-module(eval_tests).
-export([test_general/0, test_all/0]).
-include_lib("eunit/include/eunit.hrl").

% Run all tests
test_all() ->
  test_general(),
  test_matches(),
  test_world(),
  test_bindings(),
  test_fun(),
  test_bif().


% Tests for built in functions
test_bif() ->
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_integer(3).", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_integer([1, 2, 3]).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_atom(atom).", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_atom(3).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_boolean(true).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_boolean(false).", [])),
  ?assertEqual({ok, {atom, false}, [{'X', not_bool}]}, eval:eval("is_boolean(X).", [{'X', not_bool}])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_float(3).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_float(3.0).", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_function(1).", [])),
  ?assertMatch({ok, {atom, true}, [_]}, eval:eval("is_function(fun() -> 1 end).", [])),
  ?assertMatch({ok, {atom, true}, [{'X', _}, _]}, 
    eval:eval(
      "X = fun(A, B) -> A + B end,
      is_function(X).", 
    [])
  ),
  ?assertMatch({ok, {atom, true}, [_, _]}, 
    eval:eval("is_function(X, 0).", [{'X', {'fun', {'#Fun<1.4662>',0}}},
    {{'#Fun<1.4662>',0}, {{clauses,[{clause,1,[],[],[{integer,1,1}]}]},[]}}])
  ),
  ?assertMatch({ok, {atom, false}, [_, _]}, 
    eval:eval("is_function(X, 1).", [{'X', {'fun', {'#Fun<1.4662>',0}}},
    {{'#Fun<1.4662>',0}, {{clauses,[{clause,1,[],[],[{integer,1,1}]}]},[]}}])
  ),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_integer(3).", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_integer(a).", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_list(3).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_list([1, 2, 3]).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_list([1 | [2]]).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_number(75 / 2).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_list([1, 2, 3]).", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_tuple([1, 2, 3]).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_tuple({1, 2, 3}).", [])),
  ?assertEqual({ok, {integer, 8}, []}, eval:eval("abs(-8).", [])),
  ?assertEqual({ok, {atom, two}, []}, eval:eval("element(2, {1, two, 3}).", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("is_list([1, 2, 3]).", [])),
  ?assertEqual({ok, {integer, 1}, []}, eval:eval("hd([1, 2, 3]).", [])),
  ?assertEqual({ok, {integer, 3}, []}, eval:eval("length([1, 2, 3]).", [])),
  ?assertEqual({ok, {integer, 1}, []}, eval:eval("hd([1, 2, 3]).", [])),
  ?assertEqual({ok, {integer, 30}, []}, eval:eval("max(30, 2.0).", [])),
  ?assertEqual({ok, {integer, -1}, []}, eval:eval("min(-1, 2).", [])),
  ?assertEqual({ok, {cons, [{integer, 2}, {integer, 3}]}, []}, eval:eval("tl([1, 2, 3]).", [])).

% Tests for fun expressions
test_fun() ->
  % simple fun, no arguments
  ?assertMatch({ok, {'fun', Name}, [{Name, {{clauses, [{clause,1,[],[],[{integer,1,1}]}]}, []}}]},
    eval:eval("fun() -> 1 end.", [])),

  % bind to a variable
  ?assertMatch({ok, {'fun', Name}, [{'X', {'fun', Name}}, 
    {Name, {{clauses, [{clause,1,[],[],[{integer,1,1}]}]}, []}}]},
    eval:eval("X = fun() -> 1 end.", [])),

  % call to simple fun
  ?assertMatch({ok, {integer, 1}, [{'X', {'fun', Name}}, 
    {Name, {{clauses, [{clause,1,[],[],[{integer,1,1}]}]}, []}}]},
    eval:eval("X = fun() -> 1 end, X().", [])),

  % call right away (fun())()
  ?assertMatch({ok, {integer, 1}, [{{_, 0}, {{clauses, [{clause,1,[],[],[{integer,1,1}]}]}, []}}]},
    eval:eval("(fun() -> 1 end)().", [])),

  % single argument
  ?assertMatch({ok, {integer, 3}, [{'X', {'fun', Name}},
    {Name, {{clauses,[{clause,1,[{var,1,'X'}],[], [{op,1,'+',{var,1,'X'},{integer,1,1}}]}]}, []}}]},
    eval:eval("X = fun(X) -> X + 1 end, X(2).", [])),

  % many arguments
  ?assertMatch({ok, {integer, 6}, [ {'X', {'fun', Name}},
    {Name, {{clauses,[{clause,1, [{var,1,'X'},{var,1,'Y'},{var,1,'Z'}], [],
    [{op,1,'+', {op,1,'+',{var,1,'X'},{var,1,'Y'}}, {var,1,'Z'}}]}]}, []}}]},
    eval:eval("X = fun(X, Y, Z) -> X + Y + Z end, X(1, 2, 3).", [])),

  % pattern matching
  ?assertMatch({ok, {integer, 1}, [{'X', {'fun', Name}},
    {Name, {{clauses,[{clause,1,[{integer,1,1}],[],[{integer,1,1}]},
    {clause,1,[{integer,1,2}],[],[{integer,1,2}]},
    {clause,1,[{var,1,'_'}],[],[{integer,1,3}]}]}, []}}]},
    eval:eval("X = fun(1) -> 1; (2) -> 2; (_) -> 3 end, X(1).", [])),
  ?assertMatch({ok, {integer, 2}, [{'X', {'fun', Name}},
    {Name, {{clauses,[{clause,1,[{integer,1,1}],[],[{integer,1,1}]},
    {clause,1,[{integer,1,2}],[],[{integer,1,2}]},
    {clause,1,[{var,1,'_'}],[],[{integer,1,3}]}]}, []}}]},
    eval:eval("X = fun(1) -> 1; (2) -> 2; (_) -> 3 end, X(2).", [])),
  ?assertMatch({ok, {integer, 3}, [{'X', {'fun', Name}},
    {Name, {{clauses,[{clause,1,[{integer,1,1}],[],[{integer,1,1}]},
    {clause,1,[{integer,1,2}],[],[{integer,1,2}]},
    {clause,1,[{var,1,'_'}],[],[{integer,1,3}]}]}, []}}]},
    eval:eval("X = fun(1) -> 1; (2) -> 2; (_) -> 3 end, X(3).", [])),  
  ?assertMatch({ok, {integer, 1}, [{'X', {cons, [{'fun', Name}]}}, {'Y', {'fun', Name}}, 
    {Name, {_, []}}]},
    eval:eval("X = [fun() -> 1 end], [Y] = X, Y().", [])),

  % bindings received during creation being used in the fun
  ?assertMatch({ok, {integer, 3}, [{'X', {'fun', Name}}, {'Y', {integer, 1}}, {Name, _}]},
    eval:eval("Y = 1, X = fun(X) -> X + Y end, X(2).", [])),
  ?assertMatch({ok, {integer, 15}, [{'Y', {'fun', _}}, {'Z', {'fun', _}},
    {{_, 0}, _}, {{_, 0}, _}]},
    eval:eval(
      "Z = fun() -> Y = 3, Y * 5 end, 
       Y = fun() -> Z end,
       (Y())().", [])),
  
  % simple functions
  FunModule_temp1 = world:module_add_function_string(#{}, square, 1, 
    "square(X) -> Y = fun(X) -> X * X end, Y(X)."),
  FunModule_temp2 = world:module_add_function_string(FunModule_temp1, adder, 1, "adder(X) -> fun(Y) -> X + Y end."),
  FunModule = world:module_add_function_string(FunModule_temp2, apply, 2, "apply(X, Y) -> X(Y)."),
  FunWorld = world:world_add_module(world:world_init(), fun_module, FunModule),

  ?assertMatch({ok, {integer, 100}, []}, 
    eval:eval("fun_module:square(10).", [], FunWorld)),
  ?assertMatch({ok, {integer, 5}, [{'X', _}, {_,  _}]}, 
    eval:eval("X = fun_module:adder(3), X(2).", [], FunWorld)),
  ?assertMatch({ok, {integer, 5}, [{'X', _}, {_,  _}]}, 
    eval:eval("X = fun_module:adder(3), fun_module:apply(X, 2).", [], FunWorld)),
  ?assertMatch({ok, {integer, 3}, [_]}, 
    eval:eval("fun_module:apply(fun(X) -> X + 1 end, 2).", [], FunWorld)),
  ?assertMatch({ok, {integer, 5}, [{'X', _}, {_, _}]}, 
    eval:eval("X = fun_module:adder(3), fun_module:apply(X, 2).", [], FunWorld)),
  
  % extra tests
  ?assertMatch({ok, {integer, 5}, [_, _, _]},
    eval:eval("X = fun(X) -> X + Y + 1 end, X(2).", [{'Y', {integer, 2}}])),
  ?assertMatch({ok, {integer, 5}, [_, _, _]},
    eval:eval("X = fun(Z) -> Z + 3 end, X(2).", [{'Z', {integer, 100}}])),
  ?assertMatch({ok, {integer, 5}, [_, _]},
    eval:eval("X = fun(Z = 5) -> Z end, X(5).", [])).

% Tests for evaluating match for lists and tuples as well as Pattern Matching
test_matches() ->
  ?assertEqual({ok, {cons, [{integer, 7}, {integer, 8}, {integer, 9}, {atom, abc}]},
     [{'X', {cons, [{integer, 7}, {integer, 8}, {integer, 9}, {atom, abc}]}}]}, 
    eval:eval("X = [7, 8, 9, abc].", [])),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}]}, 
    eval:eval("[H | T] = [a, b, c].", [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}])),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}]}, 
    eval:eval("[H | T] = [a, b, c].", [{'H', {atom, a}}])),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}]}, 
    eval:eval("[H | T] = [a, b, c].", [{'T', {cons, [{atom, b}, {atom, c}]}}])),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}]}, 
    eval:eval("[H | T] = [a, b, c].", [])),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'H', {atom, a}}]}, 
    eval:eval("[H | [b, c]] = [a, b, c].", [])),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'T', {cons, [{atom, b}, {atom, c}]}}]}, 
    eval:eval("[a | T] = [a, b, c].", [])),
  ?assertEqual({ok, {nil, []}, []}, eval:eval("[] = [].", [])),
  ?assertEqual({ok, {cons, [{atom, j}]}, [{'J', {atom, j}}]}, eval:eval("[J] = [j].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, [{'X', {integer, 1}}]}, 
    eval:eval("[X | _] = [1, 2].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, [{'Y', {cons, [{integer, 2}]}}]}, 
    eval:eval("[_ | Y] = [1, 2].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, [{'X', {integer, 1}}]}, 
    eval:eval("[X | _] = [1, 2].", [{'X', {integer, 1}}])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, [{'Y', {cons, [{integer, 2}]}}]}, 
    eval:eval("[_ | Y] = [1, 2].", [{'Y', {cons, [{integer, 2}]}}])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}]},
    [{'H', {integer, 1}}, {'T', {cons, [{integer, 2}, {integer, 3}]}}, {'X', {cons, [{integer, 1}, {integer, 2}, {integer, 3}]}}]},
    eval:eval("X = [1, 2, 3], [H | T] = X.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}]},
    [{'H', {integer, 1}}, {'T', {integer, 2}}, {'X', {tuple, [{integer, 1}, {integer, 2}]}}]},
    eval:eval("X = {1, 2}, {H, T} = X.", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    [{'A', {integer, 1}}, {'B', {cons, [{integer, 2}, {integer, 3}]}}, 
      {'X', {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}}]},
    eval:eval("X = [1, [2, 3]], [A, B] = X.", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    [{'A', {integer, 1}}, {'X', {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}}]},
    eval:eval("X = [1, [2, 3]], [A, [2, 3]] = X.", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    [{'B', {cons, [{integer, 2}, {integer, 3}]}}, 
      {'X', {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}}]},
    eval:eval("X = [1, [2, 3]], [1, B] = X.", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    [{'A', {integer, 1}}, {'B', {cons, [{integer, 2}, {integer, 3}]}}, 
      {'X', {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}},
      {'Y', {integer, 2}}]},
    eval:eval("Y = 2, X = [1, [Y, 3]], [A, B] = X.", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    [{'A', {integer, 1}}, {'B', {cons, [{integer, 2}, {integer, 3}]}}, 
      {'X', {cons, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}},
      {'Y', {integer, 2}}]},
    eval:eval("Y = 2, X = [1, [Y, 3]], [A, B] = X.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}]}, 
    [{'A', {integer, 1}}, {'B', {integer, 2}}, {'X', {tuple, [{integer, 1}, {integer, 2}]}}]},
    eval:eval("X = {1, 2}, {A, B} = X.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}]}, 
    [{'B', {integer, 2}}, {'X', {tuple, [{integer, 1}, {integer, 2}]}}]},
    eval:eval("X = {1, 2}, {1, B} = X.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}]}, 
    [{'A', {integer, 1}}, {'X', {tuple, [{integer, 1}, {integer, 2}]}}]},
    eval:eval("X = {1, 2}, {A, 2} = X.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}]}, 
    [{'A', {integer, 1}}, {'B', {integer, 2}}, 
      {'X', {tuple, [{integer, 1}, {integer, 2}]}}, {'Y', {integer, 2}}]},
    eval:eval("Y = 2, X = {1, Y}, {A, B} = X.", [])),
  ?assertEqual({ok, {tuple, [{cons, [{integer, 1}]}, {cons, [{integer, 2}]}]}, 
    [{'A', {cons, [{integer, 1}]}}, {'B', {cons, [{integer, 2}]}}, 
     {'X', {tuple, [{cons, [{integer, 1}]}, {cons, [{integer, 2}]}]}}]},
    eval:eval("X = {[1], [2]}, {A, B} = X.", [])),
  ?assertEqual({ok, {cons, [{tuple, [{integer, 1}]}, {tuple, [{integer, 2}]}]}, 
    [{'A', {tuple, [{integer, 1}]}}, {'B', {tuple, [{integer, 2}]}}, 
     {'X', {cons, [{tuple, [{integer, 1}]}, {tuple, [{integer, 2}]}]}}]},
    eval:eval("X = [{1}, {2}], [A, B] = X.", [])),

  % tuple matching
  ?assertEqual({ok, {tuple, [{integer, 1}, {atom, abc}, {integer, 3}]}, []},
    eval:eval("{1, abc, 3} = {1, abc, 3}.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {atom, abc}, 
    {tuple, [{integer, 7}, {cons, [{integer, 8}, {integer, 9}]}]}]}, []},
    eval:eval("{1, abc, {7, [8, 9]}} = {1, abc, {7, [8, 9]}}.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}, {integer, 3}]}, [{'A', {integer, 2}}]},
    eval:eval("{1, A, 3} = {1, 2, 3}.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {cons, [{integer, 2}]}, {tuple, [{integer, 3}]}]},
    [{'A', {integer, 1}}, {'B', {cons, [{integer, 2}]}}, {'C', {tuple, [{integer, 3}]}}]},
    eval:eval("{A, B, C} = {1, [2], {3}}.", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {atom, abc}, 
    {tuple, [{integer, 7}, {cons, [{integer, 8}, {integer, 9}]}]}]},
    [{'A', {integer, 7}}, {'B', {integer, 8}}]},
    eval:eval("{1, abc, {A, [B, 9]}} = {1, abc, {7, [8, 9]}}.", [])),
  
  % more lists
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, []}, eval:eval("[1, 2] = [1, 2].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}]},
     eval:eval("[A, B] = [1, 2].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}]}, [{'A', {integer, 3}}]},
    eval:eval("[1, 2, A] = [1, 2, 3].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {cons, [{integer, 2}, {cons, [{integer, 3}, 
    {cons, [{integer, 4}]}]}]}]}, [{'A', {integer, 4}}]},
    eval:eval("[1, [2, [3, [A]]]] = [1, [2, [3, [4]]]].", [])),
  ?assertEqual({ok, {cons, [{integer, 4}, {integer, 5}, {integer, 6}]}, []},
    eval:eval("[_, _, 6] = [4, 5, 6].", [])),

  % tuple/list combined
  ?assertEqual({ok, {tuple, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    [{'A', {integer, 1}}, {'B', {integer, 2}}, {'C', {cons, [{integer, 3}]}}]},
    eval:eval("{A, [B | C]} = {1, [2, 3]}.", [{'B', {integer, 2}}])),
  ?assertEqual({ok, {cons, [{tuple, [{integer, 1}, {integer, 2}]}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}]}, 
    eval:eval("[{A, B}] = [{1, 2}].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}]}, 
    eval:eval("[A | [B]] = [1, 2].", [])),
  ?assertEqual({ok, {cons, [{cons, [{integer, 1}, {integer, 2}]}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}]}, 
    eval:eval("[[A, B]] = [[1, 2]].", [])),
  ?assertEqual({ok, {cons, [{tuple, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    {cons, [{integer, 4}, {integer, 5}]}, {tuple, [{integer, 6}, {tuple, [{integer, 7}]}, {integer, 8}]}, 
    {integer, 9}, {integer, 10}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}, {'C', {integer, 3}}, 
      {'D', {integer, 4}}, {'E', {integer, 5}}, {'F', {integer, 7}}]},
    eval:eval("[{A, [B, C]}, [D | [E]], {_, {F}, _}, 9, 10] 
      = [{1, [2, 3]}, [4, 5], {6, {7}, 8}, 9, 10].", [{'B', {integer, 2}}])).
  
% Tests for evaluating function calls/guards
test_world() ->
  % world_init
  ?assertEqual({ok, {atom, true}, [{'X', {integer, 3}}]}, eval:eval("is_integer(X).", [{'X', {integer, 3}}])),
  ?assertEqual({ok, {atom, true}, [{'X', {integer, 5}}]}, 
    eval:eval("is_integer(X).", [{'X', {integer, 5}}], world:world_init())),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("is_integer(abc).", [], world:world_init())),
  ?assertEqual({ok, {atom, head}, []}, eval:eval("hd([head, tail]).", [], world:world_init())),
  ?assertEqual({ok, {cons, [{atom, tail}]}, []}, eval:eval("tl([head, tail]).", [], world:world_init())),

  % simple functions
  SimpleModule_temp1 = world:module_add_function_string(#{}, greater, 2, "greater(X, Y) -> X > Y."),
  SimpleModule_temp2 = world:module_add_function_string(SimpleModule_temp1, sum, 2, "sum(X, Y) -> X + Y."),
  SimpleModule_temp3 = world:module_add_function_string(SimpleModule_temp2, sum, 3, "sum(X, Y, Z) -> X + Y + Z."),
  SimpleModule = world:module_add_function_string(SimpleModule_temp3, concat, 2, "concat(X, Y) -> X ++ Y."),
  SimpleWorld = world:world_add_module(world:world_init(), simple_module, SimpleModule),

  ?assertEqual({ok, {atom, true}, []}, eval:eval("simple_module:greater(10, 5).", [], SimpleWorld)),
  ?assertEqual({ok, {integer, 9}, []}, eval:eval("simple_module:sum(5, 4).", [], SimpleWorld)),
  ?assertEqual({ok, {integer, 15}, []}, eval:eval("simple_module:sum(5, 4, 6).", [], SimpleWorld)),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}]}, []},
     eval:eval("simple_module:concat([1, 2], [3, 4]).", [], SimpleWorld)),
  ?assertEqual({ok, {integer, 10}, [{'X', {integer, 3}}, {'Y', {integer, 7}}]}, 
    eval:eval("simple_module:sum(X, Y).", [{'X', {integer, 3}}, {'Y', {integer, 7}}], SimpleWorld)),

  % functions with lists
  ListModule = world:module_add_function_string(#{}, concat, 2, "concat(X, Y) -> X ++ Y."),
  ListWorld = world:world_add_module(SimpleWorld, list_module, ListModule),

  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, []}, eval:eval("list_module:concat([a, b], [c]).", [], ListWorld)),
  
  % functions with guards
  GuardModule = world:module_add_function_string(#{}, zero , 1,
    "zero(X) when X < 0 -> lesser;
     zero(X) when X == 0 -> zero;
     zero(X) when X > 0 -> greater."),
  GuardWorld = world:world_add_module(ListWorld, guard_module, GuardModule),

  ?assertEqual({ok, {atom, lesser}, []}, eval:eval("guard_module:zero(-5).", [], GuardWorld)),
  ?assertEqual({ok, {atom, zero}, []}, eval:eval("guard_module:zero(0).", [], GuardWorld)),
  ?assertEqual({ok, {atom, greater}, []}, eval:eval("guard_module:zero(6).", [], GuardWorld)),

  % recursive functions
  RecursiveModule = world:module_add_function_string(#{}, guarded_fac, 1,
    "guarded_fac(N) when N == 0 -> 1;\nguarded_fac(N) when is_integer(N), 0 < N -> N * guarded_fac(N-1).\n"),
  RecursiveWorld = world:world_add_module(GuardWorld, recursive_module, RecursiveModule),
  ?assertEqual({ok, {integer, 1}, []}, eval:eval("recursive_module:guarded_fac(0).", [], RecursiveWorld)),
  ?assertEqual({ok, {integer, 6}, []}, eval:eval("recursive_module:guarded_fac(3).", [], RecursiveWorld)),
  ?assertEqual({ok, {integer, 5040}, []}, eval:eval("recursive_module:guarded_fac(7).", [], RecursiveWorld)),
  ?assertEqual({error, function_clause}, 
    eval:eval("recursive_module:guarded_fac(-2).", [], RecursiveWorld)),

  % purging a module
  PurgedWorld = world:world_purge_module(RecursiveWorld, recursive_module),
  
  % Factorial at Last
  FactorialModule = world:module_add_function_string(RecursiveModule, fac, 1,
    "fac(0) -> 1;\n fac(N) when is_integer(N), 0 < N -> N * fac(N-1).\n"),
  FactorialWorld = world:world_add_module(PurgedWorld, factorial_module, FactorialModule),

  ?assertEqual({ok, {integer, 1}, []}, eval:eval("factorial_module:fac(0).", [], FactorialWorld)),
  ?assertEqual({ok, {integer, 6}, []}, eval:eval("factorial_module:fac(3).", [], FactorialWorld)),
  ?assertEqual({ok, {integer, 5040}, []}, eval:eval("factorial_module:fac(7).", [], FactorialWorld)),
  ?assertEqual({error, function_clause}, 
    eval:eval("factorial_module:fac(-2).", [], FactorialWorld)),
  
  % more tests on functions
  Test_Module_1 = world:module_add_function_string(#{}, unwrap, 1, "unwrap({A}) -> A."),
  Test_Module_2 = world:module_add_function_string(Test_Module_1, unwrap_and_add, 2, "unwrap_and_add({A}, {B}) -> A + B."),
  Test_Module_3 = world:module_add_function_string(Test_Module_2, recurse, 1, 
    "recurse(List) ->
      if 
        List /= [] -> 
          Head = hd(List),
          Tail = tl(List),
          unwrap(Head) + recurse(Tail);
        true ->
          0
      end."),
  Test_World = world:world_add_module(world:world_init(), test_module, Test_Module_3),

  ?assertEqual({ok, {integer, 1}, []}, eval:eval("test_module:unwrap({1}).", [], Test_World)),
  ?assertEqual({ok, {integer, 5}, []}, eval:eval("test_module:unwrap({5}).", [], Test_World)),
  ?assertEqual({ok, {integer, 12}, []}, eval:eval("test_module:unwrap_and_add({5}, {7}).", [], Test_World)),
  ?assertEqual({ok, {integer, 0}, []}, eval:eval("test_module:recurse([]).", [], Test_World)),
  ?assertEqual({ok, {integer, 11}, []}, eval:eval("test_module:recurse([{5}, {6}]).", [], Test_World)),
  ?assertEqual({ok, {integer, 19}, []}, eval:eval("test_module:recurse([{5}, {6}, {8}]).", [], Test_World)).

% test the scope of bindings
test_bindings() ->
  % basic binding usage/creation
  ?assertEqual({ok, {integer, 3}, [{'X', {integer, 3}}]}, eval:eval("X.", [{'X', {integer, 3}}])),
  ?assertEqual({ok, {integer, 3}, [{'X', {integer, 3}}]}, eval:eval("X = 3.", [{'X', {integer, 3}}])),
  ?assertEqual({error, {badmatch, {integer, 2}}}, eval:eval("X = 2.", [{'X', {integer, 3}}])),
  ?assertEqual({ok, {integer, 3}, [{'X', {integer, 3}}, {'Y', {integer, 3}}]}, 
    eval:eval("X = Y.", [{'X', {integer, 3}}, {'Y', {integer, 3}}])),
  ?assertEqual({ok, {atom, true}, [{'X', {integer, 8}}]}, eval:eval("X = 8, 4 + 5, true.", [])),

  % functions that use/create bindings
  Module_temp = world:module_add_function_string(#{}, greater, 2, "greater(X, Y) -> X > Y."),
  Module = world:module_add_function_string(Module_temp, tautology, 2, 
    "tautology(X, Y) when is_integer(X), is_integer(Y) -> 
      A = X,
      B = Y,
      X + Y;
    tautology([Hdx | Tlx], [Hdy | Tly]) ->
      X = [Hdx | Tlx],
      Y = [Hdy | Tly],
      X ++ Y;
    tautology(_, _) ->
      empty."
  ),
  World = world:world_add_module(world:world_init(), module, Module),

  ?assertEqual({ok, {atom, true}, []}, eval:eval("module:greater(10, 5).", [], World)),
  ?assertEqual({ok, {atom, true}, [{'A', {integer, 8}}]}, eval:eval("module:greater(A, 7).", [{'A', {integer, 8}}], World)),
  ?assertEqual({ok, {atom, false}, [{'X', {integer, 1}}, {'Y', {integer, 2}}]}, 
    eval:eval("module:greater(X, Y).", [{'X', {integer, 1}}, {'Y', {integer, 2}}], World)),

  ?assertEqual({ok, {integer, 4}, []}, eval:eval("module:tautology(2, 2).", [], World)),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}]}, []}, 
    eval:eval("module:tautology([1, 2], [3, 4]).", [], World)),
  ?assertEqual({ok, {integer, 4}, [{'X', {integer, 2}}, {'Y', {integer, 2}}]}, 
    eval:eval("module:tautology(X, Y).", [{'X', {integer, 2}}, {'Y', {integer, 2}}], World)),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}]},
    [{'X', {cons, [{integer, 1}, {integer, 2}]}}, {'Y', {cons, [{integer, 3}, {integer, 4}]}}]}, 
   eval:eval("module:tautology(X, Y).", 
    [{'X', {cons, [{integer, 1}, {integer, 2}]}}, {'Y', {cons, [{integer, 3}, {integer, 4}]}}], World)),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}]},
    [{'Hdx', {integer, 1}}, {'Hdy', {integer, 3}}, {'Tlx', {cons, [{integer, 2}]}}, {'Tly', {cons, [{integer, 4}]}}]}, 
   eval:eval("module:tautology([Hdx | Tlx], [Hdy | Tly]).", 
    [{'Hdx', {integer, 1}}, {'Hdy', {integer, 3}}, {'Tlx', {cons, [{integer, 2}]}}, {'Tly', {cons, [{integer, 4}]}}], World)).

% General Tests for the evalution of basic erlang statements/operations 
test_general() ->

  % arithmetic operations
  ?assertEqual({ok, {integer, 29}, []}, eval:eval("29.", [])),
  ?assertEqual({ok, {integer, 7}, []},  eval:eval("4 + 3.", [])),
  ?assertEqual({ok, {integer, -29}, []}, eval:eval("-29.", [])),
  ?assertEqual({ok, {integer, 7}, []},  eval:eval("9 - 2.", [])),
  ?assertEqual({ok, {integer, 10}, []}, eval:eval("19 - 25 + 4 - 5 + 17.", [])),
  ?assertEqual({ok, {integer, 24}, []}, eval:eval("8 * 3.", [])),
  ?assertEqual({ok, {integer, 10}, []}, eval:eval("20 div 2.", [])),
  ?assertEqual({ok, {integer, 92}, []}, eval:eval("8 * (3 + 9) - (9 div 3 + 1).", [])),
  ?assertEqual({ok, {integer, 6}, [{'X', {integer, 6}}]}, eval:eval("X.", [{'X', {integer, 6}}])),
  ?assertEqual({ok, {integer, 41}, [{'X', {integer, 6}}, {'Y', {integer, 5}}, {'Z', {integer, 13}}]}, 
    eval:eval("X + Y * (Z - X).", [{'X', {integer, 6}}, {'Y', {integer, 5}}, {'Z', {integer, 13}}])),
  ?assertEqual({ok, {integer, 3}, []}, eval:eval("1 + 2, 3.", [])),
  ?assertEqual({ok, {atom, false}, []}, eval:eval("5 > 6.", [])),

  % simple macthes
  ?assertEqual({ok, {integer, 1}, [{'X', {integer, 1}}]}, eval:eval("X = 1.", [])),
  ?assertEqual({ok, {integer, 2}, [{'X', {integer, 2}}]}, eval:eval("X = 2.", [{'X', {integer, 2}}])),
  ?assertEqual({ok, {integer, 2}, []}, eval:eval("2 = 2.", [])),
  ?assertEqual({ok, {integer, 5}, [{'X', {integer, 5}}]}, eval:eval("X = 2 + 3.", [])),
  ?assertEqual({ok, {integer, 5}, [{'X', {integer, 2}}, {'Y', {integer, 3}}]}, 
    eval:eval("X = 2, Y = 3, X + Y.", [{'X', {integer, 2}}])),
  ?assertEqual({ok, {integer, 1}, [{'X', {integer, 1}}, {'Y', {integer, 1}}]}, eval:eval("X = Y = 1.", [])),
  ?assertEqual({ok, {integer, 4}, [{'X', {integer, 2}}]}, eval:eval("(X = 2) + 2.", [])),

  % lists, tuples
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}]}, []}, eval:eval("[1, 2, 3, 4].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}, {integer, 5}]}, [{'X', {integer, 5}}]}, 
    eval:eval("[1, 2, 3, 4, X].", [{'X', {integer, 5}}])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}, {integer, 4}]}, []}, eval:eval("[1, 2] ++ [3, 4].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}]}, []}, eval:eval("[1 | [2, 3]].", [])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}, {atom, abc}, {integer, 4}]}, [{'X', {integer, 4}}]}, eval:eval("{1, 2, abc, X}.", [{'X', {integer, 4}}])),
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}, {integer, 3}]}, [{'X', {tuple, [{integer, 1}, {integer, 2}, {integer, 3}]}}]},
     eval:eval("X = {1, 2, 3}.", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}]}, []}, eval:eval("[1 | [2]].", [])),
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}]}, []}, eval:eval("[1 | [2, 3]].", [])),

  % atoms and logic operations
  ?assertEqual({ok, {atom, here_is_an_atom}, []}, eval:eval("here_is_an_atom.", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("atom1 == atom1.", [])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("(true and false) or true.", [])),
  ?assertEqual({ok, {atom, true}, [{'Bool1', {atom, true}},{'Bool2', {atom, true}}, {'X', {integer, 1}}, {'Y', {integer, 2}}]},
    eval:eval("Bool1 = X == 1, Bool2 = Y == 2, Bool1 and Bool2.", [{'X', {integer, 1}}, {'Y', {integer, 2}}])),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("atom > 2.", [])),

  % strings
  ?assertEqual({ok, {string, "here is a string"}, []}, eval:eval("\"here is a string\".", [])),
  ?assertEqual({ok, {string, "concat strings"}, []}, eval:eval("\"concat \" ++ \"strings\".", [])),
  
  % if
  ?assertEqual({ok, {atom, true}, []}, eval:eval("if true -> true end.", [])),
  ?assertEqual({ok, {integer, 35}, [{'X', {integer, 3}}]}, 
    eval:eval("if X == 1 -> 4; X == 3, X > 2 -> 35; true -> 2 end.", [{'X', {integer, 3}}])),
  ?assertEqual({ok, {atom, ab}, [{'X', {atom, a}}, {'Y', {atom, b}}]}, 
    eval:eval("if X == a, Y == b -> ab; Y == b -> b; true -> abc end.", [{'X', {atom, a}}, {'Y', {atom, b}}])),
  ?assertEqual({ok, {atom, abc}, [{'X', {atom, a}}, {'Y', {atom, c}}]}, 
    eval:eval("if X == a, Y == b -> ab; Y == b -> b; true -> abc end.", [{'X', {atom, a}}, {'Y', {atom, c}}])),
  ?assertEqual({ok, {atom, b}, [{'X', {atom, c}}, {'Y', {atom, b}}]}, 
    eval:eval("if X == a, Y == b -> ab; Y == b -> b; true -> abc end.", [{'X', {atom, c}}, {'Y', {atom, b}}])),
  
  % case of
  ?assertEqual({ok, {atom, true}, []}, eval:eval("case true of true -> true; false -> false end.", [])),
  ?assertEqual({ok, {atom, atom}, [{'X', {atom, abc}}, {'Y', {integer, 4}}]}, eval:eval(
    "case X of 
      abc -> atom; 
      Y when is_integer(Y) -> integer;
      X -> self end.", [{'X', {atom, abc}}, {'Y', {integer, 4}}])),
  ?assertEqual({ok, {atom, integer}, [{'X', {integer, 2}}, {'Y', {integer, 2}}]}, eval:eval(
    "case X of 
      abc -> atom; 
      Y when is_integer(Y) -> integer;
      X -> self end.", [{'X', {integer, 2}}, {'Y', {integer, 2}}])),
  ?assertEqual({ok, {atom, self}, [{'X', {string, "a"}}, {'Y', {string, "a"}}]}, eval:eval(
    "case X of 
      abc -> atom; 
      Y when is_integer(Y) -> integer;
      X -> self end.", [{'X', {string, "a"}}, {'Y', {string, "a"}}])),

  % try catch (incomplete)
  ?assertEqual({ok, {atom, true}, [{'X', {integer, 1}}]}, 
    eval:eval("try X =:= X div 1 catch error:E -> false end.", [{'X', {integer, 1}}])),
  ?assertEqual({ok, {atom, false}, [{'X', {float, 2.0}}]}, 
    eval:eval("try X =:= X div 1 catch error:E -> false end.", [{'X', {float, 2.0}}])),
  ?assertEqual({ok, {atom, false}, [{'X', {string, "abc"}}]}, 
    eval:eval("try X =:= X div 1 catch error:E -> false end.", [{'X', {string, "abc"}}])).