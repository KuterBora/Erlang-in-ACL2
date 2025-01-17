-module(eval_tests).
-export([test_general/0, test_messages/0, test_all/0]).
-include_lib("eunit/include/eunit.hrl").

% Run all tests
test_all() ->
  test_general(),
  test_messages(),
  test_receive().

test_messages() ->
  % send message
  ?assertEqual({ok, {atom, message}, [{'Pid', {pid, sample_pid}}], {[{{pid, sample_pid}, {atom, message}}], []}}, 
    eval:eval("Pid ! message.", [{'Pid', {pid, sample_pid}}])),
  % send message inside operation
  ?assertEqual({ok, {atom, true}, [{'Pid', {pid, sample_pid}}], {[{{pid, sample_pid}, {atom, message}}], []}}, 
    eval:eval("(Pid ! message) == message.", [{'Pid', {pid, sample_pid}}])),
  % send message in list
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}]}, 
    [{'Pid', {pid, sample_pid}}], {[{{pid, sample_pid}, {integer, 3}}], []}}, 
    eval:eval("[1, 2, Pid ! 3].", [{'Pid', {pid, sample_pid}}])),
  % send message in tuple
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}, {integer, 3}]}, 
    [{'Pid', {pid, sample_pid}}], {[{{pid, sample_pid}, {integer, 2}}], []}}, 
    eval:eval("{1, Pid ! 2, 3}.", [{'Pid', {pid, sample_pid}}])),
  % send message in fun
  ?assertMatch({ok, {atom, message}, [{'Pid', {pid, sample_pid}}, _], {[{{pid, sample_pid}, {atom, message}}], []}}, 
    eval:eval("(fun() -> Pid ! message end)().", [{'Pid', {pid, sample_pid}}])),
  % send message in function
  Module = world:module_add_function_string(#{}, message_fac, 2,
    "message_fac(0, Pid) -> Pid ! 1;\n message_fac(N, Pid) when is_integer(N), 0 < N -> Pid ! (N * message_fac(N-1, Pid)).\n"),
  World = world:world_add_module(world:world_init(), module, Module),

  ?assertMatch({ok, {integer, 1}, [_], {[{{pid, sample_pid}, {integer, 1}}], []}}, 
    eval:eval("module:message_fac(0, Pid).", [{'Pid', {pid, sample_pid}}], World)),
  ?assertMatch({ok, {integer, 6}, [_], 
    {[{{pid, sample_pid}, {integer, 1}},
      {{pid, sample_pid}, {integer, 1}},
      {{pid, sample_pid}, {integer, 2}},
      {{pid, sample_pid}, {integer, 6}}
      ], []}}, 
    eval:eval("module:message_fac(3, Pid).", [{'Pid', {pid, sample_pid}}], World)),
  % send message and fail, no send
  ?assertEqual({error, badarith, {[], []}}, 
    eval:eval("[1, 2 / 0, Pid ! 3].", [{'Pid', {pid, sample_pid}}])),
  ?assertEqual({error, badarith, _}, % TODO, should there be a message? 
    eval:eval("[1, Pid ! 2, 3 / 0].", [{'Pid', {pid, sample_pid}}])).
  % send message and fail, still send

  % send message in function argument


test_receive() ->
  % receive
  ?assertMatch({yield, _, _, [], _},
    eval:eval("receive X -> X end.", [])),
  ?assertMatch({yield, _, _, [{'X', {integer, 1}}], _},
    eval:eval("X = 1, receive X -> X end.", [])),
  % receive inside operation
  ?assertMatch({yield, _, [{op, 1, '+', {integer, 1, 1}, {var, 1, '#receive'}}], [], _},
    eval:eval("1 + receive X -> X end.", [])),
  ?assertMatch({yield, _, [{op, 1, '+', {integer, 1, 1}, {var, 1, '#receive'}}], [_], _},
    eval:eval("(X ! 1) + receive X -> X end.", [{'X', {'pid', sample_pid}}])),
  % receive in list
  ?assertMatch({yield, _, [{cons, 1, {var, 1, '#receive'}, 
    {cons, 1, {integer, 1, 2}, {cons, 1, {integer, 1, 3}, {nil, 1}}}}], [], _},
    eval:eval("[receive X -> 1 end, 2, 3].", [])),
  ?assertMatch({yield, _, [{cons, 1, {integer, 1, 1}, 
    {cons, 1, {var, 1, '#receive'}, {cons, 1, {integer, 1, 3}, {nil, 1}}}}], [], _},
    eval:eval("[1 + 0, receive X -> 1 end, 3].", [])),
  % receive in tuple
  ?assertMatch({yield, _, [{tuple, 1, [{var, 1, '#receive'}, {integer, 1, 2}, {integer, 1, 3}]}], [], _},
    eval:eval("{receive X -> 1 end, 2, 3}.", [])),
  ?assertMatch({yield, _, [{tuple, 1, [{integer, 1, 1}, {var, 1, '#receive'}, {op, _, _, _, _}]}], [], _},
    eval:eval("{1 * 1, receive X -> 1 end, 2 + 1}.", [])).
  % receive in fun
  % receive in function
  % receive in function depth 2


test_general() ->
  % basic arithmetic operations
  ?assertEqual({ok, {integer, 41}, [{'X', {integer, 6}}, {'Y', {integer, 5}}, {'Z', {integer, 13}}], procs:empty_box()}, 
    eval:eval("X + Y * (Z - X).", [{'X', {integer, 6}}, {'Y', {integer, 5}}, {'Z', {integer, 13}}])),
  % lists
  ?assertEqual({ok, {integer, 3}, [], procs:empty_box()}, eval:eval("length([1, 2, 3]).", [])),
  % case expressions
  ?assertEqual({ok, {atom, integer}, [{'X', {integer, 2}}, {'Y', {integer, 2}}], procs:empty_box()},
    eval:eval(
    "case X of 
      abc -> atom; 
      Y when is_integer(Y) -> integer;
      X -> self end.", [{'X', {integer, 2}}, {'Y', {integer, 2}}])),
  % % fun expressions
  ?assertMatch({ok, {integer, 3}, [{'X', {'fun', Name}},
    {Name, {{clauses,[{clause,1,[{integer,1,1}],[],[{integer,1,1}]},
    {clause,1,[{integer,1,2}],[],[{integer,1,2}]},
    {clause,1,[{var,1,'_'}],[],[{integer,1,3}]}]}, [], _}}], {[], []}},
    eval:eval("X = fun(1) -> 1; (2) -> 2; (_) -> 3 end, X(3).", [])),  
  ?assertMatch({ok, {integer, 1}, [{'X', {cons, [{'fun', Name}]}}, {'Y', {'fun', Name}}, 
    {Name, {_, [], _}}], {[], []}},
    eval:eval("X = [fun() -> 1 end], [Y] = X, Y().", [])),
  ?assertMatch({ok, {integer, 3}, [{'X', {'fun', Name}}, {'Y', {integer, 1}}, {Name, _}], {[], []}},
    eval:eval("Y = 1, X = fun(X) -> X + Y end, X(2).", [])),
  ?assertMatch({ok, {integer, 15}, [{'Y', {'fun', _}}, {'Z', {'fun', _}},
    {{_, 0}, _}, {{_, 0}, _}], {[], []}},
    eval:eval(
      "Z = fun() -> Y = 3, Y * 5 end, 
       Y = fun() -> Z end,
       (Y())().", [])),
  FunModule_temp1 = world:module_add_function_string(#{}, square, 1,
    "square(X) -> Y = fun(X) -> X * X end, Y(X)."),
  FunModule_temp2 = world:module_add_function_string(FunModule_temp1, adder, 1, "adder(X) -> fun(Y) -> X + Y end."),
  FunModule = world:module_add_function_string(FunModule_temp2, apply, 2, "apply(X, Y) -> X(Y)."),
  FunWorld = world:world_add_module(world:world_init(), fun_module, FunModule),
  ?assertMatch({ok, {integer, 100}, [], {[], []}}, 
    eval:eval("fun_module:square(10).", [], FunWorld)),
  ?assertMatch({ok, {integer, 5}, [{'X', _}, {_,  _}], {[], []}}, 
    eval:eval("X = fun_module:adder(3), X(2).", [], FunWorld)),
  ?assertMatch({ok, {integer, 5}, [{'X', _}, {_,  _}], {[], []}}, 
    eval:eval("X = fun_module:adder(3), fun_module:apply(X, 2).", [], FunWorld)),
  ?assertMatch({ok, {integer, 3}, [_], {[], []}}, 
    eval:eval("fun_module:apply(fun(X) -> X + 1 end, 2).", [], FunWorld)),
  ?assertMatch({ok, {integer, 5}, [{'X', _}, {_, _}], {[], []}}, 
    eval:eval("X = fun_module:adder(3), fun_module:apply(X, 2).", [], FunWorld)),
  % % matches
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}], {[], []}}, 
    eval:eval("[H | T] = [a, b, c].", [])),
  ?assertEqual({ok, {cons, [{tuple, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    {cons, [{integer, 4}, {integer, 5}]}, {tuple, [{integer, 6}, {tuple, [{integer, 7}]}, {integer, 8}]}, 
    {integer, 9}, {integer, 10}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}, {'C', {integer, 3}}, 
      {'D', {integer, 4}}, {'E', {integer, 5}}, {'F', {integer, 7}}], {[], []}},
    eval:eval("[{A, [B, C]}, [D | [E]], {_, {F}, _}, 9, 10] 
      = [{1, [2, 3]}, [4, 5], {6, {7}, 8}, 9, 10].", [{'B', {integer, 2}}])),
  % factorial
  FactorialModule = world:module_add_function_string(#{}, fac, 1,
    "fac(0) -> 1;\n fac(N) when is_integer(N), 0 < N -> N * fac(N-1).\n"),
  FactorialWorld = world:world_add_module(world:world_init(), factorial_module, FactorialModule),

  ?assertEqual({ok, {integer, 1}, [], procs:empty_box()}, eval:eval("factorial_module:fac(0).", [], FactorialWorld)),
  ?assertEqual({ok, {integer, 6}, [], procs:empty_box()}, eval:eval("factorial_module:fac(3).", [], FactorialWorld)),
  ?assertEqual({ok, {integer, 5040}, [], procs:empty_box()}, eval:eval("factorial_module:fac(7).", [], FactorialWorld)),
  ?assertEqual({error, function_clause, procs:empty_box()}, 
    eval:eval("factorial_module:fac(-2).", [], FactorialWorld)).
