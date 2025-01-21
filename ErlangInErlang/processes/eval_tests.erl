-module(eval_tests).
-export([test_all/0]).
-include_lib("eunit/include/eunit.hrl").

% Run all tests
test_all() ->
  simple_tests1(),
  simple_tests2().

simple_tests1() ->
  % integers and arithmetic
  ?assertEqual({ok, {integer, -14}, []}, eval:eval("-14.")),
  ?assertEqual({ok, {integer, 14}, []}, eval:eval("1 * 2 + 6 * 2.")),
  ?assertEqual({ok, {atom, true}, []}, eval:eval("14 == 1 + 13.")),
  % mutiple expressions
  ?assertEqual({ok, {integer, 4}, []}, eval:eval("1, 2, 3, 4.")),
  ?assertEqual({ok, {integer, 4}, []}, eval:eval("1, 1 + 1, 3, 2 * 2.")),
  % variables
  ?assertEqual({ok, {atom, false}, [{'X', {atom, true}}]},
    eval:eval("X and true, false, X == notX.", [{'X', {atom, true}}])),
  ?assertEqual({ok, {integer, 41}, [{'X', {integer, 6}}, {'Y', {integer, 5}}, {'Z', {integer, 13}}]}, 
    eval:eval("X + Y * (Z - X).", [{'X', {integer, 6}}, {'Y', {integer, 5}}, {'Z', {integer, 13}}])),
  % lists
  ?assertEqual({ok, {cons, [{integer, 1}, {integer, 2}, {integer, 3}]}, [{'X', {integer, 2}}]},
    eval:eval("[1, X, 1 + 2].", [{'X', {integer, 2}}])),
  % tuples
  ?assertEqual({ok, {tuple, [{integer, 1}, {integer, 2}, {integer, 3}]}, [{'X', {integer, 2}}]},
    eval:eval("{1, X, 1 + 2}.", [{'X', {integer, 2}}])),
  % funs
  ?assertMatch({ok, {'fun', Name}, [{Name, {{clauses, [{clause,1,[],[],[{integer,1,1}]}]}, []}}]},
    eval:eval("fun() -> 1 end.", [])),
  % simple match
  ?assertEqual({ok, {integer, 5}, [{'X', {integer, 5}}]}, eval:eval("X = 5.")),
  % match lists
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, 
    [{'H', {atom, a}}, {'T', {cons, [{atom, b}, {atom, c}]}}]}, 
    eval:eval("[H | T] = [a, b, c].")),
  ?assertEqual({ok, {cons, [{atom, a}, {atom, b}, {atom, c}]}, 
    [{'A', {atom, a}}, {'B', {atom, b}}, {'C', {atom, c}}]}, 
    eval:eval("[A, B, C] = [a, b, c].")),
  % match tuples
  ?assertEqual({ok, {tuple, [{atom, a}, {atom, b}, {atom, c}]}, 
    [{'A', {atom, a}}, {'B', {atom, b}}, {'C', {atom, c}}]}, 
    eval:eval("{A, B, C} = {a, b, c}.")),
  ?assertMatch({error, {badmatch, _}}, 
    eval:eval("{A, B, C} = {a, b, c, d}.")),
  % match tuples and lists combined
  ?assertEqual({ok, {cons, [{tuple, [{integer, 1}, {cons, [{integer, 2}, {integer, 3}]}]}, 
    {cons, [{integer, 4}, {integer, 5}]}, {tuple, [{integer, 6}, {tuple, [{integer, 7}]}, {integer, 8}]}, 
    {integer, 9}, {integer, 10}]}, [{'A', {integer, 1}}, {'B', {integer, 2}}, {'C', {integer, 3}}, 
      {'D', {integer, 4}}, {'E', {integer, 5}}, {'F', {integer, 7}}]},
    eval:eval("[{A, [B, C]}, [D | [E]], {_, {F}, _}, 9, 10] 
      = [{1, [2, 3]}, [4, 5], {6, {7}, 8}, 9, 10].", [{'B', {integer, 2}}])).

simple_tests2() ->
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
      Y when true -> integer;
      X -> self end.", [{'X', {integer, 2}}, {'Y', {integer, 2}}])),
  ?assertEqual({ok, {atom, self}, [{'X', {string, "a"}}, {'Y', {string, "a"}}]}, eval:eval(
    "case X of 
      abc -> atom; 
      Y when false -> integer;
      X -> self end.", [{'X', {string, "a"}}, {'Y', {string, "a"}}])).