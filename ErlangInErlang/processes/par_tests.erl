-module(par_tests).
-export([test_all/0]).
-include_lib("eunit/include/eunit.hrl").

% Run all tests
test_all() ->
  seq_tests:test_all(),
  test_send(),
  test_receive().

test_send() ->
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
  ?assertMatch({ok, {integer, 1}, [_], {[{{pid,sample_pid},{integer,0}}, {{pid,sample_pid},{integer,1}}], []}}, 
    eval:eval("module:message_fac((Pid ! 0), Pid).", [{'Pid', {pid, sample_pid}}], World)),
  ?assertMatch({ok, {integer, 6}, [_], 
    {[{{pid, sample_pid}, {integer, 1}},
      {{pid, sample_pid}, {integer, 1}},
      {{pid, sample_pid}, {integer, 2}},
      {{pid, sample_pid}, {integer, 6}}
      ], []}}, 
    eval:eval("module:message_fac(3, Pid).", [{'Pid', {pid, sample_pid}}], World)),
  % send message and fail, no send
  % TODO: does this follow Erlang rules?
  ?assertEqual({error, badarith, {[], []}}, 
    eval:eval("[1, 2 div 0, Pid ! 3].", [{'Pid', {pid, sample_pid}}])),
  ?assertEqual({error, badarith, {[{{pid,sample_pid},{integer,2}}], []}},
    eval:eval("[1, Pid ! 2, 3 div 0].", [{'Pid', {pid, sample_pid}}])).

test_receive() ->
	Proc = 
		"
			X = 2,\n
			receive\n
				Y when is_integer(Y) ->\n
					1;\n
				Y when is_atom(Y) ->\n
					X;\n
				_ ->\n
					receive\n
						Y when is_integer(Y) ->\n
							3;\n
						Messages when length(Messages) == 2 ->\n
							4\n
					end\n
			end.
		",
	{yield, [{'X', {integer, 2}}], _, PS, K1} = eval:eval(Proc),
	
	% message is 5
	?assertEqual({ok, {integer, 1}, [{'X', {integer, 2}}, {'Y', {integer, 5}}], {[], []}},
		cps:applyK({integer, 5}, [{'X', {integer, 2}}], {[], []}, PS, world:world_init(), K1)),
	
	% message is atom
	?assertEqual({ok, {integer, 2}, [{'X', {integer, 2}}, {'Y', {atom, atom}}], {[], []}},
		cps:applyK({atom, atom}, [{'X', {integer, 2}}], {[], []}, PS, world:world_init(), K1)),

	% message is "string"
	{yield, [{'X', {integer, 2}}], _, PS, K2} = 
		cps:applyK({string, 5}, [{'X', {integer, 2}}], {[], []}, PS, world:world_init(), K1),
	
	% second message is 5
	?assertEqual({ok, {integer, 3}, [{'X', {integer, 2}}, {'Y', {integer, 5}}], {[], []}},
		cps:applyK({integer, 5}, [{'X', {integer, 2}}], {[], []}, PS, world:world_init(), K2)),

	% second message is [a, b]
	?assertEqual({ok, {integer, 4}, [{'Messages', {cons, [{atom, a}, {atom, b}]}}, {'X', {integer, 2}}], {[], []}},
		cps:applyK({cons, [{atom, a}, {atom, b}]}, [{'X', {integer, 2}}], {[], []}, PS, world:world_init(), K2)),
	
	% second message is bad_message
	?assertEqual({error, {case_clause, {atom, bad_message}}, {[], []}},
		cps:applyK({atom, bad_message}, [{'X', {integer, 2}}], {[], []}, PS, world:world_init(), K2)).

% test_scheduler()
% test_spawn()
% test_reduce()