-module(eval_tests).
-export([test_general/0, test_all/0]).
-include_lib("eunit/include/eunit.hrl").

% Run all tests
test_all() ->
  test_general()
  test_messeges().

test_general() ->
  % basic artihmetic
  % list operations
  % case of
  % create and use fun
  % simple match
  % complex match
  % factorial
  % function that returns a fun
  ok.

test_messeges() ->
  % send message
  % send message inside operation
  % send message in list
  % send message in fun
  % send message in function
  % send message in function depth 2
  % send message and fail
  % send message in function argument
  ok.

test_receive() ->
  % receive
  % receive inside operation
  % receive in list
  % receive in fun
  % receive in function
  % receive in function depth 2
  ok.
