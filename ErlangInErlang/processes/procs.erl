-module(procs).
-export([empty_box/0, init_state/0]).

init_state() ->
    #{ module => '#none', pid => '<0.0.0>'}.

empty_box() ->
    {[], []}.