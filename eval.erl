-module(eval).
-export([eval_exprs/2, eval_expr/2, test_eval/0, eval_string/2, get_AST/1]).
-include_lib("eunit/include/eunit.hrl").


% Evaluates ASTs with given Bidnings by calling each AST
% linearly and passing the resulting Bindings to the
% next AST.
% - ASTs is the list of trees returned by erl:parse_exprs.
% - Binding is a dictionary in the form [{'<key>', <val>}, ...].
% Returns {ok, Value, NewBindings} | {error, Message}
eval_exprs(ASTs, Bindings) when tl(ASTs) == [] ->
    eval_expr(hd(ASTs), Bindings);
eval_exprs(ASTs, Bindings) ->
    {ok, _, NextBindings} = eval_expr(hd(ASTs), Bindings),
    eval_exprs(tl(ASTs), NextBindings).

% Evaluates the given AST with the given Bidnings.
% - AST is a single one of the trees returned by erl:parse_exprs
% - Binding is dictionary in form [{'<key>', <val>}, ...]
% Returns {ok, Value, NewBindings} | {error, Message}
% TODO: seperate each case to a helper function
eval_expr(AST, Bindings) ->
    case AST of
        % integers
        {integer, _, Val} when is_integer(Val) -> 
            {ok, Val, Bindings};
        % variables - TODO: add guards
        {var, _, Var} ->
            {ok, orddict:fetch(Var, Bindings), Bindings};
        % macthes - TODO: guards?, more match functionality,
        % currently match only allows LHS: var, RHS: int
        {match, _, Exp1, Exp2} ->
            {var, _, LHS} = Exp1,
            {integer, _, RHS} = Exp2,
            IsKey = orddict:is_key(LHS, Bindings),
            if
                IsKey ->
                    NewBindings = orddict:update(LHS, fun(_) -> RHS end, Bindings),
                    {ok, RHS, NewBindings};
                true ->
                    NewBindings = orddict:store(LHS, RHS, Bindings),
                    {ok, RHS, NewBindings}
            end;
        % operations - TODO: allow more operations, add guards
        {op, _, Op, Exp1, Exp2} ->
            {ok, Operand1, _} = eval_expr(Exp1, Bindings),
            {ok, Operand2, _} = eval_expr(Exp2, Bindings),
            case Op of
                '+' when is_integer(Operand1), is_integer(Operand2) ->
                    {ok, Operand1 + Operand2, Bindings};
                '-' when is_integer(Operand1), is_integer(Operand2) ->
                    {ok, Operand1 - Operand2, Bindings};
                '*' when is_integer(Operand1), is_integer(Operand2) ->
                    {ok, Operand1 * Operand2, Bindings};
                'div' when is_integer(Operand1), is_integer(Operand2) ->
                    {ok, Operand1 div Operand2, Bindings}
            end;
        % unrecognized language
        _ -> {error, "Language in the AST is not recognized by the evaluator."}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Helpers for Parsing and Testing %
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return AST structure respresented by the given string
get_AST(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_exprs(Tokens),
    AST.

% call eval after parsing the given string
eval_string(Str, Bindings) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings).

test_eval() ->
  ?assertEqual({ok, 29, []}, eval_string("29.", [])),
  ?assertEqual({ok, 7, []},  eval_string("4 + 3.", [])),
  ?assertEqual({ok, 7, []},  eval_string("9 - 2.", [])),
  ?assertEqual({ok, 10, []}, eval_string("19 - 25 + 4 - 5 + 17.", [])),
  ?assertEqual({ok, 24, []}, eval_string("8 * 3.", [])),
  ?assertEqual({ok, 10, []}, eval_string("20 div 2.", [])),
  ?assertEqual({ok, 92, []}, eval_string("8 * (3 + 9) - (9 div 3 + 1).", [])),
  ?assertEqual({ok, 6, [{'X', 6}]}, eval_string("X.", [{'X', 6}])),
  ?assertEqual({ok, 41, [{'X', 6}, {'Y', 5}, {'Z', 13}]}, 
    eval_string("X + Y * (Z - X).", [{'X', 6}, {'Y', 5}, {'Z', 13}])),
  ?assertEqual({ok, 3, []}, eval_string("1 + 2, 3.", [])),
  ?assertEqual({ok, 1, [{'X', 1}]}, eval_string("X = 1.", [])),
  ?assertEqual({ok, 2, [{'X', 2}]}, eval_string("X = 2.", [{'X', 1}])),
  ?assertEqual({ok, 5, [{'X', 2}, {'Y', 3}]}, eval_string("X = 2, Y = 3, X + Y.", [{'X', 1}])).