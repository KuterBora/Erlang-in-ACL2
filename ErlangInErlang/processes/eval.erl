-module(eval).
% evaluators
-export([eval_exprs/3, eval_exprs/4, eval_expr/4]).
% lists, tuples. operations
-export([eval_list/5, eval_tuple/5, eval_op/6, eval_op/5]).
% helpers
-export([get_AST/1, get_AST_form/1, eval/1, eval/2, eval/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  The Evaluator
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates the given list of ASTs in order with the given Bindings and World.
eval_exprs(ASTs, Bindings, World, K) ->
    case tl(ASTs) of
        [] ->
            eval_expr(hd(ASTs), Bindings, World, K);
        _ ->
            eval_expr(hd(ASTs), Bindings, World, {exprs_k, tl(ASTs), K})
    end.

eval_exprs(ASTs, Bindings, World) when ASTs /= [] ->
    eval_exprs(ASTs, Bindings, World, {initial_k}).

% Evaluates the given AST with the given Bindings and World.
eval_expr(AST, Bindings, World, K) ->
    case AST of
        {atom, _, Value} -> 
            cps:applyK({atom, Value}, Bindings, World, K);
        {nil, _} -> 
            cps:applyK({nil, []}, Bindings, World, K);
        {integer, _, Value} -> 
            cps:applyK({integer, Value}, Bindings, World, K);
        {string, _, Value} -> 
            cps:applyK({string, Value}, Bindings, World, K);
        {cons, _, Car, Cdr} ->
            eval_expr(
                Car,
                Bindings,
                World,
                {cons_cdr_k, Cdr, Bindings, K}
            );
        {tuple, _, []} -> 
            cps:applyK({tuple, []}, Bindings, World, K);
        {tuple, Line, TupleList} ->
            eval_expr(
                hd(TupleList),
                Bindings,
                World,
                {tuple_cdr_k, {tuple, Line, tl(TupleList)}, Bindings, K}
            );
        {var, _, Var} -> 
            case orddict:find(Var, Bindings) of
                {ok, Result} -> 
                    cps:applyK(Result, Bindings, World, K);
                _ -> 
                    cps:errorK(unbound, World, K)
            end;
        {'fun', Line, {clauses, Clauses}} -> 
            funs:eval_fun(Clauses, Line, Bindings, World, K);
        {match, _, Expr1, Expr2} ->
            % TODO: LHS must be a pattern
            eval_expr(
                Expr2,
                Bindings,
                World,
                {match_k, Expr1, K}
            );
        {op, _, Op, Expr} ->
            eval_expr(
                Expr,
                Bindings,
                World,
                {op1_k, Op, K});
        {op, _, Op, Expr1, Expr2} -> 
            eval_expr(
                Expr1, 
                Bindings, 
                World,
                {op2_expr1_k, Op, Expr2, Bindings, K}
            );
        {'if', _, Clasues} -> 
            cases:eval_if(Clasues, Bindings, World, K);
        {'case', _, Arg, Clauses} ->
            eval_expr(
                Arg,
                Bindings, 
                World,
                {case_value_k, Clauses, K});
        _ ->
            {error, bad_AST}
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Lists/Tuples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eval_list(CarResult, CdrResult, Bindings, World, K) ->
    case CdrResult of
        {cons, ConsList} ->
            cps:applyK({cons, [CarResult | ConsList]}, Bindings, World, K);
        {nil, []} ->
            cps:applyK({cons, [CarResult]}, Bindings, World, K);
        _ ->
            cps:errorK(badarg, World, K)
    end.

eval_tuple(CarResult, {tuple, TupleList}, Bindings, World, K) ->
    cps:applyK({tuple, [CarResult | TupleList]}, Bindings, World, K).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evalute Expr then apply Op to its result
eval_op(Op, {Type, Value}, Bindings, World, K) ->
    case Op of
        '-' when Type == integer orelse Type == float ->
            cps:applyK({Type, -Value}, Bindings, World, K);
        '+' when Type == integer orelse Type == float ->
            cps:applyK({Type, +Value}, Bindings, World, K);
        'not' when Type == atom, (Value == true orelse Value == false) ->
            cps:applyK({Type, not Value}, Bindings, World, K);
        _ ->
            cps:errorK(badarg, World, K)
    end.

% Evaluates operations.
eval_op(Op, {Type1, Result1}, {Type2, Result2}, Bindings, World, K) ->
    case Op of
        '+' when Type1 == integer, Type2 == integer ->
            cps:applyK({integer, Result1 + Result2}, Bindings, World, K);
        '-' when Type1 == integer, Type2 == integer ->
            cps:applyK({integer, Result1 - Result2}, Bindings, World, K);
        '*' when Type1 == integer, Type2 == integer ->
            cps:applyK({integer, Result1 * Result2}, Bindings, World, K);
        'div' when Type1 == integer, Type2 == integer,
                Result2 == 0 ->
            cps:errorK(badarith, World, K);
        'div' when Type1 == integer, Type2 == integer ->
            cps:applyK({integer, Result1 div Result2}, Bindings, World, K);
        '==' -> 
            cps:applyK({atom, Result1 == Result2}, Bindings, World, K);
        '/=' -> 
            cps:applyK({atom, Result1 /= Result2}, Bindings, World, K);
        '=<' -> 
            cps:applyK({atom, Result1 =< Result2}, Bindings, World, K);
        '<' -> 
            cps:applyK({atom, Result1 < Result2}, Bindings, World, K);
        '>=' -> 
            cps:applyK({atom, Result1 >= Result2}, Bindings, World, K);
        '>' -> 
            cps:applyK({atom, Result1 > Result2}, Bindings, World, K);
        '=:=' -> 
            cps:applyK({atom, Result1 =:= Result2}, Bindings, World, K);
        '=/=' -> 
            cps:applyK({atom, Result1 =/= Result2}, Bindings, World, K);
        'and' when Type1 == atom, Type2 == atom,
                (Result1 == true orelse Result1 == false),
                (Result2 == true orelse Result2 == false) ->
            cps:applyK({atom, Result1 and Result2}, Bindings, World, K);
        'or' when Type1 == atom, Type2 == atom,
                (Result1 == true orelse Result1 == false),
                (Result2 == true orelse Result2 == false) ->
            cps:applyK({atom, Result1 or Result2}, Bindings, World, K);
        'xor' when Type1 == atom, Type2 == atom,
                (Result1 == true orelse Result1 == false),
                (Result2 == true orelse Result2 == false) ->
            cps:applyK({atom, Result1 xor Result2}, Bindings, World, K);
        '++' when Type1 == nil, Type2 == nil ->
            cps:applyK({nil, []}, Bindings, World, K);
        '++' when Type1 == string orelse Type2 == string,
                Type1 == nil orelse Type1 == string,
                Type2 == nil orelse Type2 == string -> 
            cps:applyK({string, Result1 ++ Result2}, Bindings, World, K);
        '++' when Type1 == string orelse Type1 == cons 
                orelse Type1 == nil, Type2 == string 
                orelse Type2 == cons orelse Type2 == nil ->
            cps:applyK({cons, Result1 ++ Result2}, Bindings, World, K);              
        _ ->
            % TODO: seperate unexisting operation from badarg errors
            cps:errorK(badarg, World, K)
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Helpers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return the AST respresented by the given erlang expression in string form.
get_AST(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_exprs(Tokens),
    AST.

% Return the AST respresented by the given erlang form in string form.
get_AST_form(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_form(Tokens),
    AST.

% Parse the given erlang expression in string form, then evaluate it.
% Bindings are set to []
% The World parameter is filled with world:world_init()
eval(Str) ->
    AST = get_AST(Str),
    eval_exprs(AST, [], world:world_init()).

% Parse the given erlang expression in string form, then evaluate it.
% The World parameter is filled with world:world_init()
eval(Str, Bindings) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, world:world_init()).

% Parse the given erlang expression in string form, then evaluate it.
eval(Str, Bindings, World) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, World).