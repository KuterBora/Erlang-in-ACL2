-module(eval).
% evaluators
-export([eval_exprs/4, eval_exprs/6, eval_expr/6]).
% lists, tuples. operations
-export([eval_list/7, eval_tuple/7, eval_op/8, eval_op/7]).
% helpers
-export([get_AST/1, get_AST_form/1, eval/1, eval/2, eval/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  The Evaluator
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates the given list of ASTs in order with the given Bindings and World.
eval_exprs(ASTs, Bindings, Out, ProcState, World, K) ->
    case tl(ASTs) of
        [] ->
            eval_expr(
                hd(ASTs),
                Bindings,
                Out,
                ProcState,
                World,
                K);
        _ ->
            eval_expr(
                hd(ASTs),
                Bindings,
                Out,
                ProcState,
                World,
                {exprs_k, tl(ASTs), K}
            )
    end.

eval_exprs(ASTs, Bindings, ProcState, World) when ASTs /= [] ->
    eval_exprs(
        ASTs,
        Bindings,
        procs:empty_box(),
        ProcState,
        World,
        {initial_k}
    ).

% Evaluates the given AST with the given Bindings and World.
eval_expr(AST, Bindings, Out, ProcState, World, K) ->
    case AST of
        {atom, _, Value} -> 
            cps:applyK(
                {atom, Value},
                Bindings,
                Out,
                ProcState,
                World, 
                K);
        {nil, _} -> 
            cps:applyK(
                {nil, []},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        {integer, _, Value} -> 
            cps:applyK(
                {integer, Value},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        {string, _, Value} -> 
            cps:applyK(
                {string, Value},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        {cons, _, Car, Cdr} ->
            eval_expr(
                Car,
                Bindings,
                Out,
                ProcState,
                World,
                {cons_cdr_k, Cdr, Bindings, K}
            );
        {tuple, _, []} -> 
            cps:applyK(
                {tuple, []},
                Bindings,
                Out,
                ProcState,
                World,
                K);
        {tuple, Line, TupleList} ->
            eval_expr(
                hd(TupleList),
                Bindings,
                Out,
                ProcState,
                World,
                {tuple_cdr_k, {tuple, Line, tl(TupleList)}, Bindings, K}
            );
        {var, _, Var} -> 
            case orddict:find(Var, Bindings) of
                {ok, Result} -> 
                    cps:applyK(
                        Result,
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K);
                _ -> 
                    cps:errorK(unbound, Out, ProcState, World, K)
            end;
        {'fun', Line, {clauses, Clauses}} -> 
            funs:eval_fun(
                Clauses,
                Line,
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        {match, _, Expr1, Expr2} ->
            % TODO: LHS must be a pattern
            eval_expr(
                Expr2,
                Bindings,
                Out,
                ProcState,
                World,
                {match_k, Expr1, K}
            );
        {op, _, Op, Expr} ->
            eval_expr(
                Expr,
                Bindings,
                Out,
                ProcState,
                World,
                {op1_k, Op, K});
        {op, _, Op, Expr1, Expr2} -> 
            eval_expr(
                Expr1, 
                Bindings,
                Out,
                ProcState, 
                World,
                {op2_expr1_k, Op, Expr2, Bindings, K}
            );
        {'if', _, Clasues} -> 
            cases:eval_if(
                Clasues,
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        {'case', _, Arg, Clauses} ->
            eval_expr(
                Arg,
                Bindings,
                Out,
                ProcState,
                World,
                {case_value_k, Clauses, K}
            );
        {'call', _, Call, Args} ->
            functions:eval_calls(
                Call,
                Args,
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        _ ->
            {seg_fault, bad_AST}
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Lists/Tuples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

eval_list(CarResult, CdrResult, Bindings, Out, ProcState, World, K) ->
    case CdrResult of
        {cons, ConsList} ->
            cps:applyK(
                {cons, [CarResult | ConsList]},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        {nil, []} ->
            cps:applyK(
                {cons, [CarResult]},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        _ ->
            cps:errorK(badarg, Out, ProcState, World, K)
    end.

eval_tuple(CarResult, {tuple, TList}, Bindings, Out, ProcState, World, K) ->
    cps:applyK(
        {tuple, [CarResult | TList]},
        Bindings,
        Out,
        ProcState,
        World,
        K
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evalute Expr then apply Op to its result
eval_op(Op, {Type, Value}, Bindings, Out, ProcState, World, K) ->
    case Op of
        '-' when Type == integer ->
            cps:applyK({Type, -Value}, Bindings, Out, ProcState, World, K);
        '+' when Type == integer ->
            cps:applyK({Type, +Value}, Bindings, Out, ProcState, World, K);
        'not' when Type == atom, (Value == true orelse Value == false) ->
            cps:applyK({Type, not Value}, Bindings, Out, ProcState, World, K);
        _ ->
            cps:errorK(badarg, Out, ProcState, World, K)
    end.

% Evaluates operations.
eval_op(Op, {T1, R1}, {T2, R2}, Bindings, Out, ProcState, World, K) ->
    case Op of
        '+' when T1 == integer, T2 == integer ->
            cps:applyK(
                {integer, R1 + R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '-' when T1 == integer, T2 == integer ->
            cps:applyK(
                {integer, R1 - R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '*' when T1 == integer, T2 == integer ->
            cps:applyK(
                {integer, R1 * R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        'div' when T1 == integer, T2 == integer,
                R2 == 0 ->
            cps:errorK(badarith, Out, ProcState, World, K);
        'div' when T1 == integer, T2 == integer ->
            cps:applyK(
                {integer, R1 div R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '==' -> 
            cps:applyK(
                {atom, R1 == R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '/=' -> 
            cps:applyK(
                {atom, R1 /= R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '=<' -> 
            cps:applyK(
                {atom, R1 =< R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '<' -> 
            cps:applyK(
                {atom, R1 < R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '>=' -> 
            cps:applyK(
                {atom, R1 >= R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '>' -> 
            cps:applyK(
                {atom, R1 > R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '=:=' -> 
            cps:applyK(
                {atom, R1 =:= R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '=/=' -> 
            cps:applyK(
                {atom, R1 =/= R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        'and' when T1 == atom, T2 == atom,
                (R1 == true orelse R1 == false),
                (R2 == true orelse R2 == false) ->
            cps:applyK(
                {atom, R1 and R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        'or' when T1 == atom, T2 == atom,
                (R1 == true orelse R1 == false),
                (R2 == true orelse R2 == false) ->
            cps:applyK(
                {atom, R1 or R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        'xor' when T1 == atom, T2 == atom,
                (R1 == true orelse R1 == false),
                (R2 == true orelse R2 == false) ->
            cps:applyK(
                {atom, R1 xor R2},
                Bindings,
                Out,
                ProcState, 
                World,
                K
            );
        '++' when T1 == nil, T2 == nil ->
            cps:applyK(
                {nil, []},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '++' when T1 == string orelse T2 == string,
                T1 == nil orelse T1 == string,
                T2 == nil orelse T2 == string -> 
            cps:applyK(
                {string, R1 ++ R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );
        '++' when T1 == string orelse T1 == cons 
                orelse T1 == nil, T2 == string 
                orelse T2 == cons orelse T2 == nil ->
            cps:applyK(
                {cons, R1 ++ R2},
                Bindings,
                Out,
                ProcState,
                World,
                K
            );              
        _ ->
            cps:errorK(badast, Out, ProcState, World, K)
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
    eval_exprs(AST, [], procs:init_state(), world:world_init()).

% Parse the given erlang expression in string form, then evaluate it.
% The World parameter is filled with world:world_init()
eval(Str, Bindings) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, procs:init_state(), world:world_init()).

% Parse the given erlang expression in string form, then evaluate it.
eval(Str, Bindings, World) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, procs:init_state(), World).