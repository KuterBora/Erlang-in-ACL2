-module(eval).
% evaluators
-export([eval_exprs/3, eval_expr/3]).
% helpers
-export([get_AST/1, get_AST_form/1, eval/2, eval/3]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  The Evaluator
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates the given list of ASTs in order with the given Bindings and World.
% Bindings created by a previous AST are used by the next.
% Value and Bindings produced by the last AST are returned.
eval_exprs(ASTs, Bindings, World) when ASTs /= [], tl(ASTs) == [] ->
    eval_expr(hd(ASTs), Bindings, World); 
eval_exprs(ASTs, Bindings, World) when ASTs /= [] ->
    case eval_expr(hd(ASTs), Bindings, World) of
        {ok, _Result, NextBindings} -> 
            eval_exprs(tl(ASTs), NextBindings, World);
        {yield, _Kont, _Out} ->
            yield_todo;
        {error, Exception} -> 
            {error, Exception}
    end.

% Evaluates the given AST with the given Bindings and World.
eval_expr(AST, Bindings, World) ->
    case AST of
        {atom, _Line, Value} -> 
            {ok, {atom, Value}, Bindings};
        {nil, _Line} -> 
            {ok, {nil, []}, Bindings};
        {integer, _Line, Value} -> 
            {ok, {integer, Value}, Bindings};
        {float, _Line, Value} -> 
            {ok, {float, Value}, Bindings};
        {string, _Line, Value} -> 
            {ok, {string, Value}, Bindings};
        {cons, _Line, Car, Cdr} ->
            eval_list(Car, Cdr, Bindings, World);
        {tuple, _Line, TupleList} -> 
            eval_tuple(TupleList, Bindings, World);
        {var, _Line, Var} -> 
            case orddict:find(Var, Bindings) of
                {ok, Value} -> {ok, Value, Bindings};
                _ -> {error, unbound}
            end;
        {'fun', Line, {clauses, Clauses}} -> 
            funs:eval_fun(Clauses, Line, Bindings);
        {match, _Line, Expr1, Expr2} ->
            EvalRHS = eval_expr(Expr2, Bindings, World),
            case EvalRHS of
                {ok, Value, NewBindings} ->
                    match:eval_match(Expr1, Value, NewBindings, World);
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ ->
                    EvalRHS
            end;
        {op, _Line, Op, Expr} ->
            eval_op(Op, Expr, Bindings, World);
        {op, _Line, Op, Expr1, Expr2} -> 
            eval_op(Op, Expr1, Expr2 , Bindings, World);
        {'if', _Line, Clasues} -> 
            cases:eval_if(Clasues, Bindings, World);
        {'case', _Line, Arg, Clauses} ->
            EvalArg = eval_expr(Arg, Bindings, World),
            case EvalArg of
                {ok, Value, NewBindings} ->
                    cases:eval_case(Value, Clauses, NewBindings, World);
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ ->
                    EvalArg
            end;
        {'try', _Line, Exprs, Patterns, CatchClauses, _} ->
            cases:eval_try(
                Exprs,
                Patterns,
                CatchClauses,
                Bindings,
                World);
        {call, _Line1, {atom, _Line2, FName}, Args} -> 
            functions:eval_local_call(FName, Args, Bindings, World);
        {call, _Line1, {remote, _Line2, {atom, _Line3, MName}, 
                {atom, _Line4, FName} }, Args} -> 
            functions:eval_call(MName, FName, Args, Bindings, World);
        {call, _Line, CallExpr, Args} ->
            funs:eval_fun_call(CallExpr, Args, Bindings, World);
        _ -> 
            {error, bad_AST}
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Lists/Tuples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate Car and Cdr, merge the Bindings and Out
eval_list(Car, Cdr, Bindings, World) ->
    EvalCar = eval_expr(Car, Bindings, World),
    case EvalCar of
        {ok, CarResult, CarBindings} ->
            EvalCdr = eval_expr(Cdr, Bindings, World),
            case EvalCdr of
                {ok, CdrResult, CdrBindings} ->
                    NewBindings = 
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            CarBindings,
                            CdrBindings
                        ),    
                    case CdrResult of
                        {cons, Tail} ->
                            {ok, {cons, [CarResult | Tail]}, NewBindings};
                        {nil, []} ->
                            {ok, {cons, [CarResult]}, NewBindings};
                        _ ->
                            {error, badarg}
                    end;
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ -> 
                    EvalCdr
            end;
        {yield, _Kont, _Out} ->
            yield_todo;
        _ -> 
            EvalCar
    end.

% Evaluate each element of the Tuple, merge the Bindings and Out
eval_tuple([], Bindings, _World) ->
    {ok, {tuple, []}, Bindings};
eval_tuple([Hd | Tl], Bindings, World) ->
    EvalHead = eval_expr(Hd, Bindings, World),
    case EvalHead of
        {ok, HeadResult, HeadBindings} ->
            EvalTail = eval_tuple(Tl, Bindings, World),
            case EvalTail of
                {ok, {tuple, TailResult}, TailBindings} ->
                    Result = {tuple, [HeadResult | TailResult]},
                    NewBindings = 
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            HeadBindings,
                            TailBindings
                        ),
                    {ok, Result, NewBindings};
                {yield, _Kont, _Out} ->
                    yield_todo;
                {ok, _, _} ->
                    {error, badarg};
                _ ->
                    EvalTail
            end;
        {yield, _Kont, _Out} ->
            yield_todo;
        _ ->
            EvalHead
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evalute Expr then apply Op to its result
eval_op(Op, Expr, Bindings, World) ->
    Operand = eval_expr(Expr, Bindings, World),
    case Operand of
        {ok, {Type, Value}, NewBindings} -> 
            case Op of
                '-' when Type == integer orelse Type == float ->
                    {ok, {Type, -Value}, NewBindings};
                '+' when Type == integer orelse Type == float ->
                    {ok, {Type, +Value}, NewBindings};
                'not' when Type == atom,
                        (Value == true orelse Value == false) ->
                    {ok, {Type, not Value, NewBindings}};
                _ ->
                    {error, badarg}
            end;
        {yield, _Kont, _Out} ->
            yield_todo;    
        _ ->
            Operand
    end.

% Evalute Expr1 and Expr2 then apply Op
eval_op(Op, Expr1, Expr2, Bindings, World) ->
    Operand1 = eval_expr(Expr1, Bindings, World),
    case Operand1 of
        {ok, {Type1, Result1}, Bindings1} ->
            Operand2 = eval_expr(Expr2, Bindings, World),
            case Operand2 of
                {ok, {Type2, Result2}, Bindings2} ->
                    NewBindings = 
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            Bindings1,
                            Bindings2
                        ),
                    case Op of
                        '+' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 + Result2}, NewBindings};
                        '+' when Type1 == float orelse Type2 == float ->
                            {ok, {float, Result1 + Result2}, NewBindings};
                        '-' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 - Result2}, NewBindings};
                        '-' when Type1 == float orelse Type2 == float ->
                            {ok, {float, Result1 - Result2}, NewBindings};
                        '*' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 * Result2}, NewBindings};
                        '*' when Type1 == float orelse Type2 == float ->
                            {ok, {float, Result1 * Result2}, NewBindings};
                        '/' when (Type1 == integer orelse Type1 == float),
                                (Type2 == integer orelse Type2 == float),
                                Result2 == 0 ->
                            {error, badarith};
                        '/' when (Type1 == integer orelse Type1 == float),
                                (Type2 == integer orelse Type2 == float) ->
                            {ok, {float, Result1 / Result2}, NewBindings};
                        'div' when Type1 == integer, Type2 == integer,
                                Result2 == 0 ->
                            {error, badarith};
                        'div' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 div Result2}, NewBindings};
                        '==' -> 
                            {ok, {atom, Result1 == Result2}, NewBindings};
                        '/=' -> 
                            {ok, {atom, Result1 /= Result2}, NewBindings};
                        '=<' -> 
                            {ok, {atom, Result1 < Result2}, NewBindings};
                        '<' -> 
                            {ok, {atom, Result1 < Result2}, NewBindings};
                        '>=' -> 
                            {ok, {atom, Result1 < Result2}, NewBindings};
                        '>' -> 
                            {ok, {atom, Result1 > Result2}, NewBindings};
                        '=:=' -> 
                            {ok, {atom, Result1 =:= Result2}, NewBindings};
                        '=/=' -> 
                            {ok, {atom, Result1 =/= Result2}, NewBindings};
                        'and' when Type1 == atom, Type2 == atom,
                                (Result1 == true orelse Result1 == false),
                                (Result2 == true orelse Result2 == false) ->
                            {ok, {atom, Result1 and Result2}, NewBindings};
                        'or' when Type1 == atom, Type2 == atom,
                                (Result1 == true orelse Result1 == false),
                                (Result2 == true orelse Result2 == false) ->
                            {ok, {atom, Result1 or Result2}, NewBindings};
                        'xor' when Type1 == atom, Type2 == atom,
                                (Result1 == true orelse Result1 == false),
                                (Result2 == true orelse Result2 == false) ->
                            {ok, {atom, Result1 xor Result2}, NewBindings};
                        '++' when Type1 == nil, Type2 == nil ->
                            {ok, {nil, []}, NewBindings};
                        '++' when Type1 == string orelse Type2 == string,
                                Type1 == nil orelse Type1 == string,
                                Type2 == nil orelse Type2 == string -> 
                            {ok, {string, Result1 ++ Result2}, NewBindings};
                        '++' when Type1 == string orelse Type1 == cons 
                                orelse Type1 == nil, Type2 == string 
                                orelse Type2 == cons orelse Type2 == nil ->
                            {ok, {cons, Result1 ++ Result2}, NewBindings};
                        '!' when Type1 == pid ->
                            {ok, Result2, NewBindings};                     
                        _ ->
                            {error, badarg}
                    end;
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ ->
                    Operand2
            end;
        {yield, _Kont, _Out} ->
            yield_todo;
        _ ->
            Operand1
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
% The World parameter is filled with world:world_init()
eval(Str, Bindings) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, world:world_init()).

% Parse the given erlang expression in string form, then evaluate it.
eval(Str, Bindings, World) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, World).