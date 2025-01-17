-module(eval).
% evaluators
-export([eval_exprs/5, eval_expr/5, eval_exprs/2]).
% helpers
-export([get_AST/1, get_AST_form/1, eval/2, eval/3]).

% can funs declared in one module be called from another module and 
% have acess to local calls?

% guards cannot make certain calls
% args cannot use the bindings they created
% Lists cannot use ethe bindings they created
% Tuples also cannot use bindings they created
% so you only need to save the bindings obtained before the expression is about to be evaluated.

% yield needs to know Procstate...
% all the previous calss will be already evaluated, so it fine to just save the most recent Procstate
% except for Eval_Exprs()...

% function call itself cannot use the bidnings form the arguments,  this is important for funs
% for example: can't do X(X = fun() -> 1 end). 

% TODO:
% message tests
% fix args both seq and par
% yield
% yield tests
% fix guards both seq and par
% clean up par
% scheduler, and runner
% message tests
% yield
% yield tests
% scheduler, and runner, keep in mind slef and spawn
% self() and spawn()

% Bindings, Out, ProcState (world, current_module, pid)
% OutBox is {Sent, Spwaned}

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  The Evaluator
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates the given list of ASTs in order with the given Bindings and World.
% Bindings created by a previous AST are used by the next.
% Value and Bindings produced by the last AST are returned.
eval_exprs(ASTs, Bindings, OutBox, ProcState, World) when ASTs /= [] ->
    EvalValue = eval_expr(hd(ASTs), Bindings, OutBox, ProcState, World),
    case EvalValue of
        {ok, _, _, _} when tl(ASTs) == [] ->
            EvalValue;
        {ok, _Result, NextBindings, NextOutBox} -> 
            eval_exprs(tl(ASTs), NextBindings, NextOutBox, ProcState, World);
        {yield, Receive, Kont, Out} when tl(ASTs) == [] ->
            {yield, Receive, [Kont], Bindings, Out};
        {yield, Receive, Kont, NewOutBox} ->
            {yield, Receive, [Kont | tl(ASTs)], Bindings, NewOutBox};
        _ ->
            EvalValue 
    end.

% Evaluates the given AST with the given Bindings and World.
eval_expr(AST, Bindings, OutBox, ProcState, World) ->
    case AST of
        {atom, _Line, Value} -> 
            {ok, {atom, Value}, Bindings, OutBox};
        {nil, _Line} -> 
            {ok, {nil, []}, Bindings, OutBox};
        {integer, _Line, Value} -> 
            {ok, {integer, Value}, Bindings, OutBox};
        {float, _Line, Value} -> 
            {ok, {float, Value}, Bindings, OutBox};
        {string, _Line, Value} -> 
            {ok, {string, Value}, Bindings, OutBox};
        {cons, Line, Car, Cdr} ->
            eval_list(Car, Cdr, Line, Bindings, OutBox, ProcState, World);
        {tuple, Line, TupleList} -> 
            eval_tuple(TupleList, Line, Bindings, OutBox, ProcState, World);
        {var, _Line, Var} -> 
            case orddict:find(Var, Bindings) of
                {ok, Value} -> 
                    {ok, Value, Bindings, OutBox};
                _ -> 
                    {error, unbound, OutBox}
            end;
        {'fun', Line, {clauses, Clauses}} -> 
            funs:eval_fun(Clauses, Line, Bindings, OutBox, ProcState);
        {match, Line, Expr1, Expr2} ->
            EvalRHS = eval_expr(Expr2, Bindings, OutBox, ProcState, World),
            case EvalRHS of
                {ok, Value, NewBindings, NewOutBox} ->
                    match:eval_match(
                        Expr1,
                        Value,
                        NewBindings,
                        NewOutBox,
                        ProcState,
                        World
                    );
                {yield, Receive, Kont, Out} ->
                    {yield, Receive, {match, Line, Expr1, Kont}, Out};
                _ ->
                    EvalRHS
            end;
        {op, Line, Op, Expr} ->
            eval_op(Op, Expr, Line, Bindings, OutBox, ProcState, World);
        {op, Line, Op, Expr1, Expr2} -> 
            eval_op(Op, Expr1, Expr2, Line, Bindings, OutBox, ProcState, World);
        {'if', _Line, Clasues} -> 
            cases:eval_if(Clasues, Bindings, OutBox, ProcState, World);
        {'case', Line, Arg, Clauses} ->
            EvalArg = eval_expr(Arg, Bindings, OutBox, ProcState, World),
            case EvalArg of
                {ok, Value, NewBindings, NewOutBox} ->
                    cases:eval_case(Value, Clauses, NewBindings, NewOutBox, ProcState, World);
                {yield, Receive, Kont, Out} ->
                    {yield, Receive, {'case', Line, Kont, Clauses}, Out};
                _ ->
                    EvalArg
            end;
        {'call', Line, Call, Args} ->
            functions:eval_calls(Call, Line, Args, Bindings, OutBox, ProcState, World);
        {'receive', Line, Clauses} ->
            {yield, Clauses, {var, Line, '#receive'}, OutBox};
        _ -> 
            {error, bad_AST, OutBox}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Lists/Tuples
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate Car and Cdr, merge the Bindings and Out
eval_list(Car, Cdr, Line, Bindings, OutBox, ProcState, World) ->
    EvalCar = eval_expr(Car, Bindings, OutBox, ProcState, World),
    case EvalCar of
        {ok, CarResult, CarBindings, CarOutBox} ->
            EvalCdr = eval_expr(Cdr, Bindings, CarOutBox, ProcState, World),
            case EvalCdr of
                {ok, CdrResult, CdrBindings, CdrOutBox} ->
                    NewBindings = 
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            CarBindings,
                            CdrBindings
                        ),    
                    case CdrResult of
                        {cons, Tail} ->
                            {ok, {cons, [CarResult | Tail]}, NewBindings, CdrOutBox};
                        {nil, []} ->
                            {ok, {cons, [CarResult]}, NewBindings, CdrOutBox};
                        _ ->
                            {error, badarg, CdrOutBox} % or should it be just OutBox?
                    end;
                {yield, Receive, Kont, Out} ->
                    {yield, Receive, {cons, Line, value_to_AST(CarResult, Line), Kont}, Out};
                _ -> 
                    EvalCdr
            end;
        {yield, Receive, Kont, Out} ->
            {yield, Receive, {cons, Line, Kont, Cdr}, Out};
        _ -> 
            EvalCar
    end.

% Evaluate each element of the Tuple, merge the Bindings and Out
eval_tuple([], _, Bindings, OutBox, _, _) ->
    {ok, {tuple, []}, Bindings, OutBox};
eval_tuple([Hd | Tl], Line, Bindings, OutBox, ProcState, World) ->
    EvalHead = eval_expr(Hd, Bindings, OutBox, ProcState, World),
    case EvalHead of
        {ok, HeadResult, HeadBindings, HeadOutBox} ->
            EvalTail = eval_tuple(Tl, Line, Bindings, HeadOutBox, ProcState, World),
            case EvalTail of
                {ok, {tuple, TailResult}, TailBindings, TailOutBox} ->
                    Result = {tuple, [HeadResult | TailResult]},
                    NewBindings = 
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            HeadBindings,
                            TailBindings
                        ),
                    {ok, Result, NewBindings, TailOutBox};
                {yield, Receive, {tuple, KLine, Kont}, Out} ->
                    {yield, Receive, {tuple, KLine, [value_to_AST(HeadResult, KLine) | Kont]}, Out};
                {ok, _, TailOutBox} ->
                    {error, badarg, TailOutBox};
                _ ->
                    EvalTail
            end;
        {yield, Receive, Kont, Out} ->
            {yield, Receive, {tuple, Line, [Kont | Tl]}, Out};
        _ ->
            EvalHead
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Operations
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evalute Expr then apply Op to its result
eval_op(Op, Expr, Line, Bindings, OutBox, ProcState, World) ->
    Operand = eval_expr(Expr, Bindings, OutBox, ProcState, World),
    case Operand of
        {ok, {Type, Value}, NewBindings, NewOutBox} -> 
            case Op of
                '-' when Type == integer orelse Type == float ->
                    {ok, {Type, -Value}, NewBindings, NewOutBox};
                '+' when Type == integer orelse Type == float ->
                    {ok, {Type, +Value}, NewBindings, NewOutBox};
                'not' when Type == atom,
                        (Value == true orelse Value == false) ->
                    {ok, {Type, not Value, NewBindings, NewOutBox}};
                _ ->
                    {error, badarg, NewOutBox}
            end;
        {yield, Receive, Kont, Out} ->
            {yield, Receive, {op, Line, Op, Kont}, Out}; 
        _ ->
            Operand
    end.

%
% self() ! 2 + receive 2 -> 2 end.
% returns 4 
% turn it into 2 + kont

% Evalute Expr1 and Expr2 then apply Op
eval_op(Op, Expr1, Expr2, Line, Bindings, OutBox, ProcState, World) ->
    Operand1 = eval_expr(Expr1, Bindings, OutBox, ProcState, World),
    case Operand1 of
        {ok, {Type1, Result1}, Bindings1, NewOutBox1} ->
            Operand2 = eval_expr(Expr2, Bindings, NewOutBox1, ProcState, World),
            case Operand2 of
                {ok, {Type2, Result2}, Bindings2, NewOutBox2} ->
                    NewBindings = 
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            Bindings1,
                            Bindings2
                        ),
                    case Op of
                        '+' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 + Result2}, NewBindings, NewOutBox2};
                        '+' when Type1 == float orelse Type2 == float ->
                            {ok, {float, Result1 + Result2}, NewBindings, NewOutBox2};
                        '-' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 - Result2}, NewBindings, NewOutBox2};
                        '-' when Type1 == float orelse Type2 == float ->
                            {ok, {float, Result1 - Result2}, NewBindings, NewOutBox2};
                        '*' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 * Result2}, NewBindings, NewOutBox2};
                        '*' when Type1 == float orelse Type2 == float ->
                            {ok, {float, Result1 * Result2}, NewBindings, NewOutBox2};
                        '/' when (Type1 == integer orelse Type1 == float),
                                (Type2 == integer orelse Type2 == float),
                                Result2 == 0 ->
                            {error, badarith, NewOutBox2};
                        '/' when (Type1 == integer orelse Type1 == float),
                                (Type2 == integer orelse Type2 == float) ->
                            {ok, {float, Result1 / Result2}, NewBindings, NewOutBox2};
                        'div' when Type1 == integer, Type2 == integer,
                                Result2 == 0 ->
                            {error, badarith, NewOutBox2};
                        'div' when Type1 == integer, Type2 == integer ->
                            {ok, {integer, Result1 div Result2}, NewBindings, NewOutBox2};
                        '==' -> 
                            {ok, {atom, Result1 == Result2}, NewBindings, NewOutBox2};
                        '/=' -> 
                            {ok, {atom, Result1 /= Result2}, NewBindings, NewOutBox2};
                        '=<' -> 
                            {ok, {atom, Result1 < Result2}, NewBindings, NewOutBox2};
                        '<' -> 
                            {ok, {atom, Result1 < Result2}, NewBindings, NewOutBox2};
                        '>=' -> 
                            {ok, {atom, Result1 < Result2}, NewBindings, NewOutBox2};
                        '>' -> 
                            {ok, {atom, Result1 > Result2}, NewBindings, NewOutBox2};
                        '=:=' -> 
                            {ok, {atom, Result1 =:= Result2}, NewBindings, NewOutBox2};
                        '=/=' -> 
                            {ok, {atom, Result1 =/= Result2}, NewBindings, NewOutBox2};
                        'and' when Type1 == atom, Type2 == atom,
                                (Result1 == true orelse Result1 == false),
                                (Result2 == true orelse Result2 == false) ->
                            {ok, {atom, Result1 and Result2}, NewBindings, NewOutBox2};
                        'or' when Type1 == atom, Type2 == atom,
                                (Result1 == true orelse Result1 == false),
                                (Result2 == true orelse Result2 == false) ->
                            {ok, {atom, Result1 or Result2}, NewBindings, NewOutBox2};
                        'xor' when Type1 == atom, Type2 == atom,
                                (Result1 == true orelse Result1 == false),
                                (Result2 == true orelse Result2 == false) ->
                            {ok, {atom, Result1 xor Result2}, NewBindings, NewOutBox2};
                        '++' when Type1 == nil, Type2 == nil ->
                            {ok, {nil, []}, NewBindings, NewOutBox2};
                        '++' when Type1 == string orelse Type2 == string,
                                Type1 == nil orelse Type1 == string,
                                Type2 == nil orelse Type2 == string -> 
                            {ok, {string, Result1 ++ Result2}, NewBindings, NewOutBox2};
                        '++' when Type1 == string orelse Type1 == cons 
                                orelse Type1 == nil, Type2 == string 
                                orelse Type2 == cons orelse Type2 == nil ->
                            {ok, {cons, Result1 ++ Result2}, NewBindings, NewOutBox2};
                        '!' when Type1 == pid ->
                            {Sent, Spawned} = NewOutBox2,
                            NewOutBox = {Sent ++ [{{Type1, Result1}, {Type2, Result2}}], Spawned},
                            {ok, {Type2, Result2}, NewBindings, NewOutBox};                     
                        _ ->
                            {error, badarg, NewOutBox2}
                    end;
                {yield, Receive, Kont, Out} ->
                    {yield, Receive, {op, Line, Op, value_to_AST({Type1, Result1}, Line), Kont}, Out};
                _ ->
                    Operand2
            end;
        {yield, Receive, Kont, Out} ->
            {yield, Receive, {op, Line, Op, Kont, Expr2}, Out};
        _ ->
            Operand1
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Helpers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

value_to_AST(Value, Line) ->
    case Value of
        {atom, A} ->
            {atom, Line, A};
        {integer, I} ->
            {integer, Line, I};
        {float, F} ->
            {float, Line, F};
        {string, S} ->
            {string, Line, S};
        {nil, []} ->
            {nil, Line};
        {cons, List} when tl(List) == [] ->
            {cons, Line,
                value_to_AST(hd(List), Line),
                {nil, Line}};
        {cons, List} ->
            {cons, Line, 
                value_to_AST(hd(List), Line),
                value_to_AST({cons, tl(List)}, Line)};
        {tuple, List} ->
            {tuple, Line,
                lists:map(
                    fun(X) -> value_to_AST(X, Line) end,
                    List 
                )};
        {'fun', FunTag} ->
            {var, Line, FunTag};
        {pid, Pid} ->
            {pid, Line, Pid}
    end.

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
    ProcState = #{ module => '#none', pid => '<0.0.0>'},
    eval_exprs(AST, Bindings, procs:empty_box(), ProcState, world:world_init()).

% Parse the given erlang expression in string form, then evaluate it.
eval(Str, Bindings, World) ->
    AST = get_AST(Str),
    ProcState = #{ module => '#none', pid => '<0.0.0>'},
    eval_exprs(AST, Bindings, procs:empty_box(), ProcState, World).

eval_exprs(ASTs, Bindings) ->
    ProcState = #{ module => '#none', pid => '<0.0.0>'},
    eval_exprs(ASTs, Bindings, procs:empty_box(), ProcState, world:world_init()).
