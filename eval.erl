-module(eval).
% evaluators
-export([eval_exprs/3, eval_expr/3, eval/2, eval/3]).
% helpers to create ASTs
-export([get_AST/1, get_AST_form/1]).

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
            eval_if(Clasues, Bindings, World);
        {'case', _Line, Arg, Clauses} ->
            EvalArg = eval_expr(Arg, Bindings, World),
            case EvalArg of
                {ok, Value, NewBindings} ->
                    eval_case(Value, Clauses, NewBindings, World);
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ ->
                    EvalArg
            end;
        {'try', _Line, Exprs, Patterns, CatchClauses, _} ->
            eval_try(
                Exprs,
                Patterns,
                CatchClauses,
                Bindings,
                World);
        {call, _Line1, {atom, _Line2, Function_Name}, Args} -> 
            eval_call(local, Function_Name, Args, Bindings, World);
        {call, _Line1, {remote, _Line2, {atom, _Line3, Module_Name}, 
                {atom, _Line4, Function_Name} }, Args} -> 
            eval_call(Module_Name, Function_Name, Args, Bindings, World);
        
        % call to fun expression
        {call, _Line, Fun_Call, Args} ->
            Fun_Exp = eval_expr(Fun_Call, Bindings, World),
            case Fun_Exp of
                {ok, {'fun', {Name, Arity}}, NewBindings} ->
                    % TODO: error handlig for when the number of args is incorrect,
                    {{clauses, Clauses}, Fun_Bindings} = orddict:fetch({Name, Arity}, NewBindings),
                    Eval_Value = eval_fun_body(Clauses, Args, Bindings, Fun_Bindings, World, World),
                    case Eval_Value of
                        % TODO,  new   bindings if it returns a fun
                        {ok, Value, _} -> {ok, Value, NewBindings};
                        _ -> Eval_Value
                    end;
                _ -> Fun_Exp
            end;
        % fun
        {'fun', Line, {clauses, Clauses}} -> eval_fun(Clauses, Line, Bindings, World);
        % not accepted language
        _ -> {error, bad_AST}
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
%  Evaluate Guards/if/case/try
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a list of guards: return true if every expression evaluates to true.
% Guards cannot have matches, send, or function calls except BIFs.
eval_guards([], _, _) -> true;
eval_guards([Guard | Rest], Bindings, World) ->
    GuardResult = eval_expr(Guard, Bindings, World),
    case GuardResult of
        {ok, {atom, true}, Bindings} -> 
            eval_guards(Rest, Bindings, World);
        {ok, {atom, false}, Bindings} -> 
            false;
        {yield, _Kont, _Out} ->
            yield_todo;
        _ -> 
            {error, illegal_guard}
    end.

% Evaluate an if clause by recursively checking if the guards hold
eval_if([], _, _) -> {error, if_clause};
eval_if([HdClause | TlClauses], Bindings, World) ->
    {clause, _Line, [], [Guards], Body} = HdClause,
    EvalGuards = eval_guards(Guards, Bindings, world:world_init()),
    if 
        EvalGuards ->
            eval_exprs(Body, Bindings, World);
        true -> 
            eval_if(TlClauses, Bindings, World)
    end.

% Evaluate a case expression by recursively checking if the match
% and the guards hold.
eval_case(Value, [], _, _) -> {error, {case_clause, Value}};
eval_case(Value, [HdClause | TlClauses], Bindings, World) ->
    {clause, _Line, [Case], Guards, Body} = HdClause,
    TryMatch = match:eval_match(Case, Value, Bindings, World),
    case TryMatch of
        {ok, _Result, NewBindings} ->
            GuardResult = case Guards of
                            [] ->
                                true;
                            [GuardList] ->
                                eval_guards(
                                    GuardList,
                                    NewBindings,
                                    world:world_init()
                                );
                            _ ->
                                {error, illegal_guard}
                            end,
            if
                GuardResult ->
                    eval_exprs(Body, NewBindings, World);
                true ->
                    eval_case(Value, TlClauses, Bindings, World)
            end;
        {yield, _Kont, _Out} ->
            yield_todo;
        {error, {badmatch, Value}} ->
            eval_case(Value, TlClauses, Bindings, World);
        _ ->
            TryMatch
    end.

% Evaluate a try catch expression (incomplete)
eval_try(Exprs, [], _, Bindings, World) ->
    Eval_Result = eval_exprs(Exprs, Bindings, World),
    case Eval_Result of
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings}; 
        {error, _} -> {ok, {atom, false}, Bindings}
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate function calls
eval_call(Module_Name, Function_Name, Args, Bindings, World) 
        when is_map_key(Module_Name, World) ->
    Module = maps:get(Module_Name, World),
    Arity = length(Args),
    if
        is_map_key({Function_Name, Arity}, Module) ->
            Function_Def = maps:get({Function_Name, Arity}, Module),
            Local_Module = maps:merge(world:local_module(), Module),
            Local_World = world:world_add_module(World, local, Local_Module),
            ArgValues = eval_args(Args, Bindings, World, []),
            case ArgValues of
                {Results, ArgBindings} ->
                    Function_Result = eval_function_body(
                        Function_Def, 
                        Results,
                        ArgBindings,
                        World,
                        Local_World
                    ),
                    case Function_Result of
                        {ok, {'fun', FunTag}, FunBindings} ->
                            FunBody = orddict:fetch(FunTag, FunBindings),    
                            NewBindings = 
                                orddict:store(
                                    FunTag,
                                    FunBody,
                                    ArgBindings
                                ),
                            {ok, {'fun', FunTag}, NewBindings};
                        {ok, EvalVal, _} -> 
                            {ok, EvalVal, ArgBindings};
                        {yield, _Kont, _Out} ->
                            yield_todo;
                        _ ->
                            Function_Result
                    end;
                _ ->
                    ArgValues
            end;
        true ->
            {error, undef}
    end;
eval_call(_, _, _, _, _) -> {error, undef}.

% Evaluate each argument in order and return the list of results
% and the Bindings obtained.
eval_args(Args, Bindings, _World, Results) when Args == [] ->
    {lists:reverse(Results), Bindings}; 
eval_args(Args, Bindings, World, Results) when Args /= [] ->
    case eval_expr(hd(Args), Bindings, World) of
        {ok, Result, NextBindings} -> 
            eval_args(tl(Args), NextBindings, World, [Result | Results]);
        {yield, _Kont, _Out} ->
            yield_todo;
        {error, Exception} -> 
            {error, Exception}
    end.

% Checks if there is a matching function clause with valid guards, then 
% evaluates the body.
eval_function_body([], _, _, _, _) -> {error, function_clause};
eval_function_body([HdClause | Rest], Args, Bindings, World, LocalWorld) ->
    {clause, _Line, Param, GuardsList, Body} = HdClause,
    LocalBindings = create_local_bindings(Param, Args, Bindings, [], World),
    case LocalBindings of
        false ->
            eval_function_body(Rest, Args, Bindings, World, LocalWorld);
        _ ->
            case GuardsList of
                [Guards] ->
                    GuardsResult = eval_guards(
                                    Guards,
                                    LocalBindings,
                                    world:world_init()
                                ),
                    case GuardsResult of
                        true ->
                            eval_exprs(Body, LocalBindings, LocalWorld);
                        _ ->
                            eval_function_body(
                                Rest,
                                Args,
                                Bindings,
                                World,
                                LocalWorld
                            )
                    end;
                _ ->
                    eval_exprs(Body, LocalBindings, LocalWorld)
            end
    end.

% Given a list of paramteres and arguments, match each parameter to the
% corresponidng argumnt and return the new bindings created by the match.
create_local_bindings([], [], _, BindingsAcc, _) -> BindingsAcc;
create_local_bindings(Param, Args, Bindings, BindingsAcc, World)
        when length(Param) == length(Args) ->
    TryMatch = match:eval_param_match_rhs_value(hd(Param), hd(Args), Bindings, [], World),
    case TryMatch of
        {error, _} ->
            false;
        _ ->
            NewBindings =
                orddict:merge(
                    fun(_, V, _) -> V end,
                    BindingsAcc,
                    TryMatch
                ),
            create_local_bindings(
                tl(Param),
                tl(Args),
                Bindings,
                NewBindings,
                World)
    end;
create_local_bindings(_, _, _, _, _) -> false.
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates a fun statement by generating a unique name and the {name, arity} 
% pair as a key for the given clauses in the Bindings. Returns the generated name
% which has a 'fun' type.
eval_fun(Clauses, Line, Bindings, _) ->
    FunName = list_to_atom("#Fun<" ++ integer_to_list(Line) ++ "."++ integer_to_list(erlang:unique_integer([positive])) ++ ">"),
    [{clause, _, ArgList, _, _} | _] = Clauses,
    FunArity = length(ArgList),
    {ok, {'fun', {FunName, FunArity}}, orddict:store({FunName, FunArity}, {{clauses, Clauses}, Bindings}, Bindings)}.

% Checks if there is a matching function clause with valid guards, then 
% evaluates the body. BodyBindings are 
eval_fun_body([], _, _, _, _, _) -> {error, function_clause};
eval_fun_body([HdClause | TlClauses], Args, Bindings, BodyBindings, World, LocalWorld) ->
    {clause, _, Param_List, _, _} = HdClause,
    LocalBindings = create_local_bindings_fun(Param_List, Args, Bindings, BodyBindings, World),
    case {HdClause, LocalBindings} of
        {_, false} -> 
            eval_fun_body(TlClauses, Args, Bindings, BodyBindings, World, LocalWorld);
        {{clause, _, _, [], Exprs}, _} ->
            eval_exprs(Exprs, LocalBindings, LocalWorld);
        {{clause, _, _, [Guards], Exprs}, _} ->
            Guards_Result = eval_guards(Guards, LocalBindings, world:world_init()),
            case Guards_Result of
                true ->
                    eval_exprs(Exprs, LocalBindings, LocalWorld);
                _ ->
                    eval_fun_body(TlClauses, Args, Bindings, BodyBindings, World, LocalWorld)
            end;
        _ -> {error, "The function guards are invalid."}
    end.

% Given a list of paramteres and arguments, match each parameter to the 
% corresponidng binding and return the new bindings created by the match.
create_local_bindings_fun([], [], _, BindingsAcc, _) -> BindingsAcc;
create_local_bindings_fun(Param, Args, Bindings, BindingsAcc, World) when length(Param) == length(Args) ->
    TryMatch = match:param_match(hd(Param), hd(Args), Bindings, [], World),
    case TryMatch of
        {error, _} -> false;
        _ ->
            NewBindings = orddict:merge(fun(_, V, _) -> V end, BindingsAcc, TryMatch),
            create_local_bindings_fun(tl(Param), tl(Args), Bindings, NewBindings, World)
    end;
create_local_bindings_fun(_, _, _, _, _) -> false.

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