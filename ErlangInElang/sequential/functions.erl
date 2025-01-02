-module(functions).
-export([eval_calls/4, create_local_bindings/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Determine the type of call in the expression and call the appropriate helper
eval_calls(Call, Args, Bindings, World) ->
    EvalArgs = eval_args(Args, Bindings, World, []),
    case EvalArgs of
        {Results, ArgBindings} ->
            case Call of
                {atom, _Line, FName} ->
                    eval_local_call(
                        FName,
                        Results,
                        ArgBindings,
                        World
                    );
                {remote, _Line, {atom, _MLn, MName}, {atom, _FLn, FName}} ->
                    eval_remote_call(
                        MName,
                        FName, 
                        Results,
                        ArgBindings,
                        World
                    );
                _ ->
                    funs:eval_fun_call(Call, Results, ArgBindings, World)
            end;
        {yield, _Kont, _Out} ->
            yield_todo;
        _ ->
            EvalArgs
    end.

% Evaluate remote function calls
eval_remote_call(ModuleName, FunctionName, Args, Bindings, World) 
        when is_map_key(ModuleName, World) ->
    Module = maps:get(ModuleName, World),
    Arity = length(Args),
    if
        is_map_key({FunctionName, Arity}, Module) ->
            Function_Def = maps:get({FunctionName, Arity}, Module),
            LocalWorld = world:world_add_module(World, local, Module),
            FunctionResult = eval_function_body(
                Function_Def, 
                Args,
                Bindings,
                LocalWorld
            ),
            case FunctionResult of
                {ok, {'fun', FunTag}, FunBindings} ->
                    FunBody = orddict:fetch(FunTag, FunBindings),    
                    NewBindings = 
                        orddict:store(
                            FunTag,
                            FunBody,
                            Bindings
                        ),
                    {ok, {'fun', FunTag}, NewBindings};
                {ok, EvalVal, _} -> 
                    {ok, EvalVal, Bindings};
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ ->
                    FunctionResult
            end;
        true ->
            {error, undef}
    end;
eval_remote_call(_, _, _, _, _) -> {error, undef}.

% Evaluate each argument in order and return the list of results
% and the Bindings obtained.
eval_args(Args, Bindings, _World, Results) when Args == [] ->
    {lists:reverse(Results), Bindings}; 
eval_args(Args, Bindings, World, Results) when Args /= [] ->
    case eval:eval_expr(hd(Args), Bindings, World) of
        {ok, Result, NextBindings} -> 
            eval_args(tl(Args), NextBindings, World, [Result | Results]);
        {yield, _Kont, _Out} ->
            yield_todo;
        {error, Exception} -> 
            {error, Exception}
    end.

% Checks if there is a matching function clause with valid guards, then 
% evaluates the body.
eval_function_body([], _, _, _) -> {error, function_clause};
eval_function_body([HdClause | Rest], Args, Bindings, World) ->
    {clause, _Line, Param, GuardsList, Body} = HdClause,
    LocalBindings = create_local_bindings(Param, Args, Bindings, [], World),
    case LocalBindings of
        false ->
            eval_function_body(Rest, Args, Bindings, World);
        _ ->
            case GuardsList of
                [Guards] ->
                    GuardsResult = cases:eval_guards(
                                    Guards,
                                    LocalBindings,
                                    world:world_init()
                                ),
                    case GuardsResult of
                        true ->
                            eval:eval_exprs(Body, LocalBindings, World);
                        _ ->
                            eval_function_body(
                                Rest,
                                Args,
                                Bindings,
                                World
                            )
                    end;
                _ ->
                    eval:eval_exprs(Body, LocalBindings, World)
            end
    end.

% Given a list of paramteres and arguments, match each parameter to the
% corresponidng argumnt and return the new bindings created by the match.
create_local_bindings([], [], _, BindingsAcc, _) -> BindingsAcc;
create_local_bindings(Param, Args, Bindings, BindingsAcc, World)
        when length(Param) == length(Args) ->
    TryMatch = 
        match:eval_param_match(
            hd(Param),
            hd(Args),
            [],
            World
        ),
    MatchedBindings = 
        case hd(Args) of
            {'fun', FunTag} ->
                FunBody = orddict:fetch(FunTag, Bindings),
                orddict:store(FunTag, FunBody, TryMatch);
            _ ->
                TryMatch
        end,
    case MatchedBindings of
        {error, {badmatch, _}} ->
            false;
        _ ->
            NewBindings =
                orddict:merge(
                    fun(_, V, _) -> V end,
                    BindingsAcc,
                    MatchedBindings
                ),
            create_local_bindings(
                tl(Param),
                tl(Args),
                Bindings,
                NewBindings,
                World)
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Calls within the same module and BIFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate local function calls
eval_local_call(FName, Args, Bindings, World) ->
    case FName of
        is_atom when length(Args) == 1 ->
            case Args of
                [{atom, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_boolean when length(Args) == 1 ->
            case Args of
                [{atom, Val}] when Val == true orelse Val == false ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_float when length(Args) == 1 ->
            case Args of
                [{float, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_function when length(Args) == 1 ->
            case Args of
                [{'fun', _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_function when length(Args) == 2 ->
            case Args of
                [{'fun', {_, Arity}}, {integer, Arity}] 
                    when is_integer(Arity) ->
                    {ok, {atom, true}, Bindings};
                [{'fun', {_, Arity}}, {integer, Arity}] ->
                    {error, badarg};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_integer when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_list when length(Args) == 1 ->
            case Args of
                [{cons, _}] ->
                    {ok, {atom, true}, Bindings};
                [{nil, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end; 
        is_number when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                   {ok, {atom, true}, Bindings};
                [{float, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end; 
        is_pid when length(Args) == 1 ->
            case Args of
                [{pid, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        is_tuple when length(Args) == 1 ->
            case Args of
                [{tuple, _}] ->
                    {ok, {atom, true}, Bindings};
                _ ->
                    {ok, {atom, false}, Bindings}
            end;
        abs when length(Args) == 1 ->
            case Args of
                [{integer, Val}] ->
                    {ok, {integer, abs(Val)}, Bindings};
                [{float, Val}] ->
                    {ok, {float, abs(Val)}, Bindings};
                _ ->
                    {error, badarg}
            end;
        element when length(Args) == 2 ->
            case Args of
                [{integer, N}, {tuple, Tuple}] when N > 0 ->
                    {ok, element(N, list_to_tuple(Tuple)), Bindings};
                _ ->
                    {error, badarg}
            end;
        hd when length(Args) == 1 ->
            case Args of 
                [{cons, List}] ->
                    {ok, hd(List), Bindings};
                _ ->
                    {error, badarg}
            end;
        length when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    {ok, {integer, length(List)}, Bindings};
                [{nil, _}] ->
                    {ok, {integer, 0}, Bindings};
                _ ->
                    {error, badarg}
            end;
        max when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A >= B ->
                           {ok, {TypeA, A}, Bindings};
                        true ->
                            {ok, {TypeB, B}, Bindings}
                    end;
                _ ->
                    {error, badarg}
            end; 
        min when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A =< B ->
                           {ok, {TypeA, A}, Bindings};
                        true ->
                            {ok, {TypeB, B}, Bindings}
                    end;
                _ ->
                    {error, badarg}
            end; 
        tl when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    {ok, {cons, tl(List)}, Bindings};
                _ ->
                    {error, badarg}
            end;
        _ ->
            eval_remote_call('local', FName, Args, Bindings, World)
    end.