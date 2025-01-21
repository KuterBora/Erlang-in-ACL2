-module(functions).
-export([eval_calls/5, eval_local_call/5, create_local_bindings/6]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Determine the type of call in the expression and call the appropriate helper
eval_calls(Call, Args, Bindings, World, K) ->
    eval_args(
        Args,
        Bindings,
        World,
        {call_k, Call, Bindings, K}).

% Evaluate remote function calls
eval_remote_call(ModuleName, FunctionName, Args, Bindings, OutBox, ProcState, World) 
        when is_map_key(ModuleName, World) ->
    Module = maps:get(ModuleName, World),
    Arity = length(Args),
    if
        is_map_key({FunctionName, Arity}, Module) ->
            Function_Def = maps:get({FunctionName, Arity}, Module),
            LocalProcState = ProcState#{module => ModuleName}, 
            FunctionResult = eval_function_body(
                Function_Def, 
                Args,
                Bindings,
                OutBox,
                LocalProcState,
                World
            ),
            case FunctionResult of
                {ok, {'fun', FunTag}, FunBindings, NewOutBox} ->
                    FunBody = orddict:fetch(FunTag, FunBindings),    
                    NewBindings = 
                        orddict:store(
                            FunTag,
                            FunBody,
                            Bindings
                        ),
                    {ok, {'fun', FunTag}, NewBindings, NewOutBox};
                {ok, EvalVal, _, NewOutBox} -> 
                    {ok, EvalVal, Bindings, NewOutBox};
                {yield, Receive, Kont, Out} ->
                    % need to save procstate
                    {yield, Receive, Kont, Out};
                _ ->
                    FunctionResult
            end;
        true ->
            {error, undef, OutBox}
    end;
eval_remote_call(_, _, _, _, OutBox, _, _) -> {error, undef, OutBox}.

% Evaluate each argument in order and return the list of results
% and the Bindings obtained.
eval_args(Args, Bindings, World, K) when Args == [] ->
    cps:applyK([], Bindings, World, K);
eval_args(Args, Bindings, World, K) ->
    eval:eval_expr(
        hd(Args),
        Bindings,
        World,
        {arg_next_k, [], Bindings, Bindings, tl(Args), K}).

% Checks if there is a matching function clause with valid guards, then 
% evaluates the body.
eval_function_body([], _, _, OutBox, _, _) -> {error, function_clause, OutBox};
eval_function_body([HdClause | Rest], Args, Bindings, OutBox, ProcState, World) ->
    {clause, _Line, Param, GuardsList, Body} = HdClause,
    % Remark: lhs cannot have receive or send, so no need to worry about OutBox
    LocalBindings = create_local_bindings(Param, Args, Bindings, [], ProcState, World),
    case LocalBindings of
        false ->
            eval_function_body(Rest, Args, Bindings, OutBox, ProcState, World);
        _ ->
            case GuardsList of
                [Guards] ->
                    GuardsResult = cases:eval_guards(
                                    Guards,
                                    LocalBindings,
                                    procs:empty_box(),
                                    ProcState,
                                    world:world_init()
                                ),
                    case GuardsResult of
                        true ->
                            eval:eval_exprs(Body, LocalBindings, OutBox, ProcState, World);
                        _ ->
                            eval_function_body(
                                Rest,
                                Args,
                                Bindings,
                                OutBox,
                                ProcState,
                                World
                            )
                    end;
                _ ->
                    eval:eval_exprs(Body, LocalBindings, OutBox, ProcState, World)
            end
    end.

% Given a list of paramteres and arguments, match each parameter to the
% corresponidng argumnt and return the new bindings created by the match.
create_local_bindings([], [], _, BindingsAcc, _, _) -> BindingsAcc;
create_local_bindings(Param, Args, Bindings, BindingsAcc, ProcState, World)
        when length(Param) == length(Args) ->
    TryMatch = 
        match:eval_param_match(
            hd(Param),
            hd(Args),
            [],
            ProcState,
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
        {error, {badmatch, _}, _} ->
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
                ProcState,
                World)
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Calls within the same module and BIFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate local function calls
eval_local_call(FName, Args, Bindings, World, K) ->
    case FName of
        is_atom when length(Args) == 1 ->
            case Args of
                [{atom, _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        is_boolean when length(Args) == 1 ->
            case Args of
                [{atom, Val}] when Val == true orelse Val == false ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        is_function when length(Args) == 1 ->
            case Args of
                [{'fun', _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        is_function when length(Args) == 2 ->
            case Args of
                [{'fun', {_, Arity}}, {integer, Arity}] 
                    when is_integer(Arity) ->
                    cps:applyK({atom, true}, Bindings, World, K);
                [{'fun', {_, Arity}}, {integer, Arity}] ->
                    cps:errorK(badarg, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        is_integer when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        is_list when length(Args) == 1 ->
            case Args of
                [{cons, _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                [{nil, _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end; 
        is_number when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                   cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end; 
        is_pid when length(Args) == 1 ->
            case Args of
                [{pid, _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        is_tuple when length(Args) == 1 ->
            case Args of
                [{tuple, _}] ->
                    cps:applyK({atom, true}, Bindings, World, K);
                _ ->
                    cps:applyK({atom, false}, Bindings, World, K)
            end;
        abs when length(Args) == 1 ->
            case Args of
                [{integer, Val}] ->
                    cps:applyK({integer, abs(Val)}, Bindings, World, K);
                _ ->
                    cps:errorK(badarg, World, K)
            end;
        element when length(Args) == 2 ->
            case Args of
                [{integer, N}, {tuple, Tuple}] when N > 0 ->
                    cps:applyK(element(N, list_to_tuple(Tuple)), Bindings, World, K);
                _ ->
                    cps:errorK(badarg, World, K)
            end;
        hd when length(Args) == 1 ->
            case Args of 
                [{cons, List}] ->
                    cps:applyK(hd(List), Bindings, World, K);
                _ ->
                    cps:errorK(badarg, World, K)
            end;
        length when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    cps:applyK({integer, length(List)}, Bindings, World, K);
                [{nil, _}] ->
                    cps:applyK({integer, 0}, Bindings, World, K);
                _ ->
                    cps:errorK(badarg, World, K)
            end;
        max when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A >= B ->
                           cps:applyK({TypeA, A}, Bindings, World, K);
                        true ->
                            cps:applyK({TypeB, B}, Bindings, World, K)
                    end;
                _ ->
                    cps:errorK(badarg, World, K)
            end; 
        min when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A =< B ->
                           cps:applyK({TypeA, A}, Bindings, World, K);
                        true ->
                            cps:applyK({TypeB, B}, Bindings, World, K)
                    end;
                _ ->
                    cps:errorK(badarg, World, K)
            end; 
        tl when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    cps:applyK({cons, tl(List)}, Bindings, World, K);
                _ ->
                    cps:errorK(badarg, World, K)
            end;
        _ ->
            % eval_remote_call(maps:get(module, ProcState), FName, Args, Bindings, OutBox, ProcState, World)
            todo
    end.