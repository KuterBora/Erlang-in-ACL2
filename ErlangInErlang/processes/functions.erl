-module(functions).
-export([eval_calls/7, eval_local_call/7, eval_remote_call/8]).
-export([create_local_bindings/8, eval_function_body/7]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Determine the type of call in the expression and call the appropriate helper
eval_calls(Call, Args, Bindings, Out, ProcState, World, K) ->
    eval_args(
        Args,
        Bindings,
        Out,
        ProcState,
        World,
        {call_k, Call, Bindings, K}
    ).

% Evaluate each argument in order and return the list of results
% and the Bindings obtained.
eval_args(Args, Bindings, Out, ProcState, World, K) when Args == [] ->
    cps:applyK([], Bindings, Out, ProcState, World, K);
eval_args(Args, Bindings, Out, ProcState, World, K) ->
    eval:eval_expr(
        hd(Args),
        Bindings,
        Out,
        ProcState,
        World,
        {arg_next_k, [], Bindings, Bindings, tl(Args), K}
    ).


% Given a list of paramteres and arguments, match each parameter to the
% corresponidng argumnt and return the new bindings created by the match.
% Remark: Bind0 is used to aquire fun bodies.
% TODO: parameters have to be patterns. No calls or funs.
create_local_bindings([], [], _, BindAcc, Out, ProcState, World, K) -> 
    cps:applyK(
        {atom, bindings},
        BindAcc,
        Out,
        ProcState,
        World,
        K
    );
create_local_bindings(Param, Args, Bind0, BindAcc, Out, ProcState, World, K) 
        when length(Param) == length(Args) ->
    match:eval_match(
        hd(Param),
        hd(Args),
        BindAcc,
        Out,
        ProcState,    
        World,
        {create_lb_k, tl(Param), tl(Args), Bind0, K}        
    ).

% Evaluate remote function calls
eval_remote_call(ModName, FuncName, Args, Bindings, Out, ProcState, World, K)
        when is_map_key(ModName, World) ->
    Module = maps:get(ModName, World),
    Arity = length(Args),
    case is_map_key({FuncName, Arity}, Module) of
        true ->
            FuncDef = maps:get({FuncName, Arity}, Module),
            FuncProcState = ProcState#{module => ModName}, 
            eval_function_body(
                FuncDef, 
                Args,
                Bindings,
                Out,
                FuncProcState,
                World,
                {remote_call_k, Bindings, ProcState, K}
            );
        _ ->
            cps:errorK(undef, Out, World, ProcState, K)
    end;
eval_remote_call(_, _, _, _, Out, ProcState, World, K) -> 
    cps:errorK(undef, Out, World, ProcState, K).


% Checks if there is a matching function clause with valid guards, then 
% evaluates the body.
eval_function_body([], _, _, Out, ProcState, World, K) ->
    cps:errorK(function_clause, Out, ProcState, World, K);
eval_function_body([HdCl | TlCls], Args, Bind0, Out, ProcState, World, K) ->
     {clause, _, Param, GList, Body} = HdCl,
     create_local_bindings(
        Param,
        Args,
        Bind0,
        [],
        Out,
        ProcState,
        World,
        {func_body_k, Body, GList, TlCls, Args, Bind0, K}).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Calls within the same module and BIFs
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate local function calls
eval_local_call(FName, Args, Bindings, Out, ProcState, World, K) ->
    case FName of
        is_atom when length(Args) == 1 ->
            case Args of
                [{atom, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK({atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        is_boolean when length(Args) == 1 ->
            case Args of
                [{atom, Val}] when Val == true orelse Val == false ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        is_function when length(Args) == 1 ->
            case Args of
                [{'fun', _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState, 
                        World,
                        K
                    )
            end;
        is_function when length(Args) == 2 ->
            case Args of
                [{'fun', {_, Arity}}, {integer, Arity}] 
                    when is_integer(Arity) ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                [{'fun', {_, Arity}}, {integer, Arity}] ->
                    cps:errorK(badarg, Out, ProcState, World, K);
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        is_integer when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        is_list when length(Args) == 1 ->
            case Args of
                [{cons, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                [{nil, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end; 
        is_number when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end; 
        is_pid when length(Args) == 1 ->
            case Args of
                [{pid, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        is_tuple when length(Args) == 1 ->
            case Args of
                [{tuple, _}] ->
                    cps:applyK(
                        {atom, true},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:applyK(
                        {atom, false},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        abs when length(Args) == 1 ->
            case Args of
                [{integer, Val}] ->
                    cps:applyK(
                        {integer, abs(Val)},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end;
        element when length(Args) == 2 ->
            case Args of
                [{integer, N}, {tuple, Tuple}] when N > 0 ->
                    cps:applyK(
                        element(N, list_to_tuple(Tuple)),
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end;
        hd when length(Args) == 1 ->
            case Args of 
                [{cons, List}] ->
                    cps:applyK(
                        hd(List),
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end;
        length when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    cps:applyK(
                        {integer, length(List)},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                [{nil, _}] ->
                    cps:applyK(
                        {integer, 0},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end;
        max when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A >= B ->
                            cps:applyK(
                                {TypeA, A},
                                Bindings,
                                Out,
                                ProcState,
                                World,
                                K
                            );
                        true ->
                            cps:applyK(
                                {TypeB, B},
                                Bindings,
                                Out,
                                ProcState,
                                World,
                                K
                            )
                    end;
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end; 
        min when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A =< B ->
                           cps:applyK(
                            {TypeA, A},
                            Bindings,
                            Out,
                            ProcState,
                            World,
                            K
                        );
                        true ->
                            cps:applyK(
                                {TypeB, B},
                                Bindings,
                                Out,
                                ProcState,
                                World,
                                K)
                    end;
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end; 
        tl when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    cps:applyK(
                        {cons, tl(List)},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    cps:errorK(badarg, Out, ProcState, World, K)
            end;
        _ ->
            eval_remote_call(
                maps:get(module, ProcState),
                FName,
                Args,
                Bindings,
                Out,
                ProcState,
                World,
                K
            )
    end.