-module(functions).
-export([eval_calls/7, create_local_bindings/6]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Determine the type of call in the expression and call the appropriate helper
eval_calls(Call, Line, Args, Bindings, OutBox, ProcState, World) ->
    EvalArgs = eval_args(Args, Line, Bindings, OutBox, ProcState, World),
    case EvalArgs of
        {arg_yield, Receive, Kont, Out} ->
            {yield, Receive, {call, Call, Kont}, Out};
        {arg_ok, Results, ArgBindings, ArgOutBox} ->
            case Call of
                {atom, _Line, FName} ->
                    eval_local_call(
                        FName,
                        Results,
                        ArgBindings,
                        ArgOutBox,
                        ProcState,
                        World
                    );
                {remote, _Line, {atom, _MLn, MName}, {atom, _FLn, FName}} ->
                    eval_remote_call(
                        MName,
                        FName, 
                        Results,
                        ArgBindings,
                        ArgOutBox,
                        ProcState,
                        World
                    );
                _ ->
                    funs:eval_fun_call(Call, Results, ArgBindings, ArgOutBox, ProcState, World)
            end;
        _ ->
            EvalArgs
    end.

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
% TODO: so args can create bindings, but cannot use them right away
% invariant: Kont is list of bindings
eval_args(Args, _Line, Bindings, OutBox, _ProcState, _World) when Args == [] ->
    {arg_ok, [], Bindings, OutBox};
eval_args(Args, Line, Bindings, OutBox, ProcState, World) ->
    EvalHead = eval:eval_expr(hd(Args), Bindings, OutBox, ProcState, World),
    case EvalHead of
        {ok, HeadResult, HeadBindings, HeadOutBox} ->
            EvalTail = eval_args(tl(Args), Line, Bindings, HeadOutBox, ProcState, World),
            case EvalTail of
                {arg_ok, TailResults, TailBindings, TailOutBox} ->
                    NewBindings =
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            HeadBindings,
                            TailBindings
                        ),
                    {arg_ok, [HeadResult | TailResults], NewBindings, TailOutBox};
                {arg_yield, Receive, Kont, Out} ->
                    KontArgs = [eval:value_to_AST(HeadResult, Line) | Kont],
                    {arg_yield, Receive, KontArgs, Out};
                _ ->
                    EvalTail
            end;
        {yield, Receive, Kont, Out} ->
            {arg_yield, Receive, [Kont], Out};
        _ ->
            EvalHead
    end.


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
eval_local_call(FName, Args, Bindings, OutBox, ProcState, World) ->
    case FName of
        is_atom when length(Args) == 1 ->
            case Args of
                [{atom, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_boolean when length(Args) == 1 ->
            case Args of
                [{atom, Val}] when Val == true orelse Val == false ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_float when length(Args) == 1 ->
            case Args of
                [{float, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_function when length(Args) == 1 ->
            case Args of
                [{'fun', _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_function when length(Args) == 2 ->
            case Args of
                [{'fun', {_, Arity}}, {integer, Arity}] 
                    when is_integer(Arity) ->
                    {ok, {atom, true}, Bindings, OutBox};
                [{'fun', {_, Arity}}, {integer, Arity}] ->
                    {error, badarg, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_integer when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_list when length(Args) == 1 ->
            case Args of
                [{cons, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                [{nil, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end; 
        is_number when length(Args) == 1 ->
            case Args of
                [{integer, _}] ->
                   {ok, {atom, true}, Bindings, OutBox};
                [{float, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end; 
        is_pid when length(Args) == 1 ->
            case Args of
                [{pid, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        is_tuple when length(Args) == 1 ->
            case Args of
                [{tuple, _}] ->
                    {ok, {atom, true}, Bindings, OutBox};
                _ ->
                    {ok, {atom, false}, Bindings, OutBox}
            end;
        abs when length(Args) == 1 ->
            case Args of
                [{integer, Val}] ->
                    {ok, {integer, abs(Val)}, Bindings, OutBox};
                [{float, Val}] ->
                    {ok, {float, abs(Val)}, Bindings, OutBox};
                _ ->
                    {error, badarg, OutBox}
            end;
        element when length(Args) == 2 ->
            case Args of
                [{integer, N}, {tuple, Tuple}] when N > 0 ->
                    {ok, element(N, list_to_tuple(Tuple)), Bindings, OutBox};
                _ ->
                    {error, badarg, OutBox}
            end;
        hd when length(Args) == 1 ->
            case Args of 
                [{cons, List}] ->
                    {ok, hd(List), Bindings, OutBox};
                _ ->
                    {error, badarg, OutBox}
            end;
        length when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    {ok, {integer, length(List)}, Bindings, OutBox};
                [{nil, _}] ->
                    {ok, {integer, 0}, Bindings, OutBox};
                _ ->
                    {error, badarg, OutBox}
            end;
        max when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A >= B ->
                           {ok, {TypeA, A}, Bindings, OutBox};
                        true ->
                            {ok, {TypeB, B}, Bindings, OutBox}
                    end;
                _ ->
                    {error, badarg, OutBox}
            end; 
        min when length(Args) == 2 ->
            case Args of
                [{TypeA, A}, {TypeB, B}] ->
                    if
                        A =< B ->
                           {ok, {TypeA, A}, Bindings, OutBox};
                        true ->
                            {ok, {TypeB, B}, Bindings, OutBox}
                    end;
                _ ->
                    {error, badarg, OutBox}
            end; 
        tl when length(Args) == 1 ->
            case Args of
                [{cons, List}] ->
                    {ok, {cons, tl(List)}, Bindings, OutBox};
                _ ->
                    {error, badarg, OutBox}
            end;
        _ ->
            eval_remote_call(maps:get(module, ProcState), FName, Args, Bindings, OutBox, ProcState, World)
    end.