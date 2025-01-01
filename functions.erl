-module(functions).
-export([eval_local_call/4, eval_call/5, eval_args/4,
    eval_function_body/5, create_local_bindings/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate local function calls
eval_local_call(Fname, Args, Bindings, World) ->
    case Fname of
        is_atom ->
            EvalArg = eval_args(Args, Bindings, World, []),
            case EvalArg of
                {[{Type, _}], ArgBindings} ->
                    {ok, {atom, Type == atom}, ArgBindings};
                {_Results, _ArgBindings} ->
                    {error, undef};
                _ ->
                    EvalArg
            end;
        _ ->
            eval_call(local, Fname, Args, Bindings, World)
    end.

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
    end.

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
                    GuardsResult = cases:eval_guards(
                                    Guards,
                                    LocalBindings,
                                    world:world_init()
                                ),
                    case GuardsResult of
                        true ->
                            eval:eval_exprs(Body, LocalBindings, LocalWorld);
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
                    eval:eval_exprs(Body, LocalBindings, LocalWorld)
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