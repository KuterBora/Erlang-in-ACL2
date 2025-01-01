-module(funs).
-export([eval_fun/3, eval_fun_call/4, eval_fun_body/4]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a fun statement by generating a unique name and mapping the name to
% to the fun's clauses in the Bindings. Returns the generated name.
eval_fun(Clauses, Line, Bindings) ->
    FunName = 
        list_to_atom(
            "#Fun<" ++ 
            integer_to_list(Line) ++ 
            "." ++ 
            integer_to_list(erlang:unique_integer([positive])) ++ 
            ">"
        ),
    [{clause, _, ArgList, _, _} | _] = Clauses,
    FunArity = length(ArgList),
    NewBindings = 
        orddict:store(
            {FunName, FunArity},
            {{clauses, Clauses}, Bindings},
            Bindings
        ),
    {ok, {'fun', {FunName, FunArity}}, NewBindings}.

% Evaluate a call to a fun. Throw badfun error if the called expression
% does not evaluate to a fun.
eval_fun_call(CallExpr, Args, Bindings, World) ->
    FunExpr = eval:eval_expr(CallExpr, Bindings, World),
    case FunExpr of
        {ok, {'fun', {Name, Arity}}, CallBindings} ->
            {{clauses, Clauses}, FunBindings} = 
                orddict:fetch(
                    {Name, Arity},
                    CallBindings
                ),
            ArgValues = functions:eval_args(Args, CallBindings, World, []),
            case ArgValues of
                {Results, ArgBindings} ->
                    if 
                        Arity == length(Args) ->
                            FunResult = eval_fun_body(
                                Clauses, 
                                Results,
                                FunBindings,
                                World
                            ),
                            case FunResult of
                                {ok, {'fun', FunTag}, ResultBindings} ->
                                    FunBody = 
                                        orddict:fetch(
                                            FunTag,
                                            ResultBindings
                                        ),    
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
                                    FunResult
                            end;
                        true ->
                            F = {'fun', {Name, Arity}},
                            {error, {badarity, {F, ArgValues}}}
                    end;
                _ ->
                    ArgValues
            end;
        {ok, F, _} ->
            {error, {badfun, F}};
        {yield, _Kont, _Out} ->
            yield_todo;
        _ -> 
            FunExpr
    end.

% Create the proper bindings and evaluate the fun's body.
eval_fun_body([], _, _, _) -> {error, function_clause};
eval_fun_body([HdClause | Rest], Args, FunBindings, World) ->
    {clause, _Line, Param, GuardsList, Body} = HdClause,
    LocalBindings = 
        functions:create_local_bindings(
            Param,
            Args,
            FunBindings,
            [],
            World
        ),
    case LocalBindings of
        false ->
            eval_fun_body(Rest, Args, FunBindings, World);
        _ ->
            BodyBindings =
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            LocalBindings,
                            FunBindings
                        ),
            case GuardsList of
                [Guards] ->
                    GuardsResult = cases:eval_guards(
                                    Guards,
                                    BodyBindings,
                                    world:world_init()
                                ),
                    case GuardsResult of
                        true ->
                            eval:eval_exprs(Body, BodyBindings, World);
                        _ ->
                            eval_fun_body(
                                Rest,
                                Args,
                                FunBindings,
                                World
                            )
                    end;
                _ ->
                    eval:eval_exprs(Body, BodyBindings, World)
            end
    end.
