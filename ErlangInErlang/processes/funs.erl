-module(funs).
-export([eval_fun/5, eval_fun_call/6]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a fun statement by generating a unique name and mapping the name to
% to the fun's clauses in the Bindings. Returns the generated name.
eval_fun(Clauses, Line, Bindings, OutBox, ProcState) ->
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
            {{clauses, Clauses}, Bindings, ProcState},
            Bindings
        ),
    {ok, {'fun', {FunName, FunArity}}, NewBindings, OutBox}.

% Evaluate a call to a fun. Throw badfun error if the called expression
% does not evaluate to a fun.
% TODO: evaluate the CallExpr in functions:local_call
eval_fun_call(CallExpr, Args, Bindings, OutBox, ProcState, World) ->
    FunExpr = eval:eval_expr(CallExpr, Bindings, OutBox, ProcState, World),
    case FunExpr of
        {ok, {'fun', {Name, Arity}}, CallBindings, CallOutBox} ->
            {{clauses, Clauses}, FunBindings, FunProcState} = 
                orddict:fetch(
                    {Name, Arity},
                    CallBindings
                ),
                if 
                    Arity == length(Args) ->
                        FunResult = eval_fun_body(
                            Clauses, 
                            Args,
                            FunBindings,
                            CallOutBox,
                            FunProcState,
                            World
                        ),
                        case FunResult of
                            {ok, {'fun', FunTag}, ResultBindings, ResultOutBox} ->
                                FunBody = 
                                    orddict:fetch(
                                        FunTag,
                                        ResultBindings
                                    ),    
                                NewBindings = 
                                    orddict:store(
                                        FunTag,
                                        FunBody,
                                        CallBindings
                                    ),
                                {ok, {'fun', FunTag}, NewBindings, ResultOutBox};
                            {ok, EvalVal, _, Box} -> 
                                {ok, EvalVal, CallBindings, Box};
                            {yield, Receive, Kont, Out} ->
                                {yield, Receive, Kont, Out};
                            _ ->
                                FunResult
                        end;
                    true ->
                        F = {'fun', {Name, Arity}},
                        {error, {badarity, {F, Args}}, CallOutBox}
                end;
        {ok, F, _, Box} ->
            {error, {badfun, F}, Box};
        {yield, Receive, Kont, Out} ->
            
            {yield, Receive, {call, Line, }};
        _ -> 
            FunExpr
    end.

% Create the proper bindings and evaluate the fun's body.
eval_fun_body([], _, _, _, OutBox, _) -> {error, function_clause, OutBox};
eval_fun_body([HdClause | Rest], Args, FunBindings, OutBox, FunProcState, World) ->
    {clause, _Line, Param, GuardsList, Body} = HdClause,
    LocalBindings = 
        functions:create_local_bindings(
            Param,
            Args,
            FunBindings,
            [],
            FunProcState,
            World
        ),
    case LocalBindings of
        false ->
            eval_fun_body(Rest, Args, FunBindings, OutBox, FunProcState, World);
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
                                    FunProcState,
                                    world:world_init()
                                ),
                    case GuardsResult of
                        true ->
                            eval:eval_exprs(Body, BodyBindings, OutBox, FunProcState, World);
                        _ ->
                            eval_fun_body(
                                Rest,
                                Args,
                                OutBox,
                                FunBindings,
                                FunProcState,
                                World
                            )
                    end;
                _ ->
                    eval:eval_exprs(Body, BodyBindings, OutBox, FunProcState, World)
            end
    end.
