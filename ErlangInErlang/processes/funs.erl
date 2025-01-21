-module(funs).
-export([eval_fun/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a fun statement by generating a unique name and mapping the name to
% to the fun's clauses in the Bindings.
eval_fun(Clauses, Line, Bindings, World, K) ->
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
    cps:applyK({'fun', {FunName, FunArity}}, NewBindings, World, K).

% % Evaluate a call to a fun. Throw badfun error if the called expression
% % does not evaluate to a fun.
% eval_fun_call(CallExpr, Args, Bindings, World) ->
%     FunExpr = eval:eval_expr(CallExpr, Bindings, World),
%     case FunExpr of
%         {ok, {'fun', {Name, Arity}}, CallBindings} ->
%             {{clauses, Clauses}, FunBindings} = 
%                 orddict:fetch(
%                     {Name, Arity},
%                     CallBindings
%                 ),
%                 if 
%                     Arity == length(Args) ->
%                         FunResult = eval_fun_body(
%                             Clauses, 
%                             Args,
%                             FunBindings,
%                             World
%                         ),
%                         case FunResult of
%                             {ok, {'fun', FunTag}, ResultBindings} ->
%                                 FunBody = 
%                                     orddict:fetch(
%                                         FunTag,
%                                         ResultBindings
%                                     ),    
%                                 NewBindings = 
%                                     orddict:store(
%                                         FunTag,
%                                         FunBody,
%                                         CallBindings
%                                     ),
%                                 {ok, {'fun', FunTag}, NewBindings};
%                             {ok, EvalVal, _} -> 
%                                 {ok, EvalVal, CallBindings};
%                             {yield, _Kont, _Out} ->
%                                 yield_todo;
%                             _ ->
%                                 FunResult
%                         end;
%                     true ->
%                         F = {'fun', {Name, Arity}},
%                         {error, {badarity, {F, Args}}}
%                 end;
%         {ok, F, _} ->
%             {error, {badfun, F}};
%         {yield, _Kont, _Out} ->
%             yield_todo;
%         _ -> 
%             FunExpr
%     end.

% % Create the proper bindings and evaluate the fun's body.
% eval_fun_body([], _, _, _) -> {error, function_clause};
% eval_fun_body([HdClause | Rest], Args, FunBindings, World) ->
%     {clause, _Line, Param, GuardsList, Body} = HdClause,
%     LocalBindings = 
%         functions:create_local_bindings(
%             Param,
%             Args,
%             FunBindings,
%             [],
%             World
%         ),
%     case LocalBindings of
%         false ->
%             eval_fun_body(Rest, Args, FunBindings, World);
%         _ ->
%             BodyBindings =
%                         orddict:merge(
%                             fun(_, V, _) -> V end,
%                             LocalBindings,
%                             FunBindings
%                         ),
%             case GuardsList of
%                 [Guards] ->
%                     GuardsResult = cases:eval_guards(
%                                     Guards,
%                                     BodyBindings,
%                                     world:world_init()
%                                 ),
%                     case GuardsResult of
%                         true ->
%                             eval:eval_exprs(Body, BodyBindings, World);
%                         _ ->
%                             eval_fun_body(
%                                 Rest,
%                                 Args,
%                                 FunBindings,
%                                 World
%                             )
%                     end;
%                 _ ->
%                     eval:eval_exprs(Body, BodyBindings, World)
%             end
%     end.
