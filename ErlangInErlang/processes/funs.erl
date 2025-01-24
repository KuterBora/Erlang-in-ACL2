-module(funs).
-export([eval_fun/7, eval_fun_call/8, eval_fun_body/7]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a fun statement by generating a unique name and mapping the name to
% to the fun's clauses in the Bindings.
eval_fun(Clauses, Line, Bindings, Out, ProcState, World, K) ->
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
    cps:applyK(
        {'fun', {FunName, FunArity}},
        NewBindings,
        Out,
        ProcState,
        World,
        K
    ).

% % Evaluate a call to a fun. Throw badfun error if the called expression
% % does not evaluate to a fun.
eval_fun_call(CallExpr, Args, Bind0, ArgBind, Out, ProcState, World, K) ->
    eval:eval_expr(
        CallExpr,
        Bind0,
        Out,
        ProcState,
        World,
        {fun_call_k, Args, ArgBind, K}
    ).

% Create the proper bindings and evaluate the fun's body.
eval_fun_body([], _, _, Out, ProcState, World, K) ->
    cps:errorK(function_clause, Out, ProcState, World, K);
eval_fun_body([HdCl | TlCls], Args, FunBind, Out, ProcState, World, K) ->
    {clause, _, Param, GList, Body} = HdCl,
    functions:create_local_bindings(
        Param,
        Args,
        FunBind,
        [],
        Out,
        ProcState,
        World,
        {fun_body_k, Body, GList, TlCls, Args, FunBind, K}  
    ).