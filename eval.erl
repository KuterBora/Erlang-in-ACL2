-module(eval).
-export([eval_exprs/3, eval_expr/3, eval_string/2, eval_world/3]).
-export([get_AST/1, get_AST_form/1]).
-export([module_add_function_string/4, world_add_module/3]).


% TODO:
% Core
% functions with guards
% handle multiple function clauses with guards
% - should allow recursive functions

% Time Allows
% test the error handling
% built in guard functions
% test/eval pattern matching
% modify world_add_module to load from an existing erlang file
%   and handle the Module Map creation automaticalls.

% Utility
% add sets , and document changes
% better function commentary
% add guards and type checking to the evaluator


% Evaluates ASTs with given Bidnings by calling each AST
% linearly and passing the resulting Bindings to the
% next AST.
% - ASTs is the list of trees returned by erl:parse_exprs.
% - Binding is a dictionary in the form [{'<key>', <val>}, ...].
% - World is TODO
% Returns {ok, Value, NewBindings} | {error, Message}
eval_exprs(ASTs, Bindings, World) when tl(ASTs) == [] ->
    eval_expr(hd(ASTs), Bindings, World);
eval_exprs(ASTs, Bindings, World) ->
    Eval = eval_expr(hd(ASTs), Bindings, World),
    case Eval of
        {ok, _, NextBindings} -> 
            eval_exprs(tl(ASTs), NextBindings, World);
        {error, Message} ->
            {error, Message}
    end.

% Evaluates the given AST with the given Bidnings.
% - AST is a single one of the trees returned by erl:parse_exprs
% - Binding is dictionary in form [{'<key>', <val>}, ...]
% - World is TODO
% Returns {ok, Value, NewBindings} | {error, Message}
eval_expr(AST, Bindings, World) ->
    case AST of
        % atoms
        {atom, _, Atom} -> {ok, Atom, Bindings}; 
        % integers
        {integer, _, Val} when is_integer(Val) -> {ok, Val, Bindings};
        % negtive integers/sign change
        {op, _, '-', Expr} -> 
            {ok, Val, _} = eval_expr(Expr, Bindings, World),
            {ok, -Val, Bindings};
        % strings
        {string, _, String} -> {ok, String, Bindings};
        % nil
        {nil, _} -> {ok, [], Bindings};
        % lists
        {cons, _, Car, Cdr} ->
            {ok, Head, _} = eval_expr(Car, Bindings, World),
            {ok, Tail, _} = eval_expr(Cdr, Bindings, World),
            {ok, [Head | Tail], Bindings};
        % variables
        {var, _, Var} -> {ok, orddict:fetch(Var, Bindings), Bindings};
        % macthes
        {match, _, Exp1, Exp2} -> eval_match(Exp1, Exp2, Bindings, World);
        % operations
        {op, _, Op, Exp1, Exp2} -> eval_op(Op, Exp1, Exp2, Bindings, World);
        % if
        {'if', _, Clasues} -> eval_if(Clasues, Bindings, World);
        % local calls
        {call, _, {atom, _, Function_Name}, Param_Values} -> 
            eval_call(local, Function_Name, Param_Values, Bindings, World);
        % remote calls
        {call, _, {remote, _, {atom, _, Module_Name}, {atom, _, Function_Name} }, Param_Values} -> 
            eval_call(Module_Name, Function_Name, Param_Values, Bindings, World);
        % unrecognized language
        _ -> {error, "Language in the AST is not recognized by the evaluator."}
    end.

% Given an Operation, Bindings and two expressions as ASTs,
% evaluate the AST expressions and apply the given operation.
% Exp1 and Exp2 are not associative, Exp1 must be used first.
eval_op(Op, Exp1, Exp2, Bindings, World) ->
    {ok, Operand1, _} = eval_expr(Exp1, Bindings, World),
    {ok, Operand2, _} = eval_expr(Exp2, Bindings, World),
    case Op of
        '+' when is_integer(Operand1), is_integer(Operand2) ->
            {ok, Operand1 + Operand2, Bindings};
        '-' when is_integer(Operand1), is_integer(Operand2) ->
            {ok, Operand1 - Operand2, Bindings};
        '*' when is_integer(Operand1), is_integer(Operand2) ->
            {ok, Operand1 * Operand2, Bindings};
        'div' when is_integer(Operand1), is_integer(Operand2) ->
            {ok, Operand1 div Operand2, Bindings};
        '++' when is_list(Operand1), is_list(Operand2) ->
            {ok, Operand1 ++ Operand2, Bindings};
        '|' when is_list(Operand2) ->
            [Operand1 | Operand2];
        '==' -> {ok, Operand1 == Operand2, Bindings};
        '/=' -> {ok, Operand1 /= Operand2, Bindings};
        '<' -> {ok, Operand1 < Operand2, Bindings};
        '=<' -> {ok, Operand1 < Operand2, Bindings};
        '>' -> {ok, Operand1 > Operand2, Bindings};
        '>=' -> {ok, Operand1 < Operand2, Bindings};
        'and' when is_atom(Operand1), is_atom(Operand2) ->
            {ok, Operand1 and Operand2, Bindings};
        'or' when is_atom(Operand1), is_atom(Operand2) ->
            {ok, Operand1 or Operand2, Bindings};
        _ -> {error, "Operation with given arguments is not recognized by the evaluator."}
    end.

% Given a match statement, if the left hand side is an unbound
% variable, assigns the value of the right hand side to that variable
% and adds it to the Bindings. Otherwise, asserts that the left hand side
% is equal to the right hand side.
eval_match({var, _, LHS}, Exp2, Bindings, World) ->
    {ok, RHS, Bindings} = eval_expr(Exp2, Bindings, World),
    IsKey = orddict:is_key(LHS, Bindings),
    if
        IsKey ->
            Value = orddict:fetch(LHS, Bindings),
            case Value of
                RHS -> 
                    {ok, RHS, Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        true ->
            NewBindings = orddict:store(LHS, RHS, Bindings),
            {ok, RHS, NewBindings}
    end;
eval_match(Exp1, Exp2, Bindings, World) ->
    {ok, LHS, Bindings} = eval_expr(Exp1, Bindings, World),
    {ok, RHS, Bindings} = eval_expr(Exp2, Bindings, World),
    case LHS of
        RHS -> {ok, RHS, Bindings};
        _ -> {error, "No match of right hand side value."} 
    end.

% Evaluates an if clause
% if there are no conditions to check, implying that no "ture" has been seen
% an error is returned. clasues have lists of statement expressions, and list of list
% of condition statements.
eval_if([], _, _) -> {error, "no true branch found when evaluating an if expression"};
eval_if([HdClause | TlClauses], Bindings, World) ->
    {clause, _, [], [Condition], Statement} = HdClause,
    {ok, Eval_Cond, _} = eval_exprs(Condition, Bindings, World),
    case Eval_Cond of
        true -> eval_exprs(Statement, Bindings, World);
        _ -> eval_if(TlClauses, Bindings, World)
    end.

% Evaluates calls
% local calls are made to the module "local"
% TODO: error handling
eval_call(Module_Name, Function_Name, Param_Values, Bindings, World) ->
    Module = maps:get(Module_Name, World),
    Function_AST = maps:get({Function_Name, length(Param_Values)}, Module),


    eval_function_body(Function_AST, Param_Values, Bindings, World).

% Clause, Guards, LocalBindings, World

% Evaluates the function body in forrm of AST
% Currently there is no type checking when binding parameters.
% TODO: optimize to prevent Local Binding creation at every iteration
eval_function_body([], _, _, _) -> {error, "no function matching given arguments."};
eval_function_body([HdClause | TlClauses], Param_Values, Bindings, World) ->
    {clause, _, Param_List, _, Exprs} = HdClause,
    LocalBindings = lists:map(
        fun({{var, _, Name}, Expr}) ->
            {ok, Value, _} = eval_expr(Expr, Bindings, World), 
            {Name, Value}
        end, 
        lists:zip(Param_List, Param_Values)
    ),
    io:format("The value of Variable is: ~p~n", [HdClause]),
    io:format("The local bindings are: ~p~n", [LocalBindings]),
    case HdClause of
        {_, _, _, [Guards], _} ->
            Guards_Result = lists:foldr(
                fun(Guard, AccIn) -> 
                {ok, Guard_Result, _} = eval_expr(Guard, LocalBindings, World),
                io:format("The Current Guard: ~p~n", [Guard]),
                io:format("The Current Guard evaluated: ~p~n", [Guard_Result]),
                Guard_Result and AccIn
                end,
                true,
                Guards
            ),
            io:format("The Guard Result is: ~p~n", [Guards_Result]),
            if
                Guards_Result ->
                    io:format("Evaluating: ~p~n", [Exprs]),
                    {ok, EvalValue, _} = eval_exprs(Exprs, LocalBindings, World),
                    {ok, EvalValue, Bindings};
                true ->
                    eval_function_body(TlClauses, Param_Values, Bindings, World)
            end;
        _ ->
            {ok, EvalValue, _} = eval_exprs(Exprs, LocalBindings, World),
            {ok, EvalValue, Bindings}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% World Specification
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% World is a map Mod_Atom -> Module_Map
% Module_Map is map {Fun_Atom, Arity} -> FunDefForm
% FunDefForm is the AST returned by erl_pare:parse_form()

% Add a bindig from the name to the module into the world.
world_add_module(World, Module_Name, Module) when is_map(World), is_map(Module) ->
    New_World = World#{Module_Name => Module},
    New_World.

% add the function description described by the String to to the module.
module_add_function_string(Module, Function_Name, Function_Arity, Function_String) when is_map(Module) ->
    {function, _, _, _, Function_Def} = get_AST_form(Function_String),
    New_Module = Module#{{Function_Name, Function_Arity} => Function_Def},
    New_Module.

% Remove the module with the given name from the world
% world_purge_module(World, Module_Name) when is_map(World) ->
%     New_World = maps:remove(Module_Name, World),
%     New_World.

% % add the function description described by the AST to the module.
% module_add_function_AST(Module, Function_Name, Function_Arity, Function_AST) when is_map(Module) ->
%     {function, _, _, _, Function_Def} = Function_AST,
%     New_Module = #{{Function_Name, Function_Arity} => Function_Def},
%     New_Module.

% % remove the function with the given name and arity from the module.
% module_purge_function(Module, Function_Name, Arity) when is_map(Module) ->
%     New_Module = maps:remove({Function_Name, Arity}, Module),
%     New_Module.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Helpers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return AST structure respresented by the given string erlang expression
get_AST(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_exprs(Tokens),
    AST.

% Return AST structure respresented by the given string erlang form
get_AST_form(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_form(Tokens),
    AST.

% call eval after parsing the given string, ignores the World
eval_string(Str, Bindings) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, #{}).

% same as eval string, but does not ignore the World
eval_world(Str, Bindings, World) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, World).