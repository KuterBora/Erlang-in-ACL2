-module(eval).
% evaluators
-export([eval_exprs/3, eval_expr/3, eval_string/2, eval_world/3]).
% helpers to create ASTs
-export([get_AST/1, get_AST_form/1]).

%%% TODO:

%%% Core
% - built in hd and tl
% fix/test local binding creation
% - pattern matching in functions

%%% Time Allows
% - tuples matching
% fix try-catch
% - maps
% test the error handling
% built in guard functions, rest
% test different pattern matching
% modify world_add_module to load from an existing erlang file
%   and handle the Module Map creation automatically.

%%% Utility
% document changes
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
        % tuples
        {tuple, _, TupleList} -> eval_tuple(TupleList, Bindings, World);
        % variables
        {var, _, Var} -> {ok, orddict:fetch(Var, Bindings), Bindings};
        % macthes
        {match, _, Exp1, Exp2} -> eval_match(Exp1, Exp2, Bindings, World);
        % operations
        {op, _, Op, Exp1, Exp2} -> 
                Operand1 = eval_expr(Exp1, Bindings, World),
                Operand2 = eval_expr(Exp2, Bindings, World),
            eval_op(Op, Operand1, Operand2, Bindings);
        % if
        {'if', _, Clasues} -> eval_if(Clasues, Bindings, World);
        % local calls
        {call, _, {atom, _, Function_Name}, Args} -> 
            eval_call(local, Function_Name, Args, Bindings, World);
        % remote calls
        {call, _, {remote, _, {atom, _, Module_Name}, {atom, _, Function_Name} }, Args} -> 
            eval_call(Module_Name, Function_Name, Args, Bindings, World);
        % try catch statements (simplified)
        {'try', _, Exprs, _, _, _} ->
            eval_try_catch(Exprs, Bindings, World);
        % unrecognized language
        _ -> {error, "Language in the AST is not recognized by the evaluator."}
    end.

% Given an Operation, Bindings and two expressions as ASTs,
% evaluate the AST expressions and apply the given operation.
% Exp1 and Exp2 are not associative, Exp1 must be used first.
eval_op(_, {error, _}, _, _) -> {error, "Invalid argument for the operation."};
eval_op(_, _, {error, _}, _) -> {error, "Invalid argument for the operation."};
eval_op(Op, {ok, Operand1, _}, {ok, Operand2, _}, Bindings) ->
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
        '=:=' -> {ok, Operand1 =:= Operand2, Bindings};
        _ -> {error, "Operation with given arguments is not recognized by the evaluator."}
    end.

% Evaluate Tuples
% Tuples are of the form {tuple, Line_Number, List}.
% First parse the list, then convert it to a tuple
eval_tuple([], _, Bindings) -> {ok, {}, Bindings};
eval_tuple(TupleList, Bindings, World) when is_list(TupleList)->
    TermList = parse_AST_list(TupleList, Bindings, World, []),
    {ok, list_to_tuple(TermList), Bindings};
eval_tuple(_, _, _) -> {error, "invalid tuple"}.

% Parse AST List
% [AST1, AST2, ...], Bindings, World -> [term1, term2, ...]
% Evaluate each AST and embed its value in the correct position
% in the list
parse_AST_list([], _, _, Acc) -> Acc;
parse_AST_list([Hd | Tl], Bindings, World, Acc) ->
    {ok, Head, _} = eval_expr(Hd, Bindings, World),
    parse_AST_list(Tl, Bindings, World, Acc ++ [Head]);
parse_AST_list(_, _, _, _) -> {error, "invalid AST List"}.


% Given a match statement, if the left hand side is an unbound
% variable, assigns the value of the right hand side to that variable
% and adds it to the Bindings. Otherwise, asserts that the left hand side
% is equal to the right hand side.

% match variables
eval_match({var, _, LHS}, Exp2, Bindings, World) ->
    {ok, RHS, _} = eval_expr(Exp2, Bindings, World),
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

% macth lists
eval_match({cons, _, {var, _, Hd}, {var, _, Tl}}, {cons, _, Car, Cdr}, Bindings, World) ->
    {ok, RHS_Head, _} = eval_expr(Car, Bindings, World),
    {ok, RHS_Tail, _} = eval_expr(Cdr, Bindings, World),
    Hd_is_key = orddict:is_key(Hd, Bindings),
    Tl_is_key = orddict:is_key(Tl, Bindings),
    if
        Hd_is_key andalso Tl_is_key ->
            Head_Value = orddict:fetch(Hd, Bindings),
            Tail_Value = orddict:fetch(Tl, Bindings),
            case {Head_Value, Tail_Value} of
                {RHS_Head, RHS_Tail} -> {ok, [RHS_Head | RHS_Tail], Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Hd_is_key ->
            Head_Value = orddict:fetch(Hd, Bindings),
            Tl_to_Bindings = orddict:store(Tl, RHS_Tail, Bindings),
            case Head_Value of
                RHS_Head -> {ok, [RHS_Head | RHS_Tail], Tl_to_Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Tl_is_key ->
            Tail_Value = orddict:fetch(Tl, Bindings),
            Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
            case Tail_Value of
                RHS_Tail -> {ok, [RHS_Head | RHS_Tail], Hd_to_Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        true ->
            Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
            Tl_to_Bindings = orddict:store(Tl, RHS_Tail, Hd_to_Bindings),
            {ok, [RHS_Head | RHS_Tail], Tl_to_Bindings}
    end;
eval_match({cons, _, Hd, {var, _, Tl}}, {cons, _, Car, Cdr}, Bindings, World) ->
    {ok, RHS_Head, _} = eval_expr(Car, Bindings, World),
    {ok, RHS_Tail, _} = eval_expr(Cdr, Bindings, World),
    {ok, LHS_Head, _} = eval_expr(Hd, Bindings, World),
    IsKey = orddict:is_key(Tl, Bindings),
    if
        RHS_Head == LHS_Head andalso IsKey ->
            Value = orddict:fetch(Tl, Bindings),
            case Value of
                RHS_Tail -> 
                    {ok, [RHS_Head | RHS_Tail], Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        RHS_Head == LHS_Head ->
            NewBindings = orddict:store(Tl, RHS_Tail, Bindings),
            {ok, [RHS_Head | RHS_Tail], NewBindings};
        true ->
            {error, "No match of right hand side value."}
    end;
eval_match({cons, _, {var, _, Hd}, Tl}, {cons, _, Car, Cdr}, Bindings, World) ->
    {ok, RHS_Head, _} = eval_expr(Car, Bindings, World),
    {ok, RHS_Tail, _} = eval_expr(Cdr, Bindings, World),
    {ok, LHS_Tail, _} = eval_expr(Tl, Bindings, World),
    IsKey = orddict:is_key(Hd, Bindings),
    if
        RHS_Tail == LHS_Tail andalso IsKey ->
            Value = orddict:fetch(Hd, Bindings),
            case Value of
                RHS_Head -> 
                    {ok, [RHS_Head | RHS_Tail], Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        RHS_Tail == LHS_Tail ->
            NewBindings = orddict:store(Hd, RHS_Head, Bindings),
            {ok, [RHS_Head | RHS_Tail], NewBindings};
        true ->
            {error, "No match of right hand side value."}
    end;

% match tuples TODO
% eval_match({tuple, _, TupleList_LHS}, {tuple, _, TupleList_RHS}, Bindings, World) ->
%     if
%         length(TupleList_LHS) == length(TupleList_RHS) ->
%             {ok, _, NewBindings} = eval_match_tuple(TupleList_LHS, TupleList_RHS, Bindings, World),
%             {ok, list_to_tuple(parse_AST_list(TupleList_RHS, Bindings, World, [])), NewBindings};
%         true -> {error, "No match of right hand side value."}
%     end; 

% macth values
eval_match(Exp1, Exp2, Bindings, World) ->
    {ok, LHS, Bindings} = eval_expr(Exp1, Bindings, World),
    {ok, RHS, Bindings} = eval_expr(Exp2, Bindings, World),
    case LHS of
        RHS -> {ok, RHS, Bindings};
        _ -> {error, "No match of right hand side value."} 
    end.

% TODO
% Evaluate a match with tuples. Requires that length(RHS) == length(LHS)
% returns {ok, SomeValue, NewBindings} or {error, message}
% NewBindings is list of bindings created by matching variables to RHS. 
% eval_match_tuple([LHS_Hd | LHS_Tl], [RHS_Hd | RHS_Tl], Bindings, World) ->
%     {ok, RHS_Head, _} = eval_expr(RHS_Hd, Bindings, World),
%     IsKey = orddict:is_key(LHS_Hd, Bindings),
%     case IsKey of
%         true -> {error}
%     end.


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

% Evaluate a try catch expression
% Does not have actual functionality currently, catches any error regardless.
% Only handles try catches of the form % try <Exp> catch error:<E> -> false end.
% TODO: implement a recursive function to handle catches, requires tuple implementation
eval_try_catch(Exprs, Bindings, World) ->
    Eval_Result = eval_exprs(Exprs, Bindings, World),
    case Eval_Result of 
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings}; 
        {error, _} -> {ok, false, Bindings};
        _ -> {error, "Failed to catch any errors, but evaluator did not return ok."}
    end.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Calls
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates calls
% local calls are made to the module "local"
% TODO: error handling, bindings must be made in body evaluation when pattern matching is added
eval_call(Module_Name, Function_Name, Args, Bindings, World) ->
    Module = maps:get(Module_Name, World),
    Function_Arity = length(Args),
    Function_Def = maps:get({Function_Name, Function_Arity}, Module),
    [HdClause | TlClauses] = Function_Def,
    Local_Module = world:module_add_function_AST(
        maps:get(local, World),
        Function_Name,
        Function_Arity,
        Function_Def
    ),
    Local_World = world:world_add_module(world:world_init(), local, Local_Module),
    Function_Result = eval_function_body([HdClause | TlClauses], Args, Bindings,  World, Local_World),
    case Function_Result of
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings};
        {error, Message} -> {error, Message};
        _ -> {error, "Function evaluation failed."}
    end.


% Evaluates the function body in forrm of AST
% Currently there is no type checking when binding parameters.
eval_function_body([], _, _, _, _) -> {error, "no function matching given arguments."};
eval_function_body([HdClause | TlClauses], Args, Bindings, World, LocalWorld) ->
    {clause, _, Param_List, _, _} = HdClause,

    Argument_Values = parse_AST_list(Args, Bindings, World, []),

    LocalBindings = lists:map(
        fun({{var, _, Name}, Arg}) -> 
            {Name, Arg};
        
        ({_, _}) -> {empty, empty}
        end, 
        lists:zip(Param_List, Argument_Values)
    ),
    
    % Pattern matching in function signitures cannot make calls, so the world is empty 
    Param_Values = parse_AST_list(Param_List, LocalBindings, #{}, []),
    if
        Argument_Values == Param_Values ->
            case HdClause of
                {clause, _, _, [], Exprs} ->
                    eval_exprs(Exprs, LocalBindings, LocalWorld);
                {clause, _, _, [Guards], Exprs} ->
                    Guards_Result = lists:foldr(
                        fun(Guard, AccIn) -> 
                        {ok, Guard_Result, _} = eval_expr(Guard, LocalBindings, LocalWorld),
                        Guard_Result and AccIn
                        end,
                        true,
                        Guards
                    ),
                    case Guards_Result of
                        true ->
                            eval_exprs(Exprs, LocalBindings, LocalWorld);
                        _ ->
                            eval_function_body(TlClauses, Args, Bindings, World, LocalWorld)
                    end;
                _ -> {error, "The function guards are invalid."}
            end;
        true -> eval_function_body(TlClauses, Args, Bindings, World, LocalWorld)
    end.


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
    eval_exprs(AST, Bindings, world:world_init()).

% same as eval string, but does not ignore the World
eval_world(Str, Bindings, World) ->
    AST = get_AST(Str),
    eval_exprs(AST, Bindings, World).