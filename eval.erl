-module(eval).
% evaluators
-export([eval_exprs/3, eval_expr/3, eval_string/2, eval_world/3]).
% helpers to create ASTs
-export([get_AST/1, get_AST_form/1]).

%%% TODO:

% tell mark
% added _
% lots of bug fixing and tests
% types
% fun

% tuple matching not done yet


%%% - typed bindings
%%% - tuples matching
%%% - fun expression

%%% - control F TODO 
%%% - refactor match
%%% - fix try-catch
%%% - better function commentary/error handling
%%% - maps
%%%
%%% - add to doc that bindings have to be ordered
%%% - add to doc the new binding rules

%%% Time Allows
% test the error handling, add line numbers and 
%   proper error messages.
% built in guard functions
% test different pattern matching
% modify world_add_module to load from an existing erlang file
%   and handle the Module Map creation automatically.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  The Evaluator
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates the given list of AST linearly with the given Bindings and World.
% Bindings created by a previous AST are used by the next.
% Value and Bindings produced by the last AST are returned.
% - ASTs is a list of abstract syntax trees returned by erl_parse:parse_exprs()
% - Bindings is an orddict() of atom to term()
% - World is a map of the form: #{module_name => #{{function_name, arity} => AST}}
% Returns {ok, term(), NewBindings} | {error, string()}
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

% Evaluates the given AST with the given Bidnings and World.
% - AST is an abstract syntax tree returned by erl:parse_exprs
% - Binding is an orddict from atom to term()
% - World is a map of the form: #{module_name => #{{function_name, arity} => AST}}
% Returns {ok, term(), NewBindings} | {error, string()}
eval_expr(AST, Bindings, World) ->
    case AST of
        % atom
        {atom, _, Atom} -> {ok, Atom, Bindings};
        % nil
        {nil, _} -> {ok, [], Bindings};
        % integer
        {integer, _, Val} -> {ok, Val, Bindings};
        % string
        {string, _, String} -> {ok, String, Bindings};
        % list
        {cons, _, Car, Cdr} ->
            EvalHead = eval_expr(Car, Bindings, World),
            EvalTail = eval_expr(Cdr, Bindings, World),
            case {EvalHead, EvalTail} of
                {{ok, Head, _}, {ok, Tail, _}} -> 
                    {ok, [Head | Tail], Bindings};
                _ -> {error, "error"}
            end;
        % tuple
        {tuple, _, TupleList} -> eval_tuple(TupleList, Bindings, World);
        % variable
        {var, _, Var} -> 
            Find = orddict:find(Var, Bindings),
            case Find of
                {ok, Value} -> {ok, Value, Bindings};
                _ -> {error, "Variable unbound"}
            end;
        % macth
        {match, _, Exp1, Exp2} -> eval_match(Exp1, Exp2, Bindings, World);
        % operation
        {op, _, Op, Exp1, Exp2} -> 
            Operand1 = eval_expr(Exp1, Bindings, World),
            Operand2 = eval_expr(Exp2, Bindings, World),
            eval_op(Op, Operand1, Operand2, Bindings);
        % negtive integer/sign change
        {op, _, '-', Expr} -> 
            {ok, Val, _} = eval_expr(Expr, Bindings, World),
            {ok, -Val, Bindings};
        % if
        {'if', _, Clasues} -> eval_if(Clasues, Bindings, World);
        % case of
        {'case', _, Arg, Clauses} -> eval_case(Arg, Clauses, Bindings, World);
        % try catch statements (simplified)
        {'try', _, Exprs, _, _, _} ->
            eval_try_catch(Exprs, Bindings, World);
        % local calls
        {call, _, {atom, _, Function_Name}, Args} -> 
            eval_call(local, Function_Name, Args, Bindings, World);
        % remote calls
        {call, _, {remote, _, {atom, _, Module_Name}, {atom, _, Function_Name} }, Args} -> 
            eval_call(Module_Name, Function_Name, Args, Bindings, World);
        % fun (not so fun)
        % {'fun', _, {clauses, Clauses}} -> eval_fun(Clauses, Bindings, World);
        % not accepted language
        _ -> {error, "AST is not accepted by the evaluator."}
    end.

% Given two pre-evaluated expressions, applies the given operation.
% returns {ok, term(), Bindings} | {error, string()}
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
        _ -> {error, "Operation with given arguments is not allowed by the evaluator."}
    end.

% Evaluates given AST with the assumption that it represents a tuple.
% Tuples are of the form {tuple, Line_Number, TupleList}
% First parses and evaluates the TupleList, then produces the corresponding tuple.
eval_tuple([], _, Bindings) -> {ok, {}, Bindings};
eval_tuple(TupleList, Bindings, World) when is_list(TupleList)->
    TermList = eval_AST_list(TupleList, Bindings, World, []),
    {ok, list_to_tuple(TermList), Bindings};
eval_tuple(_, _, _) -> {error, "invalid tuple"}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Given a match statement, if the left hand side is an unbound
% variable, assigns the value of the right hand side to that variable
% and adds it to the Bindings. Otherwise, asserts that the left hand side
% is equal to the right hand side.
% returns {ok, term(), NewBindings} | {error, string()}

% var = term()
eval_match({var, _, LHS}, Exp2, Bindings, World) ->
    Eval_RHS = eval_expr(Exp2, Bindings, World),
    case Eval_RHS of
        {ok, RHS, _} -> 
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
        _ -> {error, "Failed to evaluate left hand side value."}
    end;

% macth lists
% {cons var var} = term()
% TODO: check RHS is a non-empty list
eval_match({cons, _, {var, _, Hd}, {var, _, Tl}}, RHS, Bindings, World) ->
    % TODO: check if RHS_Value is ok
    {ok, RHS_Value, _} = eval_expr(RHS, Bindings, World),
    RHS_Head = hd(RHS_Value),
    RHS_Tail = tl(RHS_Value),
    Hd_is_key = orddict:is_key(Hd, Bindings),
    Tl_is_key = orddict:is_key(Tl, Bindings),
    if
        Hd == '_' andalso Tl == '_' ->
            {ok, [RHS_Head | RHS_Tail], Bindings};
        Hd_is_key andalso Tl_is_key ->
            Head_Value = orddict:fetch(Hd, Bindings),
            Tail_Value = orddict:fetch(Tl, Bindings),
            case {Head_Value, Tail_Value} of
                {RHS_Head, RHS_Tail} -> {ok, [RHS_Head | RHS_Tail], Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Hd_is_key andalso Tl /= '_' ->
            Head_Value = orddict:fetch(Hd, Bindings),
            Tl_to_Bindings = orddict:store(Tl, RHS_Tail, Bindings),
            case Head_Value of
                RHS_Head -> {ok, [RHS_Head | RHS_Tail], Tl_to_Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Tl_is_key andalso Hd /= '_' ->
            Tail_Value = orddict:fetch(Tl, Bindings),
            Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
            case Tail_Value of
                RHS_Tail -> {ok, [RHS_Head | RHS_Tail], Hd_to_Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Hd_is_key andalso Tl == '_' ->
            Head_Value = orddict:fetch(Hd, Bindings),
            case Head_Value of
                RHS_Head -> {ok, [RHS_Head | RHS_Tail], Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Tl_is_key andalso Hd == '_' ->
            Tail_Value = orddict:fetch(Tl, Bindings),
            case Tail_Value of
                RHS_Tail -> {ok, [RHS_Head | RHS_Tail], Bindings};
                _ -> {error, "No match of right hand side value."}
            end;
        Hd == '_' ->
            Tl_to_Bindings = orddict:store(Tl, RHS_Tail, Bindings),
            {ok, [RHS_Head | RHS_Tail], Tl_to_Bindings};
        Tl == '_' ->
            Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
            {ok, [RHS_Head | RHS_Tail], Hd_to_Bindings};
        true ->
            Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
            Tl_to_Bindings = orddict:store(Tl, RHS_Tail, Hd_to_Bindings),
            {ok, [RHS_Head | RHS_Tail], Tl_to_Bindings}
    end;

% {cons term() var} = term()
% TODO: check RHS is a non-empty list
eval_match({cons, _, Hd, {var, _, Tl}}, RHS, Bindings, World) ->
    % TODO: check if RHS_Value is ok
    {ok, RHS_Value, _} = eval_expr(RHS, Bindings, World),
    RHS_Head = hd(RHS_Value),
    RHS_Tail = tl(RHS_Value),
    % TODO: check if LHS_Value is ok
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
        RHS_Head == LHS_Head andalso Tl == '_' ->
            {ok, [RHS_Head | RHS_Tail], Bindings};
        RHS_Head == LHS_Head ->
            NewBindings = orddict:store(Tl, RHS_Tail, Bindings),
            {ok, [RHS_Head | RHS_Tail], NewBindings};
        true ->
            {error, "No match of right hand side value."}
    end;

% {cons var term()} = term()
% TODO: check RHS is a non-empty list
eval_match({cons, _, {var, _, Hd}, Tl}, RHS, Bindings, World) ->
    % TODO: check if RHS_Value is ok
    {ok, RHS_Value, _} = eval_expr(RHS, Bindings, World),
    RHS_Head = hd(RHS_Value),
    RHS_Tail = tl(RHS_Value),
    % TODO: check if LHS_Value is ok
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
        RHS_Tail == LHS_Tail andalso Hd == '_' ->
            {ok, [RHS_Head | RHS_Tail], Bindings};
        RHS_Tail == LHS_Tail ->
            NewBindings = orddict:store(Hd, RHS_Head, Bindings),
            {ok, [RHS_Head | RHS_Tail], NewBindings};
        true ->
            {error, "No match of right hand side value."}
    end;

% term() = term()
eval_match(Exp1, Exp2, Bindings, World) ->
    % TODO: check if LHS and RHS are ok
    {ok, LHS, Bindings} = eval_expr(Exp1, Bindings, World),
    {ok, RHS, Bindings} = eval_expr(Exp2, Bindings, World),
    case LHS of
        RHS -> {ok, RHS, Bindings};
        _ -> {error, "No match of right hand side value."} 
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Guards/if/case/try
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates an if clause
% if there are no conditions to check, implying that no "ture" has been seen
% an error is returned. clasues have lists of statement expressions, and list of list
% of condition statements.
eval_if([], _, _) -> {error, "no true branch found when evaluating an if expression"};
eval_if([HdClause | TlClauses], Bindings, World) ->
    {clause, _, [], [Conditions], Statement} = HdClause,
    Eval_Conds = eval_conditions(Conditions, Bindings, World),
    case Eval_Conds of
        true -> eval_exprs(Statement, Bindings, World);
        _ -> eval_if(TlClauses, Bindings, World)
    end.

% Evaluates a case of expression
% if there are no conditions to check, implying that no "_" has been seen
% an error is returned. clasues have lists of arguments to be matched, lists of guards,
% and lists of expressions to be returned.
eval_case(_, [], _, _) -> {error, "no case clause matching given argument."};
eval_case(Arg, [HdClause | TlClauses], Bindings, World) ->
    {clause, _, [Case], Guards, Statement} = HdClause,
    TryMatch = eval_match(Case, Arg, Bindings, World),
    case {TryMatch, Guards} of
        {{ok, _, NewBindings}, [GuardList]} ->
            % TODOC: only pass in world_init() as guards can't make remote calls.
            Eval_Guards = eval_conditions(GuardList, NewBindings, world:world_init()),
            if
                Eval_Guards -> eval_exprs(Statement, NewBindings, World);
                true -> eval_case(Arg, TlClauses, Bindings, World)
            end;
        {{ok, _, NewBindings}, []} ->
            eval_exprs(Statement, NewBindings, World);
        _ -> eval_case(Arg, TlClauses, Bindings, World)
    end.

% Evaluates a try catch expression
% Does not have actual functionality currently, catches any error regardless.
% Only handles try catches of the form try <Exp> catch error:<E> -> false end.
% TODO: complete the try-catch design
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
eval_call(Module_Name, Function_Name, Args, Bindings, World) ->
    Module = maps:get(Module_Name, World),
    Function_Arity = length(Args),
    Function_Def = maps:get({Function_Name, Function_Arity}, Module),
    [HdClause | TlClauses] = Function_Def,
    Local_Module = world:module_add_function_AST(
        maps:get(local, world:world_init()),
        Function_Name,
        Function_Arity,
        Function_Def
    ),
    Local_World = world:world_add_module(World, local, Local_Module),
    Function_Result = eval_function_body([HdClause | TlClauses], Args, Bindings,  World, Local_World),
    case Function_Result of
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings};
        {error, Message} -> {error, Message};
        _ -> {error, "Function evaluation failed."}
    end.


% Evaluates the function body in form of AST
% Currently there is no type checking when binding parameters.
eval_function_body([], _, _, _, _) -> {error, "no function matching given arguments."};
eval_function_body([HdClause | TlClauses], Args, Bindings, World, LocalWorld) ->
    {clause, _, Param_List, _, _} = HdClause,

    Argument_Values = eval_AST_list(Args, Bindings, World, []),
    % TODO: check correctness of Argument Values

    LocalBindings_List = lists:map( %TODO: add tuple matching here, as well as list with a single element
        % TODO: use match rather than this as this does not guarantee the validity of the bindings
        fun({{var, _, Name}, Arg}) -> [{Name, Arg}];
            ({{cons, _, {var, _, Car}, {var, _, Cdr}}, Arg}) ->
                [{Car, hd(Arg)}, {Cdr, tl(Arg)}];
            ({{cons, _, {var, _, Car}, _}, Arg}) ->
                [{Car, hd(Arg)}];
            ({{cons, _, _, {var, _, Cdr}}, Arg}) ->
                [{Cdr, tl(Arg)}];
            ({_, _}) -> [{empty, empty}]
        end, 
        lists:zip(Param_List, Argument_Values)
    ),

    LocalBindings = lists:sort(lists:flatten(LocalBindings_List)),
    
    % Pattern matching in function signitures cannot make calls, so the world is init()
    % Assume ParamList and LocalBindings are of the same length.
    % Also assume every variable in Param_Values can be evaluated using LocalBindings.
    % TODO: use world:init() instead of empty
    Param_Values = eval_AST_list(Param_List, LocalBindings, #{}, []),
    % TODO: check correctness of Param Values
    if
        Argument_Values == Param_Values ->
            case HdClause of
                {clause, _, _, [], Exprs} ->
                    eval_exprs(Exprs, LocalBindings, LocalWorld);
                {clause, _, _, [Guards], Exprs} ->
                    Guards_Result = eval_conditions(Guards, LocalBindings, world:world_init()),
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
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate a fun expression by creating the function it represents, naming it
% and adding it to the local module of the world. Returns the name (symbol) 
% of the function created.
% eval_fun(Clauses, Bindings, World) -> notSoFun.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Helpers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Given list of ASTs, produce the list of values produced by each AST
eval_AST_list([], _, _, Acc) -> Acc;
eval_AST_list([Hd | Tl], Bindings, World, Acc) ->
    {ok, Head, _} = eval_expr(Hd, Bindings, World),
    eval_AST_list(Tl, Bindings, World, Acc ++ [Head]);
eval_AST_list(_, _, _, _) -> {error, "invalid AST List."}.

% Evalutes a list of AST as if it represents a list of bool expressions
% Return true if every expression in the given AST list evaluates true
eval_conditions([], _, _) -> true;
eval_conditions([Condition | Rest], Bindings, World) ->
    Condition_Result = eval_expr(Condition, Bindings, World),
    case Condition_Result of
        {ok, true, _} -> eval_conditions(Rest, Bindings, World);
        _ -> false
    end.

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