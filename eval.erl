-module(eval).
% evaluators
-export([eval_exprs/3, eval_expr/3, eval_string/2, eval_world/3]).
% helpers to create ASTs
-export([get_AST/1, get_AST_form/1]).


%%% TODO:
%%% handle arity missmatch in function calls
%%% - better function commentary/error handling
%%% - fix try-catch
%% no more string matching, string instead of cons in match
%%% - no supprt for hd("string") which should return an integer.
%%% - add to doc that bindings have to be ordered
%%% - add to doc the new binding rules, types 
%%% - currently no floats are allowed in arithmetic operations
%%% - add to doc new match that takes AST and term()
%%% - try catch is complete except for the after functionality, but now alos matching
%%% - maps?
%%% %%% new types: ast and fun. add all types to the doc

%%% Time Allows
% test the error handling, add line numbers and 
%   proper error messages, atoms from erlang docs.
% built in guard functions
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
        {atom, _, Atom} -> {ok, {atom, Atom}, Bindings};
        % nil
        {nil, _} -> {ok, {nil, []}, Bindings};
        % integer
        {integer, _, Val} -> {ok, {integer, Val}, Bindings};
        % float
        {float, _, Val} -> {ok, {float, Val}, Bindings};
        % string
        {string, _, String} -> {ok, {string, String}, Bindings};
        % list
        {cons, _, Car, Cdr} ->
            EvalHead = eval_expr(Car, Bindings, World),
            EvalTail = eval_expr(Cdr, Bindings, World),
            case {EvalHead, EvalTail} of
                % TODO: remove duplication
                {{ok, Head, HdBindings}, {ok, {cons, Tail}, TlBindings}} ->
                    NewBindings = orddict:merge(fun(_, Value1, _) -> Value1 end, HdBindings, TlBindings),
                    {ok, {cons, [Head | Tail]}, NewBindings};
                {{ok, Head, HdBindings}, {ok, {nil, []}, TlBindings}} ->
                    NewBindings = orddict:merge(fun(_, Value1, _) -> Value1 end, HdBindings, TlBindings),
                    {ok, {cons, [Head]}, NewBindings};
                {{ok, Head, HdBindings}, {ok, Tail, TlBindings}} ->
                    NewBindings = orddict:merge(fun(_, Value1, _) -> Value1 end, HdBindings, TlBindings),
                    {ok, {cons, [Head | Tail]}, NewBindings};
                _ -> {error, "illegal list."}
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
        % match
        {match, _, Exp1, Exp2} ->
            match:eval_match(Exp1, Exp2, Bindings, World);
        % operation
        {op, _, Op, Exp1, Exp2} -> 
            Operand1 = eval_expr(Exp1, Bindings, World),
            Operand2 = eval_expr(Exp2, Bindings, World),
            eval_op(Op, Operand1, Operand2, Bindings);
        % negtive integer/sign change
        {op, _, '-', Expr} ->
            Eval_Value = eval_expr(Expr, Bindings, World),
            case Eval_Value of
                {ok, {_, Val}, _} -> {ok, {integer, -Val}, Bindings};
                _ -> {error, "illegal expression."}
            end;
        % if
        {'if', _, Clasues} -> eval_if(Clasues, Bindings, World);
        % case of
        {'case', _, Arg, Clauses} -> 
            eval_case(Arg, Clauses, Bindings, World);
        % try catch (without 'after')
        {'try', _, Exprs, Patterns, CatchClauses, _} ->
            eval_try_catch(Exprs, Patterns, CatchClauses, Bindings, World);
        % local call
        {call, _, {atom, _, Function_Name}, Args} -> 
            eval_call(local, Function_Name, Args, Bindings, World);
        % remote call
        {call, _, {remote, _, {atom, _, Module_Name}, {atom, _, Function_Name} }, Args} -> 
            eval_call(Module_Name, Function_Name, Args, Bindings, World);
        % call to fun expression
        {call, _, Fun_Call, Args} ->
            Fun_Exp = eval_expr(Fun_Call, Bindings, World),
            case Fun_Exp of
                {ok, {'fun', {Name, Arity}}, NewBindings} ->
                    % TODO: error handlig for when the number of args is incorrect,
                    % also  this to the eval_call function
                    {{clauses, Clauses}, Fun_Bindings} = orddict:fetch({Name, Arity}, NewBindings),
                    Eval_Value = eval_function_body(Clauses, Args, NewBindings, Fun_Bindings, World, World),
                    case Eval_Value of
                        % TODO,  new   bindings if it returns a fun
                        {ok, Value, _} -> {ok, Value, NewBindings};
                        _ -> Eval_Value
                    end;
                _ -> Fun_Exp
            end;
        % fun
        {'fun', Line, {clauses, Clauses}} -> eval_fun(Clauses, Line, Bindings, World);
        % not accepted language
        _ -> {error, "AST is not accepted by the evaluator."}
    end.

% Given two pre-evaluated expressions, applies the given operation.
% returns {ok, term(), Bindings} | {error, string()}
eval_op(_, {error, Message}, _, _) -> {error, "Invalid first argument for the operation+ " ++ Message};
eval_op(_, _, {error, Message}, _) -> {error, "Invalid second argument for the operation: + " ++ Message};
eval_op(Op, {ok, {Type1, Operand1}, _}, {ok, {Type2, Operand2}, _}, Bindings) ->
    case Op of
        '+' when (Type1 == integer orelse Type1 == float), (Type2 == integer orelse Type2 == float) ->
            {ok, {Type1, Operand1 + Operand2}, Bindings};
        '-' when (Type1 == integer orelse Type1 == float), (Type2 == integer orelse Type2 == float) ->
            {ok, {Type1, Operand1 - Operand2}, Bindings};
        '*' when (Type1 == integer orelse Type1 == float), (Type2 == integer orelse Type2 == float) ->
            {ok, {Type1, Operand1 * Operand2}, Bindings};
        'div' when (Type1 == integer), (Type2 == integer) ->
            {ok, {Type1, Operand1 div Operand2}, Bindings};
        '++' when (Type1 == string orelse Type1 == cons orelse Type1 == nil), 
                  (Type2 == string orelse Type2 == cons orelse Type2 == nil) ->
            {ok, {Type1, Operand1 ++ Operand2}, Bindings};
        '|' ->
            [Operand1 | Operand2];
        '==' -> {ok, {atom, Operand1 == Operand2}, Bindings};
        '/=' -> {ok, {atom, Operand1 /= Operand2}, Bindings};
        '<' -> {ok, {atom, Operand1 < Operand2}, Bindings};
        '=<' -> {ok, {atom, Operand1 < Operand2}, Bindings};
        '>' -> {ok, {atom, Operand1 > Operand2}, Bindings};
        '>=' -> {ok, {atom, Operand1 < Operand2}, Bindings};
        'and' when (Type1 == atom andalso Type2 == atom) ->
            {ok, {atom, Operand1 and Operand2}, Bindings};
        'or' when (Type1 == atom andalso Type2 == atom) ->
            {ok, {atom, Operand1 or Operand2}, Bindings};
        '=:=' -> {ok, {atom, Operand1 =:= Operand2}, Bindings};
        '!' when Type1 == pid ->
            {{ok, Operand2, Bindings}, {message, {{Type1, Operand1}, {Type2, Operand2}}}};
        _ -> {error, "Operation with given arguments is not allowed by the evaluator."}
    end.

% Evaluates given AST with the assumption that it represents a tuple.
% Tuples are of the form {tuple, Line_Number, TupleList}
% First parses and evaluates the TupleList, then produces the corresponding tuple.
eval_tuple([], _, Bindings) -> {ok, {tuple, {}}, Bindings};
eval_tuple(TupleList, Bindings, World) when is_list(TupleList)->
    TermList = eval_AST_list(TupleList, Bindings, World, []),
    case TermList of
        {error, _} -> TermList;
        _ -> {ok, {tuple, list_to_tuple(TermList)}, Bindings}
    end;
eval_tuple(_, _, _) -> {error, "invalid tuple"}.


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
    TryMatch = match:eval_match(Case, Arg, Bindings, World),
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
% TODO:
% no pattern matching for now
% complete the try-catch design
%eval_try_catch(Exprs, Patterns, CatchClauses, Bindings, World);
% eval:get_AST("try X =:= X div 1 catch error:E -> false end."). 
eval_try_catch(Exprs, [], _, Bindings, World) ->
    Eval_Result = eval_exprs(Exprs, Bindings, World),
    case Eval_Result of
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings}; 
        {error, _} -> {ok, {atom, false}, Bindings} % Handle error clauses here
    end.
% eval_try_catch(Exprs, Patterns, _, Bindings, World) ->
%     Eval_Result = eval_exprs(Exprs, Bindings, World),
%     case Eval_Result of
%         {ok, EvalVal, _} -> eval_case(EvalVal, Patterns, Bindings, World); 
%         {error, _} -> {ok, {atom, false}, Bindings} % Handle error clauses here
%     end.

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
    Local_Module = maps:merge(maps:get(local, world:world_init()), Module),
    Local_World = world:world_add_module(World, local, Local_Module),
    Function_Result = eval_function_body([HdClause | TlClauses], 
        Args,
        Bindings,
        [],
        World,
        Local_World),
    case Function_Result of
        {ok, {'fun', NameAndArity}, FunBindings} ->
            % TODO: error handling for failed fetch
            FunBody = orddict:fetch(NameAndArity, FunBindings),
            {ok, {'fun', NameAndArity}, orddict:store(NameAndArity, FunBody, Bindings)};
        {ok, EvalVal, _} -> {ok, EvalVal, Bindings};
        {error, Message} -> {error, Message};
        _ -> {error, "Function evaluation failed."}
    end.

% Evaluates the function body in form of AST
% Currently there is no type checking when binding parameters.
eval_function_body([], _, _, _, _, _) -> {error, "no function matching given arguments."};
eval_function_body([HdClause | TlClauses], Args, Bindings, BodyBindings, World, LocalWorld) ->
    {clause, _, Param_List, _, _} = HdClause,
    LocalBindings = create_local_bindings(Param_List, Args, Bindings, BodyBindings, World),
    case {HdClause, LocalBindings} of
        {_, {error, _}} -> 
            eval_function_body(TlClauses, Args, Bindings, BodyBindings, World, LocalWorld);
        {{clause, _, _, [], Exprs}, _} ->
            eval_exprs(Exprs, LocalBindings, LocalWorld);
        {{clause, _, _, [Guards], Exprs}, _} ->
            Guards_Result = eval_conditions(Guards, LocalBindings, world:world_init()),
            case Guards_Result of
                true ->
                    eval_exprs(Exprs, LocalBindings, LocalWorld);
                _ ->
                    eval_function_body(TlClauses, Args, Bindings, BodyBindings, World, LocalWorld)
            end;
        _ -> {error, "The function guards are invalid."}
    end.

% Given a list of paramteres and arguments, match each parameter to the corresponidng binding
% and return the new bindings created by the match.
create_local_bindings([], [], _, Bindings, _) -> Bindings;
create_local_bindings(ParamList, Args, Bindings, BindingsAcc, World) when length(ParamList) == length(Args) ->
    Match_Value = match:eval_param_match(hd(ParamList), hd(Args), Bindings, [], World),
    case Match_Value of
        {error, _} -> Match_Value;
        _ ->
            NewBindings = orddict:merge(fun(_, Value1, _) -> Value1 end, BindingsAcc, Match_Value),
            create_local_bindings(tl(ParamList), tl(Args), Bindings, NewBindings, World)
    end;
create_local_bindings(_, _, _, _, _) -> {error, "illegal param-arg lists."}.
 

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evalulate Fun Expressions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluates a fun statement by generating a unique name and the {name, arity} 
% pair as a key for the given clauses in the Bindings. Returns the generated name
% which has a 'fun' type.
eval_fun(Clauses, Line, Bindings, _) ->
    FunName = list_to_atom("#Fun<" ++ integer_to_list(Line) ++ "."++ integer_to_list(erlang:unique_integer([positive])) ++ ">"),
    [{clause, _, ArgList, _, _} | _] = Clauses,
    FunArity = length(ArgList),
    {ok, {'fun', {FunName, FunArity}}, orddict:store({FunName, FunArity}, {{clauses, Clauses}, Bindings}, Bindings)}.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Helpers
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Given list of ASTs, produce the list of values produced by each AST
% returns Acc | {error, string()}
eval_AST_list([], _, _, Acc) -> Acc;
eval_AST_list([Hd | Tl], Bindings, World, Acc) ->
    Eval_Result = eval_expr(Hd, Bindings, World),
    case Eval_Result of
        {ok, Value, _} -> 
            eval_AST_list(Tl, Bindings, World, Acc ++ [Value]);
        _ -> Eval_Result
    end;
eval_AST_list(_, _, _, _) -> {error, "invalid AST List."}.

% Evalutes a list of AST as if it represents a list of bool expressions
% Return true if every expression in the given AST list evaluates true
eval_conditions([], _, _) -> true;
eval_conditions([Condition | Rest], Bindings, World) ->
    Condition_Result = eval_expr(Condition, Bindings, World),
    case Condition_Result of
        {ok, {atom, true}, _} -> eval_conditions(Rest, Bindings, World);
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