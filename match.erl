-module(match).

-export([eval_match/4, eval_param_match_rhs_value/5, param_match/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return the same as eval_match, except the RHS is pre-evaluated. 
eval_match(LHS, RHS, Bindings, World) ->
    case {LHS, RHS} of
        {_, {error, _}} -> RHS;
        {{var, _, '_'}, _} -> {ok, RHS, Bindings};
        {{var, _, Var}, _} ->
            IsKey = orddict:is_key(Var, Bindings),
            case IsKey of
                true ->
                    LHS_Value = orddict:fetch(Var, Bindings),
                    case LHS_Value of
                        RHS -> {ok, RHS, Bindings};
                        _ -> {error, {badmatch, RHS}}
                    end;
                false ->
                    {ok, RHS, orddict:store(Var, RHS, Bindings)};
                _ -> {error, "Illegal pattern."}
            end;
        {{cons, _, L_Hd, L_Tl}, {cons, R_List}} ->
            Match_Head = eval_match(L_Hd, hd(R_List), Bindings, World),
            case {Match_Head, L_Tl} of
                {{ok, _, NewBindings}, {nil, _}} when tl(R_List) == [] ->
                    {ok, {cons, R_List}, NewBindings};
                {{ok, _, Hd_Bindings}, _} ->
                    Match_Tail = eval_match(L_Tl, {cons, tl(R_List)}, Hd_Bindings, World),
                    case Match_Tail of 
                        {ok, _, Tl_Bindings} -> {ok, {cons, R_List}, Tl_Bindings};
                        _ -> Match_Tail
                    end;
                _ -> Match_Head
            end;
        {{tuple, L_Line, LTupleList}, {tuple, RTuple}} ->
            RTupleList = RTuple, 
            case {LTupleList, RTupleList} of
                {[], []} -> {ok, {tuple, {}}, Bindings};
                _ ->
                    Match_Head = eval_match(hd(LTupleList), hd(RTupleList), Bindings, World),
                    case Match_Head of
                        {ok, _, Hd_Bindings} ->
                            Match_Tail = eval_match({tuple, L_Line, tl(LTupleList)}, 
                                {tuple, tl(RTupleList)}, Hd_Bindings, World),
                            case Match_Tail of
                                {ok, _, Tl_Bindings} -> {ok, {tuple, RTuple}, Tl_Bindings};
                                _ -> Match_Tail
                            end;
                        _ -> Match_Head
                    end
            end;
        _ ->
            Eval_LHS = eval:eval_expr(LHS, Bindings, World),
            case Eval_LHS of
                {ok, RHS, _} -> {ok, RHS, Bindings};
                {ok, _, _} -> {error, {badmatch, RHS}};
                _ -> {error, "Illegal pattern."}
            end
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Parameter Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Given LHS and RHS, match LHS to RHS, but treat every variable in LHS as
% unbound, even if they exist in BindingsIn. Return the new bindings created
% by this match or error.

% match '_'
param_match({var, _, '_'}, _, _, BindingsAcc, _) ->
    BindingsAcc;

% match var = term()/list()/tuple()/fun()
param_match({var, _, Var}, Exp2, BindingsIn, BindingsAcc, World) ->
    RHS = eval:eval_expr(Exp2, BindingsIn, World),
    case RHS of
        % TODO: maybe RBindings?
        {ok,  {'fun', NameAndArity}, FunBindings} ->
            % TODO: error handling for failed fetch
            FunBody = orddict:fetch(NameAndArity, FunBindings),
            NewBindings = orddict:store(NameAndArity, FunBody, BindingsAcc),
            orddict:store(Var, {'fun', NameAndArity}, NewBindings); 
        {ok, RHS_Value, _} ->
            orddict:store(Var, RHS_Value, BindingsAcc);
        _ -> {error, "Illegal Pattern."}
    end;

% list() = list()
param_match({cons, _, L_Hd, L_Tl}, {cons, _, R_Hd, R_Tl}, BindingsIn, BindingsAcc, World) ->
    Match_Heads = param_match(L_Hd, R_Hd, BindingsIn, BindingsAcc, World),
    case Match_Heads of
        {error, _} -> Match_Heads;
        _ ->
            NewBindingsAcc = orddict:merge(fun(_, Value1, _) -> Value1 end, Match_Heads, BindingsAcc),
            param_match(L_Tl, R_Tl, BindingsIn, NewBindingsAcc, World)
    end;

% list() = var()
param_match({cons, Line, L_Hd, L_Tl}, {var, _, Var}, BindingsIn, BindingsAcc, World) ->
    RHS = orddict:fetch(Var, BindingsIn),
    eval_param_match_rhs_value({cons, Line, L_Hd, L_Tl}, RHS, BindingsIn, BindingsAcc, World);

% tuple() = tuple()
param_match({tuple, _, L_List}, {tuple, _, R_List}, BindingsIn, BindingsAcc, World) ->
    param_match_tuple_vars(L_List, R_List, BindingsIn, BindingsAcc, World);

% tuple() = var()
param_match({tuple, Line, TupleList}, {var, _, Var}, BindingsIn, BindingsAcc, World) ->
    RHS = orddict:fetch(Var, BindingsIn),
    eval_param_match_rhs_value({tuple, Line, TupleList}, RHS, BindingsIn, BindingsAcc, World);

% term() = term()
param_match(Exp1, Exp2, BindingsIn, BindingsAcc, World) -> 
    Eval_LHS = eval:eval_expr(Exp1, BindingsIn, World),
    Eval_RHS = eval:eval_expr(Exp2, BindingsIn, World),
    case {Eval_LHS, Eval_RHS} of
        {{ok, LHS, _}, {ok, RHS, _}} when LHS == RHS ->
            BindingsAcc;
        {{ok, _, _}, {ok, _, _}} ->
            {error, "No match of right hand side value."};
        _ -> {error, "Illegal pattern."}
    end.

% Given two lists that represent two tuples, call match on each corresponding 
% element pair. Return combination of the new Bindings obtained from each match.
% However, treat every variable in LHS as unbound. 
% [term()] = [term()]
param_match_tuple_vars([], [], _, BindingsAcc, _) -> BindingsAcc;
param_match_tuple_vars([LHS_First | LHS_Rest], [RHS_First | RHS_Rest], BindingsIn, BindingsAcc, World) ->
    Match_First = param_match(LHS_First, RHS_First, BindingsIn, BindingsAcc, World),
    case Match_First of
        {error, _} -> Match_First;
        _ -> 
            NewBindingsAcc = orddict:merge(fun(_, Value1, _) -> Value1 end, Match_First, BindingsAcc),
            param_match_tuple_vars(LHS_Rest, RHS_Rest, BindingsIn, NewBindingsAcc, World)
    end;
param_match_tuple_vars(_, _, _, _, _) -> {error, "Illegal pattern."}.

% Match LHS to a pre-evaluated RHS while treating every variable in LHS
% as unbound. Return the new bindings created by the match or error.
eval_param_match_rhs_value(LHS, RHS, BindingsIn, BindingsAcc, World) ->
    case {LHS, RHS} of
        {{var, _, '_'}, _} -> BindingsAcc;
        {{var, _, Var}, {'fun', NameAndArity}} ->
            FunBody = orddict:fetch(NameAndArity, BindingsIn),
            NewBindings = orddict:store(NameAndArity, FunBody, BindingsAcc),
            orddict:store(Var, {'fun', NameAndArity}, NewBindings); 
        {{var, _, Var}, _} -> orddict:store(Var, RHS, BindingsAcc);

        {{cons, _, L_Hd, L_Tl}, {cons, R_List}} ->
            Match_Head = eval_param_match_rhs_value(L_Hd, hd(R_List), BindingsIn, BindingsAcc, World),
            case {Match_Head, L_Tl} of
                {{error, _}, _} -> Match_Head;
                {_, {nil, _}} when tl(R_List) == [] -> Match_Head;
                _ -> eval_param_match_rhs_value(L_Tl, {cons, tl(R_List)}, BindingsIn, Match_Head, World)
            end;
        {{tuple, L_Line, LTupleList}, {tuple, RTuple}} ->
            RTupleList = RTuple, 
            case {LTupleList, RTupleList} of
                {[], []} -> BindingsAcc;
                _ ->
                    Match_Head = eval_param_match_rhs_value(hd(LTupleList), hd(RTupleList), 
                        BindingsIn, BindingsAcc, World),
                    case Match_Head of
                        {error, _} -> Match_Head;
                        _ ->
                            eval_param_match_rhs_value({tuple, L_Line, tl(LTupleList)}, 
                                {tuple, tl(RTupleList)}, BindingsIn, Match_Head, World)
                    end
            end;
        _ ->
            Eval_LHS = eval:eval_expr(LHS, BindingsIn, World),
            case Eval_LHS of
                {ok, RHS, _} -> BindingsAcc;
                {ok, _, _} -> {error, "No match of righ hand side value."};
                _ -> {error, "Illegal pattern HERE."}
            end
    end.