-module(match).

-export([eval_match/4, eval_param_match/4]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate macthing LHS to RHS. Update Bindings if necessary.
% Throw a bad_match error if match is not sucessful.
eval_match(LHS, RHS, Bindings, World) ->
    case {LHS, RHS} of
        {{var, _Line, '_'}, _} -> 
            {ok, RHS, Bindings};
        {{var, _Line, Var}, _} ->
            case orddict:is_key(Var, Bindings) of
                true ->
                    case orddict:fetch(Var, Bindings) of
                        RHS -> 
                            {ok, RHS, Bindings};
                        _ -> 
                            {error, {badmatch, RHS}}
                    end;
                _ ->
                    {ok, RHS, orddict:store(Var, RHS, Bindings)}
            end;
        {{cons, _Line, LHS_Hd, LHS_Tl}, {cons, RHS_List}} ->
            MatchHead = eval_match(LHS_Hd, hd(RHS_List), Bindings, World),
            case MatchHead of
                {ok, _HVal, HdBindings} ->
                    case LHS_Tl of
                        {nil, _} when tl(RHS_List) == [] ->
                            {ok, RHS, HdBindings};
                        _ ->
                            MatchTail = 
                                eval_match(
                                    LHS_Tl,
                                    {cons, tl(RHS_List)},
                                    HdBindings,
                                    World
                                ),
                            case MatchTail of
                                {ok, _TVal, TlBindings} ->
                                    {ok, RHS, TlBindings};
                                {yield, _Kont, _Out} ->
                                    yield_todo;
                                _ ->
                                    MatchTail
                            end
                    end;
                {yield, _Kont, _Out} ->
                    yield_todo;
                _ ->
                    MatchHead
            end;
        {{tuple, Line, LTupleList}, {tuple, RTupleList}} ->
            case {LTupleList, RTupleList} of
                {[], []} ->
                    {ok, {tuple, {}}, Bindings};
                _ ->
                    MatchHead = 
                        eval_match(
                            hd(LTupleList),
                            hd(RTupleList),
                            Bindings,
                            World
                        ),
                    case MatchHead of
                        {ok, _HVal, HdBindings} ->
                            MatchTail =
                                eval_match(
                                  {tuple, Line, tl(LTupleList)},
                                  {tuple, tl(RTupleList)},
                                  HdBindings,
                                  World
                                ),
                            case MatchTail of
                                {ok, _TVal, TlBindings} ->
                                    {ok, {tuple, RTupleList}, TlBindings};
                                {yield, _Kont, _Out} ->
                                    yield_todo;
                                _ ->
                                    MatchTail
                            end;
                        {yield, _Kont, _Out} ->
                            yield_todo;
                        _ ->
                            MatchHead
                    end
            end;
        _ ->
            EvalLHS = eval:eval_expr(LHS, Bindings, World),
            case EvalLHS of
                {ok, RHS, NewBindings} -> 
                    {ok, RHS, NewBindings};
                {ok, _, _} -> 
                    {error, {badmatch, RHS}};
                _ ->
                    EvalLHS
            end
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Parameter Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return the Bindings obtained by macthing LHS to RHS.
% Throw a bad_match error if match is not sucessful.
eval_param_match(LHS, RHS, BindingsAcc, World) ->
    case {LHS, RHS} of
        {{var, _, '_'}, _} -> 
            BindingsAcc; 
        {{var, _, Var}, _} -> 
            orddict:store(Var, RHS, BindingsAcc);
        {{cons, _, LHS_Hd, LHS_Tl}, {cons, RHS_List}} ->
            MatchHead = 
                eval_param_match(
                    LHS_Hd,
                    hd(RHS_List),
                    BindingsAcc,
                    World
                ),
            case MatchHead of
                {error, _} ->
                    MatchHead;
                _ ->
                    case LHS_Tl of
                        {nil, _} when tl(RHS_List) == [] ->
                            MatchHead;
                        _ ->
                            eval_param_match(
                                LHS_Tl,
                                {cons, tl(RHS_List)},
                                MatchHead,
                                World
                            )
                    end
            end;
        {{tuple, L_Line, LTupleList}, {tuple, RTupleList}} ->
            case {LTupleList, RTupleList} of
                {[], []} -> 
                    BindingsAcc;
                _ ->
                    MatchHead = 
                        eval_param_match(
                            hd(LTupleList),
                            hd(RTupleList), 
                            BindingsAcc,
                            World
                        ),
                    case MatchHead of
                        {error, _} -> 
                            MatchHead;
                        _ ->
                            eval_param_match(
                                {tuple, L_Line, tl(LTupleList)}, 
                                {tuple, tl(RTupleList)},
                                MatchHead,
                                World
                            )
                    end
            end;
        _ ->
            EvalLHS = eval:eval_expr(LHS, [], World),
            case EvalLHS of
                {ok, RHS, NewBindings} ->
                    orddict:merge(
                        fun(_, V, _) -> V end,
                        NewBindings,
                        BindingsAcc
                    );
                _ ->
                    {error, {badmatch, RHS}}
            end
    end.