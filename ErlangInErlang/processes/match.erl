-module(match).

-export([eval_match/6, eval_param_match/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate macthing LHS to RHS. Update Bindings if necessary.
% Throw a bad_match error if match is not sucessful.
eval_match(LHS, RHS, Bindings, OutBox, ProcState, World) ->
    case {LHS, RHS} of
        {{var, _Line, '_'}, _} -> 
            {ok, RHS, Bindings, OutBox};
        {{var, _Line, Var}, _} ->
            case orddict:is_key(Var, Bindings) of
                true ->
                    case orddict:fetch(Var, Bindings) of
                        RHS -> 
                            {ok, RHS, Bindings, OutBox};
                        _ -> 
                            {error, {badmatch, RHS}, OutBox}
                    end;
                _ ->
                    {ok, RHS, orddict:store(Var, RHS, Bindings), OutBox}
            end;
        {{cons, _Line, LHS_Hd, LHS_Tl}, {cons, RHS_List}} ->
            MatchHead = eval_match(LHS_Hd, hd(RHS_List), Bindings, OutBox, ProcState, World),
            case MatchHead of
                {ok, _HVal, HdBindings, HdOutBox} ->
                    case LHS_Tl of
                        {nil, _} when tl(RHS_List) == [] ->
                            {ok, RHS, HdBindings, HdOutBox};
                        _ ->
                            MatchTail = 
                                eval_match(
                                    LHS_Tl,
                                    {cons, tl(RHS_List)},
                                    HdBindings,
                                    HdOutBox,
                                    ProcState,
                                    World
                                ),
                            case MatchTail of
                                {ok, _TVal, TlBindings, TlOutBox} ->
                                    {ok, RHS, TlBindings, TlOutBox};
                                {yield, _, _, _} ->
                                    {error, illegal_pattern};
                                _ ->
                                    MatchTail
                            end
                    end;
                {yield, _, _, _} ->
                    {error, illegal_pattern};
                _ ->
                    MatchHead
            end;
        {{tuple, Line, LTupleList}, {tuple, RTupleList}} ->
            case {LTupleList, RTupleList} of
                {[], []} ->
                    {ok, {tuple, {}}, Bindings, OutBox};
                _ ->
                    MatchHead = 
                        eval_match(
                            hd(LTupleList),
                            hd(RTupleList),
                            Bindings,
                            OutBox,
                            ProcState,
                            World
                        ),
                    case MatchHead of
                        {ok, _HVal, HdBindings, HdOutBox} ->
                            MatchTail =
                                eval_match(
                                  {tuple, Line, tl(LTupleList)},
                                  {tuple, tl(RTupleList)},
                                  HdBindings,
                                  HdOutBox,
                                  ProcState,
                                  World
                                ),
                            case MatchTail of
                                {ok, _TVal, TlBindings, TlOutBox} ->
                                    {ok, {tuple, RTupleList}, TlBindings, TlOutBox};
                                {yield, _, _, _} ->
                                    {error, illegal_pattern};
                                _ ->
                                    MatchTail
                            end;
                        {yield, _, _, _} ->
                            {error, illegal_pattern};
                        _ ->
                            MatchHead
                    end
            end;
        _ ->
            EvalLHS = eval:eval_expr(LHS, Bindings, OutBox, ProcState, World),
            case EvalLHS of
                {ok, RHS, NewBindings, NewOutBox} -> 
                    {ok, RHS, NewBindings, NewOutBox};
                {ok, _, _, NewOutBox} -> 
                    {error, {badmatch, RHS}, NewOutBox};
                {yield, _, _, _} ->
                    {error, illegal_pattern};
                _ ->
                    EvalLHS
            end
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Parameter Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return the Bindings obtained by macthing LHS to RHS.
% Throw a bad_match error if match is not sucessful.
% remark: no yield can be thrown
eval_param_match(LHS, RHS, BindingsAcc, ProcState, World) ->
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
                    ProcState,
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
                                ProcState,
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
                            ProcState,
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
                                ProcState,
                                World
                            )
                    end
            end;
        _ ->
            EvalLHS = eval:eval_expr(LHS, [], procs:empty_box(), ProcState, World),
            case EvalLHS of
                {ok, RHS, NewBindings, _} ->
                    orddict:merge(
                        fun(_, V, _) -> V end,
                        NewBindings,
                        BindingsAcc
                    );
                {yield, _, _, _} ->
                    {error, illegal_pattern};
                _ ->
                    {error, {badmatch, RHS}, procs:empty_box()}
            end
    end.