-module(match).

-export([eval_match/7]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Evaluate macthing LHS to RHS. Update Bindings if necessary.
% Throw a badmatch error if match is not sucessful.
eval_match(LHS, RHS, Bindings, Out, ProcState, World, K) ->
    case {LHS, RHS} of
        {{var, _, '_'}, _} -> 
            cps:applyK(RHS, Bindings, Out, ProcState, World, K);
        {{var, _, Var}, _} ->
            case orddict:is_key(Var, Bindings) of
                true ->
                    case orddict:fetch(Var, Bindings) of
                        RHS -> 
                            cps:applyK(
                                RHS,
                                Bindings,
                                Out,
                                ProcState,
                                World,
                                K
                            );
                        _ -> 
                            cps:errorK(
                                {badmatch, RHS},
                                Out,
                                ProcState,
                                World,
                                K
                            )
                    end;
                _ ->
                    cps:applyK(
                        RHS,
                        orddict:store(Var, RHS, Bindings),
                        Out,
                        ProcState,
                        World,
                        K
                    )
            end;
        {{cons, _, LHSHd, LHSTl}, {cons, RHSList}} when RHSList /= [] ->
            case LHSTl of
                {nil, _} when tl(RHSList) == [] ->
                    eval_match(
                        LHSHd,
                        hd(RHSList),
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        {match_cons_nil_k, K});
                _ ->
                    eval_match(
                        LHSHd,
                        hd(RHSList),
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        {
                            match_cons_k,
                            LHSTl,
                            {cons,
                            tl(RHSList)},
                            Bindings,
                            K
                        }
                    )
            end;
        {{cons, _, _, _}, {cons, _}} ->
            cps:errorK({badmatch, RHS}, Out, ProcState, World, K);
        {{tuple, Line, LTupleList}, {tuple, RTupleList}} 
            when length(LTupleList) == length(RTupleList) ->  
            case {LTupleList, RTupleList} of
                {[], []} ->
                    cps:applyK(
                        {tuple, []},
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        K
                    );
                _ ->
                    eval_match(
                        hd(LTupleList),
                        hd(RTupleList),
                        Bindings,
                        Out,
                        ProcState,
                        World,
                        {
                            match_tuple_k,
                            {tuple, Line, tl(LTupleList)},
                            {tuple, tl(RTupleList)},
                            Bindings,
                            K
                        }
                    )
            end;
        {{tuple, _, _}, {tuple, _}} ->
            cps:errorK({badmatch, RHS}, Out, ProcState, World, K);
        _ ->
            eval:eval_expr(
                LHS,
                Bindings,
                Out,
                ProcState,
                World,
                {match_lhs_k, RHS, K}
            )
    end.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Function Parameter Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Return the Bindings obtained by macthing LHS to RHS.
% Throw a badmatch error if match is not sucessful.
% eval_param_match(LHS, RHS, BindingsAcc, Out, ProcState, World) ->
%     case {LHS, RHS} of
%         {{var, _, '_'}, _} -> 
%             BindingsAcc; 
%         {{var, _, Var}, _} -> 
%             orddict:store(Var, RHS, BindingsAcc);
%         {{cons, _, LHS_Hd, LHS_Tl}, {cons, RHS_List}} ->
%             MatchHead = 
%                 eval_param_match(
%                     LHS_Hd,
%                     hd(RHS_List),
%                     BindingsAcc,
%                     Out, ProcState, World
%                 ),
%             case MatchHead of
%                 {error, _} ->
%                     MatchHead;
%                 _ ->
%                     case LHS_Tl of
%                         {nil, _} when tl(RHS_List) == [] ->
%                             MatchHead;
%                         _ ->
%                             eval_param_match(
%                                 LHS_Tl,
%                                 {cons, tl(RHS_List)},
%                                 MatchHead,
%                                 Out, ProcState, World
%                             )
%                     end
%             end;
%         {{tuple, L_Line, LTupleList}, {tuple, RTupleList}} ->
%             case {LTupleList, RTupleList} of
%                 {[], []} -> 
%                     BindingsAcc;
%                 _ ->
%                     MatchHead = 
%                         eval_param_match(
%                             hd(LTupleList),
%                             hd(RTupleList), 
%                             BindingsAcc,
%                             Out, ProcState, World
%                         ),
%                     case MatchHead of
%                         {error, _} -> 
%                             MatchHead;
%                         _ ->
%                             eval_param_match(
%                                 {tuple, L_Line, tl(LTupleList)}, 
%                                 {tuple, tl(RTupleList)},
%                                 MatchHead,
%                                 Out, ProcState, World
%                             )
%                     end
%             end;
%         _ ->
%             EvalLHS = eval:eval_expr(LHS, [], Out, ProcState, World),
%             case EvalLHS of
%                 {ok, RHS, NewBindings} ->
%                     orddict:merge(
%                         fun(_, V, _) -> V end,
%                         NewBindings,
%                         BindingsAcc
%                     );
%                 _ ->
%                     {error, {badmatch, RHS}}
%             end
%     end.