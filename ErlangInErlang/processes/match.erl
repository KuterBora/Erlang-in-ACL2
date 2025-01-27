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