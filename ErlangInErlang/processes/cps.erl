-module(cps).
-export([applyK/6, errorK/5]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% CPS Implementation
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Apply the given continutation K to Result with the given Bindings
applyK(Result, Bindings, Out, ProcState, World, K) ->
    case K of
        {initial_k} ->
            {ok, Result, Bindings};
        {exprs_k, ASTs, ExprsK} ->
            (
                fun(_PrevResult, PrevBindings) ->
                    eval:eval_exprs(
                        ASTs,
                        PrevBindings,
                        Out,
                        ProcState,
                        World,
                        ExprsK
                    )
                end
            )(Result, Bindings);
        {cons_cdr_k, Cdr, Bindings0, ConsK} ->
            (
                fun(CarResult, CarBindings) ->
                    eval:eval_expr(
                        Cdr,
                        Bindings0,
                        Out,
                        ProcState,
                        World,
                        {cons_merge_k, CarResult, CarBindings, ConsK}
                    )
                end
            )(Result, Bindings);
        {cons_merge_k, CarResult, CarBindings, ConsK} ->
            (
                fun(CdrResult, CdrBindings) ->
                    NewBindigs =
                        orddict:merge(
                            fun(_, V, _) ->
                                V
                            end,
                            CarBindings,
                            CdrBindings
                        ),
                    eval:eval_list(
                        CarResult,
                        CdrResult,
                        NewBindigs,
                        Out,
                        ProcState,
                        World,
                        ConsK
                    )
                end
            )(Result, Bindings);
        {tuple_cdr_k, TupleCdr, Bindings0, TupleK} ->
            (
                fun(CarResult, CarBindings) ->
                    eval:eval_expr(
                        TupleCdr,
                        Bindings0,
                        Out,
                        ProcState,
                        World,
                        {tuple_merge_k, CarResult, CarBindings, TupleK}
                    )
                end
            )(Result, Bindings);
        {tuple_merge_k, CarResult, CarBindings, TupleK} ->
            (
                fun(CdrResult, CdrBindings) ->
                    NewBindigs =
                        orddict:merge(
                            fun(_, V, _) ->
                                V
                            end,
                            CarBindings,
                            CdrBindings
                        ),
                    eval:eval_tuple(
                        CarResult,
                        CdrResult,
                        NewBindigs,
                        Out,
                        ProcState,
                        World,
                        TupleK
                    )
                end
            )(Result, Bindings);
        {match_k, Expr, MatchK} ->
            (
                fun(RHS, RHSBindings) ->
                    match:eval_match(
                        Expr,
                        RHS,
                        RHSBindings,
                        Out,
                        ProcState,
                        World,
                        MatchK
                    )
                end
            )(Result, Bindings);
        {match_cons_k, LHSTl, RHSTl, Bindings0, MatchK} ->
            (
                fun(HdResult, HdBindings) ->
                    match:eval_match(
                        LHSTl,
                        RHSTl,
                        Bindings0,
                        Out,
                        ProcState,
                        World,
                        {cons_merge_k, HdResult, HdBindings, MatchK}
                    )
                end
            )(Result, Bindings);
        {match_cons_nil_k, MatchK} ->
            applyK(
                {cons, [Result]},
                Bindings,
                Out,
                ProcState,
                World,
                MatchK
            );
        {match_tuple_k, LHSTl, RHSTl, Bindings0, MatchK} ->
            (
                fun(HdResult, HdBindings) ->
                    match:eval_match(
                        LHSTl,
                        RHSTl,
                        Bindings0,
                        Out,
                        ProcState,
                        World,
                        {tuple_merge_k, HdResult, HdBindings, MatchK}
                    )
                end
            )(Result, Bindings);
        {match_lhs_k, RHS, MatchK} ->
            (
                fun(LHS, NewBindigs) ->
                    case LHS of
                        RHS ->
                            applyK(
                                LHS,
                                NewBindigs,
                                Out,
                                ProcState,
                                World,
                                MatchK
                            );
                        _ ->
                            errorK(
                                {badmatch, RHS},
                                Out,
                                ProcState,
                                World,
                                MatchK
                            )
                    end
                end
            )(Result, Bindings);
        {op1_k, Op, OpK} ->
            (
                fun(Operand, OpBindings) ->
                    eval:eval_op(
                        Op,
                        Operand,
                        OpBindings,
                        Out,
                        ProcState,
                        World,
                        OpK
                    )
                end
            )(Result, Bindings);
        {op2_expr1_k, Op, Expr2, Bindings0, OpK} ->
            (
                fun(Result1, Bindings1) ->
                    eval:eval_expr(
                        Expr2, 
                        Bindings0,
                        Out,
                        ProcState,
                        World,
                        {op2_expr2_k, Op, Result1, Bindings1, OpK}
                    )
                end
            )(Result, Bindings);
        {op2_expr2_k, Op, Result1, Bindings1, OpK} ->
            (
                fun(Result2, Bindings2) ->
                    NewBindigs =
                        orddict:merge(
                            fun(_, V, _) ->
                                V
                            end,
                            Bindings1,
                            Bindings2
                        ),
                    eval:eval_op(
                        Op,
                        Result1,
                        Result2,
                        NewBindigs, 
                        Out,
                        ProcState,
                        World,
                        OpK
                    )
                end
            )(Result, Bindings);
        {guard_k, Guards, Bindings0, GuardK} ->
            (
                fun(GuardResult, _) ->
                    case GuardResult of
                        {atom, true} ->
                            cases:eval_guards(
                                Guards,
                                Bindings0,
                                Out,
                                ProcState,
                                World,
                                GuardK
                            );
                        _ ->
                            applyK(
                                {atom, false},
                                Bindings0,
                                Out,
                                ProcState,
                                World,
                                GuardK   
                            )
                    end
                end 
            )(Result, Bindings);
        {if_k, Body, Bindings0, TlClauses, IfK} ->
            (
                fun(GuardsResult, _) ->
                    case GuardsResult of
                        {atom, true} ->
                            eval:eval_exprs(
                                Body,
                                Bindings0,
                                Out,
                                ProcState,
                                World,
                                IfK
                            );
                        _ ->
                            cases:eval_if(
                                TlClauses,
                                Bindings0,
                                Out,
                                ProcState,
                                World,
                                IfK
                            )
                    end
                end
            )(Result, Bindings);
        {case_value_k, Clauses, CaseK} ->
            (
                fun(Value, NewBindigs) ->
                    cases:eval_case(
                      Value,
                      Clauses,
                      NewBindigs,
                      Out,
                      ProcState,
                      World,
                      CaseK  
                    )
                end
            )(Result, Bindings);
        {case_match_k, Value, GList, Body, Bindings0, TlCls, CaseK} ->
            (
                fun(_, MBindings) ->
                    cases:eval_guards(
                        case GList of
                            [] -> 
                                GList;
                            [Guards] -> 
                                Guards;
                            _ ->
                                {error, illegal_guard}
                        end,
                        MBindings,
                        Out,
                        ProcState,
                        World,
                        {
                            case_guards_k,
                            Value,
                            Body,
                            MBindings,
                            Bindings0,
                            TlCls,
                            CaseK
                        }
                    )
                end    
            )(Result, Bindings);
        {case_guards_k, Value, Body, MBindings, Bindings0, TlCls, CaseK} ->
            (
                fun(GResult, _) ->
                    case GResult of
                        {atom, true} ->
                            eval:eval_exprs(
                                Body,
                                MBindings,
                                Out,
                                ProcState,
                                World,
                                CaseK    
                            );
                        _ ->
                            cases:eval_case(
                                Value,
                                TlCls,
                                Bindings0,
                                Out,
                                ProcState,
                                World,
                                CaseK    
                            )
                    end
                end    
            )(Result, Bindings);
        {call_k, Call, _Bindings0, CallK} ->
            (
                fun(Args, ArgBindings) ->
                    case Call of
                        {atom, _, FName} ->
                            functions:eval_local_call(
                                FName,
                                lists:reverse(Args),
                                ArgBindings,
                                Out,
                                ProcState,
                                World,
                                CallK
                            );
                        {remote, _, {atom, _, _MName}, {atom, _, _FName}} ->
                            % functions:eval_remote_call(
                            %     MName,
                            %     FName, 
                            %     Args,
                            %     ArgBindings,
                            %     Out, ProcState, World,
                            %     CallK
                            % );
                            todo;
                        _ ->
                            todo_fun
                    end
                end    
            )(Result, Bindings);
        {arg_next_k, Results, Bindings0, BindingsAcc, Args, ArgK} ->
            (
                fun(Arg, ArgBindings) ->
                    NewBindings =
                        orddict:merge(
                            fun(_, V, _) -> V end,
                            BindingsAcc,
                            ArgBindings
                        ),
                    case Args of
                        [] ->
                            cps:applyK(
                                [Arg| Results],
                                NewBindings,
                                Out,
                                ProcState,
                                World,
                                ArgK);
                        _ ->
                            eval:eval_expr(
                                hd(Args),
                                Bindings0,
                                Out,
                                ProcState,
                                World,
                                {
                                    arg_next_k,
                                    [Arg | Results],
                                    Bindings0,
                                    NewBindings,
                                    tl(Args),
                                    ArgK
                                }
                            )
                    end
                end    
            )(Result, Bindings);
        _ ->
            {seg_fault, bad_kont}
    end.

errorK(Exception, Out, ProcState, World, K) ->
    case K of
        {initial_k} ->
            {error, Exception};
        {exprs_k, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {cons_cdr_k, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {cons_merge_k, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {tuple_cdr_k, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {tuple_merge_k, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {match_k, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {match_cons_k, _, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {match_cons_nil_k, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {match_tuple_k, _, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {match_lhs_k, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {op1_k, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {op2_expr1_k, _, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {op2_expr2_k, _, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {guard_k, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {case_value_k, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {case_match_k, Value, _, _, Bindings0, TlClauses, ErrK}  ->
            case Exception of
                {badmatch, _} ->
                    cases:eval_case(
                        Value,
                        TlClauses,
                        Bindings0,
                        Out,
                        ProcState,
                        World,
                        ErrK    
                    );
                _ ->
                    % TODO: throw an illegal guard error maybe?
                    % or should it be a seg fault
                    {error, illegal_guard}
            end;
        {case_guards_k, _, _, _, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {call_k, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        {arg_next_k, _, _, _, _, ErrK} ->
            errorK(Exception, Out, ProcState, World, ErrK);
        _ ->
            {seg_fault, bad_kont}
    end.
