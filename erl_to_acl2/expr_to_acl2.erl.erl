-module(expr_to_acl2).
-export([tesst/1, expr_to_lisp/1, exprs_to_lisp/1, clause_list_to_lisp/1, clause_to_lisp/1]).

%% indentation is not supported. There is only some for debugging purposes.

test(AST) ->
    io:format(
        "AST:\n ~p~nResult:~n~s",
        [get_AST(AST), exprs_to_lisp(get_AST(AST))]).

get_AST(Str) ->
    {ok, Tokens, _} = erl_scan:string(Str),
    {ok, AST} = erl_parse:parse_exprs(Tokens),
    AST.

exprs_to_lisp([]) -> "nil";
exprs_to_lisp([AST]) -> "(" ++ expr_to_lisp(AST) ++ ")";
exprs_to_lisp(ASTs) -> "(" ++ exprs_to_lisp0(ASTs) ++ ")".

exprs_to_lisp0([]) -> "";
exprs_to_lisp0([AST]) -> expr_to_lisp(AST);
exprs_to_lisp0([Hd | Tl]) ->
    expr_to_lisp(Hd) ++ "\n  " ++ exprs_to_lisp0(Tl).

clause_list_to_lisp([]) -> "nil";
clause_list_to_lisp([Cl]) -> clause_to_lisp(Cl);
clause_list_to_lisp([Hd | Tl]) ->
    clause_to_lisp(Hd) ++ clause_list_to_lisp(Tl).

expr_to_lisp(Expr) ->
    case Expr of
        {integer, _, V} ->
            "(:integer " ++ integer_to_list(V) ++ ")";
        {atom, _, V} ->
            "(:atom " ++ atom_to_list(V) ++ ")";
        {string, _, V} ->
            "(:string \"" ++ V ++ "\")";
        {nil, _} ->
            "(:nil)";
        {'fun', _, {clauses, Cls}} ->
            "(:fun\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        {cons, _, Hd, Tl} ->
            "(:cons "++ expr_to_lisp(Hd) ++ " \n  " ++ expr_to_lisp(Tl) ++ ")";
        {tuple, _, ExprList} ->
            "(:tuple\n  "
                ++ expr_to_lisp(normalize_expr_list(ExprList))
                ++")";
        {var, _, Id} ->
            "(:var " ++ atom_to_list(Id) ++ ")";
        {op, _, Op, Expr1} ->
            "(:unop " ++ atom_to_list(Op) ++ " "
            ++ expr_to_lisp(Expr1) ++ ")";
        {op, _, Op, Expr1, Expr2} ->
            "(:binop " ++ atom_to_list(Op) ++ " "
            ++ expr_to_lisp(Expr1) ++ " "
            ++ expr_to_lisp(Expr2) ++ ")";
        {match, _, Expr1,  Expr2} ->
            "(:match "
            ++ expr_to_lisp(Expr1) ++ " "
            ++ expr_to_lisp(Expr2) ++ ")";
        {'if', _, Cls} ->
            "(:if\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        {'case', _, Expr1, Cls} ->
            "(:case-of " ++ expr_to_lisp(Expr1)
            ++  "\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        {call, _, {atom, _, Fn}, Args} ->
            "(:call " ++ atom_to_list(Fn) ++ " "
            ++ expr_to_lisp(normalize_expr_list(Args)) ++ ")";
        {call, _, {remote, _, {atom, _, Mod}, {atom, _, Fn}}, Args} ->
            "(:remote-call " ++ atom_to_list(Mod) ++ " " ++ atom_to_list(Fn) ++ " "
            ++ expr_to_lisp(normalize_expr_list(Args)) ++ ")";
        {call, _, Expr1, Args} ->
            "(:fun-call " ++ expr_to_lisp(Expr1) ++ " "
            ++ expr_to_lisp(normalize_expr_list(Args)) ++ ")";
        {'receive', _, Cls} ->
            "(:receive\n  (" ++ clause_list_to_lisp(Cls) ++ "))";
        _ -> "(:reject)"
    end.

normalize_expr_list([]) -> {nil, 1};
normalize_expr_list([Hd | Tl]) ->
    {cons, 1, Hd, normalize_expr_list(Tl)}.

guards_to_lisp([]) -> "";
guards_to_lisp([Hd | Tl]) ->
    exprs_to_lisp(Hd) ++ guards_to_lisp(Tl).

clause_to_lisp(Cl) ->
    case Cl of
        {clause, _, [], [], Exprs} ->
            "((cases)\n   (guards)\n    "
            ++ "(body " ++ exprs_to_lisp(Exprs) ++ "))\n";
        {clause, _, Cases, [], Exprs} ->
            "((cases " ++ exprs_to_lisp0(Cases) ++ ")"
            ++ "\n   (guards)"
            ++ "\n   (body " ++ exprs_to_lisp0(Exprs) ++ "))\n";
        {clause, _, [], Guards, Exprs} ->
            "((cases)\n   "
            ++ "(guards " ++ guards_to_lisp(Guards) ++ ")\n   "
            ++ "(body " ++ exprs_to_lisp0(Exprs) ++ "))\n";
    
        {clause, _, Cases, Guards, Exprs} ->
            "((cases " ++ exprs_to_lisp0(Cases) ++ ")\n   "
            ++ "(guards " ++ guards_to_lisp(Guards) ++ ")\n   "
            ++ "(body " ++ exprs_to_lisp0(Exprs) ++ "))\n"
    end.


