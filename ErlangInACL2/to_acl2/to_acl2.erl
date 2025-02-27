-module(to_acl2).


exprs_to_acl2(ASTs) ->
    case ASTs of
        [] ->
            todo;
        [Hd | Tl] ->
            todo
    end.


expr_to_acl2(AST) ->
    case AST of
        {atom, Line, Value} -> 
            todo;
        {nil, Line} -> 
            todo;
        {integer, Line, Value} -> 
            todo;
        {string, Line, Value} -> 
            todo;
        {cons, Line, Car, Cdr} ->
            todo;
        {tuple, Line, TupleList} -> 
            todo;
        {var, Line, Var} -> 
            todo;
        {'fun', Line, {clauses, Clauses}} -> 
            todo;
        {match, Line, Expr1, Expr2} ->
            todo;
        {op, Line, Op, Expr} ->
            todo;
        {op, Line, Op, Expr1, Expr2} -> 
            todo;
        {'if', Line, Clasues} -> 
            todo;
        {'case', Line, Arg, Clauses} ->
            todo;
        {'call', _Line, Call, Args} ->
            todo;
        _ -> 
            {error, bad_AST}
    end.


tupleList_to_alc2(TupleList) ->
    case TupleList of
        [] ->
            todo;
        [Hd | Tl] ->
            todo;
    end.

clause_to_acl2(Clause) ->
    todo.