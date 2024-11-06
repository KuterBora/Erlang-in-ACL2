-module(match).

-export([eval_match/4, match_tuple/4]).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%  Evaluate Match
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% TODO: should not need world in match, as it cannot make function calls on LHS?

% TODO: comma seperated lists matching: [1, A, 3] = [1, 2, 3].

% Plan: 
% test what cases are not working

% change tuple representation to {tuple, []} instead of {tuple, {}} which makes 
% implementation easier
% rewrite match tuple, and put the calls to it inside the main match

% OR, same thing except make match take in unevaluated RHS. This seems more rigorous

% clean up match


% Given a match statement, if the left hand side is an unbound
% variable, assigns the value of the right hand side to that variable
% and adds it to the Bindings. Otherwise, asserts that the left hand side
% is equal to the right hand side.
% returns {ok, term(), NewBindings} | {error, string()}

% Evaluate matches of ASTs on the left hand side to terms on the right side
eval_match({var, _, '_'}, RHS, Bindings, _) ->
    {ok, RHS, Bindings};
eval_match({var, _, LHS}, RHS, Bindings, _) ->
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

% {cons var var} = term()
eval_match({cons, _, {var, _, Hd}, {var, _, Tl}}, RHS, Bindings, _) ->
    case RHS of
        {RHS_Type, RHS_Value} when RHS_Type /= nil ->
            RHS_Head = hd(RHS_Value),
            RHS_Tail = tl(RHS_Value),
            Hd_is_key = orddict:is_key(Hd, Bindings),
            Tl_is_key = orddict:is_key(Tl, Bindings),
            if
                Hd == '_' andalso Tl == '_' ->
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                Hd_is_key andalso Tl_is_key ->
                    Head_Value = orddict:fetch(Hd, Bindings),
                    {TailType, Tail_Value} = orddict:fetch(Tl, Bindings),
                    case {Head_Value, Tail_Value, TailType} of
                        {RHS_Head, RHS_Tail, RHS_Type} -> 
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                        {RHS_Head, RHS_Tail, nil} -> 
                            {ok, {RHS_Type, [RHS_Head]}, Bindings};
                        _ -> {error, "No match of right hand side value 10."}
                    end;
                Hd_is_key andalso Tl /= '_' ->
                    Head_Value = orddict:fetch(Hd, Bindings),
                    case {Head_Value, RHS_Tail} of
                        {RHS_Head, []} ->
                            Tl_to_Bindings = orddict:store(Tl, {nil, RHS_Tail}, Bindings),
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_to_Bindings};
                        {RHS_Head, _} -> 
                            Tl_to_Bindings = orddict:store(Tl, {RHS_Type, RHS_Tail}, Bindings),
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_to_Bindings};
                        _ -> {error, "No match of right hand side value 9."}
                    end;
                Tl_is_key andalso Hd /= '_' ->
                    {TailType, Tail_Value} = orddict:fetch(Tl, Bindings),
                    Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
                    case {Tail_Value, TailType} of
                        {RHS_Tail, RHS_Type} -> 
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Hd_to_Bindings};
                        {RHS_Tail, nil} -> 
                            {ok, {RHS_Type, [RHS_Head]}, Hd_to_Bindings};
                        _ -> {error, "No match of right hand side value 8."}
                    end;
                Hd_is_key andalso Tl == '_' ->
                    Head_Value = orddict:fetch(Hd, Bindings),
                    case Head_Value of
                        RHS_Head -> {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                        _ -> {error, "No match of right hand side value 7."}
                    end;
                Tl_is_key andalso Hd == '_' ->
                    {TailType, Tail_Value} = orddict:fetch(Tl, Bindings),
                    case {Tail_Value, TailType} of
                        {RHS_Tail, RHS_Type} -> 
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                        {RHS_Tail, nil} -> 
                            {ok, {RHS_Type, [RHS_Head]}, Bindings};
                        _ -> {error, "No match of right hand side value 6."}
                    end;
                Hd == '_' andalso RHS_Tail == [] ->
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                Hd == '_' ->
                    Tl_to_Bindings = orddict:store(Tl, {RHS_Type, RHS_Tail}, Bindings),
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_to_Bindings};
                Tl == '_' ->
                    Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Hd_to_Bindings};
                RHS_Tail == [] ->
                    Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
                    Tl_to_Bindings = orddict:store(Tl, {nil, RHS_Tail}, Hd_to_Bindings),
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_to_Bindings};
                true ->
                    Hd_to_Bindings = orddict:store(Hd, RHS_Head, Bindings),
                    Tl_to_Bindings = orddict:store(Tl, {RHS_Type, RHS_Tail}, Hd_to_Bindings),
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_to_Bindings}
            end;
        _ -> {error, "illegal pattern 1."}
    end;

% TODO: nil case?

% TODO, nil case? variable in head case?
% {cons term() var} = term()
eval_match({cons, _, Hd, {var, _, Tl}}, RHS, Bindings, World) ->
    case RHS of
        {RHS_Type, RHS_Value} when RHS_Type /= nil->
            RHS_Head = hd(RHS_Value),
            RHS_Tail = tl(RHS_Value),
            Eval_LHS_Head = eval_match(Hd, RHS_Head, Bindings, World),
            case Eval_LHS_Head of
                {ok, LHS_Head, Hd_Bindings} ->
                    IsKey = orddict:is_key(Tl, Bindings),
                    if
                        RHS_Head == LHS_Head andalso IsKey ->
                            Value = orddict:fetch(Tl, Bindings),
                            case Value of
                                {RHS_Type, RHS_Tail} -> 
                                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Hd_Bindings};
                                {nil, RHS_Tail} -> 
                                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Hd_Bindings};
                                _ -> {error, "No match of right hand side value 5."}
                            end;
                        RHS_Head == LHS_Head andalso Tl == '_' ->
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Hd_Bindings};
                        RHS_Head == LHS_Head andalso RHS_Tail == [] ->
                            NewBindings = orddict:store(Tl, {nil, RHS_Tail}, Hd_Bindings),
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, NewBindings};
                        RHS_Head == LHS_Head ->
                            NewBindings = orddict:store(Tl, {RHS_Type, RHS_Tail}, Hd_Bindings),
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, NewBindings};
                        true ->
                            {error, "No match of right hand side value 4."}
                    end;
                _ -> {error, "illegal pattern 2."}
            end;
        _ -> {error, "illegal pattern 3."}
    end;

% TODO
% {cons var term()} = term()
eval_match({cons, _, {var, _, Hd}, {nil, _}}, RHS, Bindings, _) ->
    case RHS of
        {RHS_Type, RHS_Value} when RHS_Type /= nil->
            RHS_Head = hd(RHS_Value),
            RHS_Tail = tl(RHS_Value),

            %io:format("\nTail is: ~p", [Tl]),
            %io:format("\nRHS_Tail: ~p", [RHS_Tail]),
            %io:format("\nEval_LHS: ~p", [Eval_LHS]),
            % what if Eval_LHS is a cons that has vars in it?
            % instead of eval, call match with Tl and RHS Tail
            IsKey = orddict:is_key(Hd, Bindings),
            if
                RHS_Tail == [] andalso IsKey ->
                    Value = orddict:fetch(Hd, Bindings),
                    case Value of
                        RHS_Head -> 
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                        _ -> {error, "No match of right hand side value 1."}
                    end;
                RHS_Tail == [] andalso Hd == '_' ->
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Bindings};
                RHS_Tail == [] ->
                    NewBindings = orddict:store(Hd, RHS_Head, Bindings),
                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, NewBindings};
                true ->
                    {error, "No match of right hand side value 2."}
            end;
        _ -> {error, "illegal pattern 5."}
    end;


% {cons var term()} = term()
eval_match({cons, _, {var, _, Hd}, Tl}, RHS, Bindings, World) ->
    case RHS of
        {RHS_Type, RHS_Value} when RHS_Type /= nil->
            RHS_Head = hd(RHS_Value),
            RHS_Tail = tl(RHS_Value),

            %io:format("\nTail is: ~p", [Tl]),
            %io:format("\nRHS_Tail: ~p", [RHS_Tail]),

            Eval_LHS = eval_match(Tl, {RHS_Type, RHS_Tail}, Bindings, World),
            %io:format("\nEval_LHS: ~p", [Eval_LHS]),
            % what if Eval_LHS is a cons that has vars in it?
            % instead of eval, call match with Tl and RHS Tail
            case Eval_LHS of
                {ok, {LHS_Type, LHS_Tail}, Tl_Bindings} when LHS_Type == RHS_Type orelse LHS_Type == nil ->
                    IsKey = orddict:is_key(Hd, Bindings),
                    if
                        RHS_Tail == LHS_Tail andalso IsKey ->
                            Value = orddict:fetch(Hd, Bindings),
                            case Value of
                                RHS_Head -> 
                                    {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_Bindings};
                                _ -> {error, "No match of right hand side value 1."}
                            end;
                        RHS_Tail == LHS_Tail andalso Hd == '_' ->
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, Tl_Bindings};
                        RHS_Tail == LHS_Tail ->
                            NewBindings = orddict:store(Hd, RHS_Head, Tl_Bindings),
                            {ok, {RHS_Type, [RHS_Head | RHS_Tail]}, NewBindings};
                        true ->
                            {error, "No match of right hand side value 2."}
                    end;
                _ -> {error, "illegal pattern 4."}
                end;
        _ -> {error, "illegal pattern 5."}
    end;

% TODO
eval_match({cons, _, Hd, {nil, _}}, {cons, RHS}, Bindings, World) ->
    Match_Hd = eval_match(Hd, hd(RHS), Bindings, World),
    case Match_Hd of
        {ok, _, Hd_NewBindings} ->
            {ok, {cons, RHS}, Hd_NewBindings};
        _ -> {error, "illegal pattern 72."}
    end;

% TODO
eval_match({cons, _, Hd, Tl}, {cons, RHS}, Bindings, World) ->
    Match_Hd = eval_match(Hd, hd(RHS), Bindings, World),
    io:format("\nmatch head: ~p", [Match_Hd]),
    case Match_Hd of
        {ok, _, Hd_NewBindings} ->
            %io:format("\n RHS tail is: ~p", [tl(RHS)]),
            Match_Tl = eval_match(Tl, {cons, tl(RHS)}, Hd_NewBindings, World),
            %io:format("\n Match_Tl is: ~p", [Match_Tl]),
            case Match_Tl of
                {ok, _, Tl_NewBindings} ->
                    {ok, {cons, RHS}, Tl_NewBindings};
                _ -> {error, "illegal pattern 6."}
            end;
        _ -> {error, "illegal pattern 7."}
    end;

    % what id Tl is nil?
    % also need to checl for size equality of the two lists
    % match Hd to RHS car to recieve Hd_NewBindings
    % match Tl to RHS cdr with Hd_NewBindings to obtain Tl_NewBindings
    % return {ok, RHS, Tl_NewBindings}

%{match, _, {cons, _, {cons, _, Exp1}, {cons, _, Exp2}}, ExpRHS} ->
%{match, _, {cons, _, {cons, _, }, Exp1}, ExpRHS} ->
%{match, _, {cons, _, Exp1, {cons}}, ExpRHS} ->

% {cons {cons AST} {cons AST}} = term()

% {cons {cons AST} AST} = 

% tuple?
% term() = term()
eval_match(Exp1, RHS, Bindings, World) ->
    % TODO: this has to be matched too
    io:format("\nExp1: ~p", [Exp1]),
    io:format("\nBindings: ~p", [Bindings]),
    Eval_LHS = eval:eval_expr(Exp1, Bindings, World),
    io:format("\nEval LHS: ~p", [Eval_LHS]),
    case {Eval_LHS, RHS} of
        {{ok, LHS, NewBindings}, RHS} when LHS == RHS ->
            {ok, RHS, NewBindings};
        {{ok, _, _}, _} ->
            {error, "No match of right hand side value 3."};
        _ -> {error, "illegal pattern 8."}
    end.



% TODO: descriptions of the functions below

match_tuple(TupleList, {tuple, RHS_Line, RHS_List}, Bindings, World) ->
    NewBindings = match_tuple_vars(TupleList, RHS_List, Bindings, World),
    RHS = eval:eval_expr({tuple, RHS_Line, RHS_List}, Bindings, World),
    case {RHS, NewBindings} of
        {{error, _}, _} -> {error, "illegal pattern 9."};
        {_, {error, _}} -> NewBindings;
        {{ok, RHS_Value, _}, _} -> {ok, RHS_Value, NewBindings};
        _ -> {error, "illegal pattern 10."}
    end.

% {tuple, list()} = term()
match_tuple_vars([], [], Bindings, _) -> Bindings;
match_tuple_vars([LHS_First | LHS_Rest], [RHS_First | RHS_Rest], Bindings, World) ->
    Eval_RHS_First = eval:eval_expr(RHS_First, Bindings, World),
    % TODO: what if LHS is a tuple?
    case {Eval_RHS_First, LHS_First} of
        {{ok, _, _}, {tuple, _, TupleList}} ->
            Eval_Tuple = match_tuple(TupleList, RHS_First, Bindings, World),
            case Eval_Tuple of
                {ok, _, NewBindings} -> match_tuple_vars(LHS_Rest, RHS_Rest, NewBindings, World);
                _ -> {error, "illegal pattern 11."}
            end;
        {{ok, RHS_Value, _}, _} ->
            Eval_Match = eval_match(LHS_First, RHS_Value, Bindings, World),
            case Eval_Match of
                {ok, _, NewBindings} -> match_tuple_vars(LHS_Rest, RHS_Rest, NewBindings, World);
                _ -> Eval_Match
            end;
        _ -> {error, "Failed to evaluate right hand side."}
    end;
match_tuple_vars(_, _, _, _) -> {error, "illegal pattern 12."}.