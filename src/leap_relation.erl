-module(leap_relation).
-include("leap.hrl").


-define(DEE, true).
-define(DUM, false).

-record(relation, {
    head                ::  [leap_var:var() | rva()],
    body                ::  sofs:relation()
}).
-type rva()             ::  {leap_var:var(), [leap_var:var()]}.
-type relation()        ::  #relation{} | ?DEE | ?DUM.
-type attribute()       ::  leap_var:var().

-export_type([relation/0]).



-export([cardinality/1]).
-export([dee/0]).
-export([degree/1]).
-export([dum/0]).
-export([is_empty/1]).
-export([relation/2]).
-export([rename/2]).
-export([size/1]).
-export([tuples/1]).


%% Relational Operators
-export([compose/2]).
-export([extend/3]).
-export([group_by/3]).
-export([intersect/1]).
-export([intersect/2]).
-export([join/2]).
-export([join/3]).
-export([join/4]).
-export([matching/3]).
-export([matching/4]).
-export([minus/2]).
-export([not_matching/3]).
-export([product/1]).
-export([product/2]).
-export([project/2]).
-export([restrict/2]).
-export([ungroup/2]).
-export([union/1]).
-export([union/2]).
-export([unwrap/2]).
-export([wrap/3]).





%% =============================================================================
%% API
%% =============================================================================




%% -----------------------------------------------------------------------------
%% @doc
%% A relation comprises a heading and a body. The heading is an ordered set of
%% attributes or attribute/type pairs. The body is a set of tuples with arity
%% equal to the arity of the head.
%%
%% More formally the meaning of the relation called 'foo' is that the heading
%% provides the arguments to the predicate called 'foo' and the body provides
%% a set of instances of that predicate.
%% @end
%% -----------------------------------------------------------------------------
-spec relation(tuple() | [attribute()], [tuple()]) -> relation().
relation(Head, L) when is_list(Head), is_list(L) ->
    relation(list_to_tuple(Head), L);

relation(Head, L) when is_tuple(Head), is_list(L) ->
    #relation{
        head = Head,
        body = sofs:relation(L, tuple_size(Head))
    }.


-spec dee() -> relation().
dee() ->
    ?DEE.


-spec dum() -> relation().
dum() ->
    ?DUM.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec tuples(relation()) -> [tuple()].
tuples(?DEE) ->
    [{}];

tuples(?DUM) ->
    [];

tuples(R) ->
    sofs:to_external(R#relation.body).



%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec size(relation()) -> non_neg_integer().
size(R) ->
    cardinality(R).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec is_empty(relation()) -> boolean().

is_empty(R) ->
    cardinality(R) == 0.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec cardinality(relation()) -> non_neg_integer().
cardinality(?DEE) ->
    1;

cardinality(?DUM) ->
    0;

cardinality(R) ->
    sofs:no_elements(R#relation.body).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec degree(relation()) -> non_neg_integer().
degree(?DEE) ->
    0;

degree(?DUM) ->
    0;

degree(#relation{head = H}) ->
    tuple_size(H).




%% =============================================================================
%% RELATIONAL OPERATORS
%% =============================================================================




%% -----------------------------------------------------------------------------
%% @doc
%% Let relation r not have an attribute called A. Then the expression EXTEND r 
%% : {A := exp} returns a relation with heading the heading of r extended with 
%% attribute A and body the set of all tuples t such that t is a tuple of r 
%% extended with a value for A that’s computed by evaluating exp on that tuple 
%% of r.
%% @end
%% -----------------------------------------------------------------------------
-spec extend(relation(), attribute(), function() | [function()]) -> relation().
extend(#relation{} = R, A, F) 
when ?IS_VAR(A), is_function(F, 1) orelse is_list(F) ->
    #relation{
        head = erlang:append_element(R#relation.head, A),
        body = sofs:relation([
            leap_tuples:extend(T, F) || 
            T <- sofs:to_external(R#relation.body)])
    }.



%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec group_by(relation(), leap_tuples:projection(), leap_tuples:group_by_opts()) -> relation().
group_by(#relation{} = R, Proj, Opts) ->
    relation(
        terms_to_vars(Proj), 
        leap_tuples:group_by(tuples(R), terms_to_fields(R, Proj), Opts)).



%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1, r2, …, rn (n ≥ 0) all have the same heading H. 
%% Then the expression INTERSECT {r1, r2,…, rn} returns a relation with 
%% heading H and body the set of all tuples t such that t appears in each of 
%% r1, r2, …, rn.
%% @end
%% -----------------------------------------------------------------------------
-spec intersect([relation()]) -> relation().
intersect(L) ->
    sets:size(sets:from_list([R#relation.head || R <- L])) == 1 orelse error(badarg, [L]),
    #relation{
        head = hd(L),
        body = sofs:intersection([R#relation.body || R <- L])
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1 and r2 have the same heading H. Then the expression r1 
%% INTERSECT r2 returns a relation with heading H and body the set of all 
%% tuples t such that t appears in both r1 and r2. 2. 
%% @end
%% -----------------------------------------------------------------------------
-spec intersect(relation(), relation()) -> relation().
intersect(?DUM, _) ->
    ?DUM;

intersect(_, ?DUM) ->
    ?DUM;

intersect(?DEE, _) ->
    ?DUM;

intersect(_, ?DEE) ->
    ?DUM;

intersect(#relation{head = H1, body = B1} = R1, #relation{head = H2, body = B2} = R2) ->
    H1 == H2 orelse error(badarg, [R1, R2]),
    #relation{
        head = H1,
        body = sofs:intersection(B1, B2)
    }.



%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1 and r2 be such that attributes with the same name are of the
%% same type. Then the expression r1 JOIN r2 returns a relation with heading 
%% the set theory union of the headings of r1 and r2 and body the set of all 
%% tuples t such that t is the set theory union of a tuple from r1 and a tuple 
%% from r2. 2. 
%% @end
%% -----------------------------------------------------------------------------
-spec join(relation(), relation(), map()) -> relation().
join(?DEE, R, _) ->
    R;

join(R, ?DEE, _) ->
    R;

join(?DUM, _, _) ->
    ?DUM;

join(_, ?DUM, _) ->
    ?DUM;

join(#relation{} = L, #relation{} = R, Opts) ->
    Common = sets:intersection(
        sets:from_list(tuple_to_list(L#relation.head)),
        sets:from_list(tuple_to_list(R#relation.head))
    ),
    %% We pick one
    %% We do not support joining on multiple variables
    join(L, R, hd(sets:to_list(Common)), Opts).


%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1 and r2 be such that attributes with the same name are of the
%% same type. Then the expression r1 JOIN r2 returns a relation with heading 
%% the set theory union of the headings of r1 and r2 and body the set of all 
%% tuples t such that t is the set theory union of a tuple from r1 and a tuple 
%% from r2. 2. 
%% @end
%% -----------------------------------------------------------------------------
-spec join(relation(), relation(), leap_var:var(), map()) -> relation().

join(?DEE, R, _,  _) ->
    R;

join(R, ?DEE, _, _) ->
    R;

join(?DUM, _, _, _) ->
    ?DUM;

join(_, ?DUM, _, _) ->
    ?DUM;

join(#relation{} = R1, #relation{} = R2, Var, _Opts) ->
    [R1Field] = vars_to_fields(R1, [Var]),
    [R2Field] = vars_to_fields(R2, [Var]),
    [R2Proj] = leap_tuples:project(
        [R2#relation.head], 
        vars_to_fields(R2, tuple_to_list(R2#relation.head)) -- [R2Field]),
    
    #relation{
        head = leap_tuples:append(R1#relation.head, R2Proj), 
        body = sofs:join(R1#relation.body, R1Field, R2#relation.body, R2Field)
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1, r2, …, rn (n ≥ 0) be such that attributes with the same 
%% name are of the same type. Then the expression JOIN {r1, r2, …, rn} is 
%% defined as follows: If n = 0, the result is TABLE_DEE; if n = 1, the result 
%% is r1; otherwise, choose any two distinct relations from the set 
%% r1, r2, …, rn and replace them by their dyadic join, and repeat this process 
%% until the set consists of just one relation r, which is the overall result.
%% @end
%% -----------------------------------------------------------------------------
-spec join([relation()], map()) -> relation().
join([#relation{} = R], _Opts) ->
    R;

join([A, B | T], Opts) ->
    join([join(A, B, Opts) | T], Opts);

join([], _) ->
    dee().



%% -----------------------------------------------------------------------------
%% @doc
%% Returns the semijoin of a relation i.e. a relation equal to the relation 
%% returned by the expression R1 JOIN R2, projected back on the attributes 
%% of R1.
%% @end
%% -----------------------------------------------------------------------------
matching(R1, R2, Opts) ->
    project(join(R1, R2, Opts), R1#relation.head).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns the semijoin of a relation i.e. a relation equal to the relation 
%% returned by the expression R1 JOIN R2, projected back on the attributes 
%% of R1.
%% @end
%% -----------------------------------------------------------------------------
matching(R1, R2, Var, Opts) ->
    project(join(R1, R2, Var, Opts), R1#relation.head).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec minus(relation(), relation()) -> relation().

minus(#relation{head = H1} = R1, #relation{head = H2} = R2) ->
    H1 == H2 orelse error(badarg, [R1, R2]),
    #relation{
        head = H1,
        body = sofs:difference(R1#relation.body, R2#relation.body)
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% Returns the semiminus of a relation i.e. a relation equal to the relation 
%% returned by the expression R1 MINUS (R1 MATCHING R2).
%% @end
%% -----------------------------------------------------------------------------
not_matching(R1, R2, Opts) ->
    minus(R1, matching(R1, R2, Opts)).


%% -----------------------------------------------------------------------------
%% @doc
%% Let relation r have an attribute called A and no attribute called B. 
%% Then the expression r RENAME {A AS B} returns a relation with heading 
%% identical to that of r except that attribute A in that heading is renamed B 
%% and body identical to that of r except that all references to A in that 
%% body — more precisely, in tuples in that body — are replaced by references to B. 
%% @end
%% -----------------------------------------------------------------------------
-spec rename(relation(), leap_unification:substitution()) -> relation().
rename(#relation{} = R, S) ->
    R#relation{
        head = leap_unification:apply_substitution(R#relation.head, S)
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% Let relation r have heading H, let X be a subset of H, and let A1, A2, …, An 
%% be all of the attribute names in X. Then the projection r{ A1, A2,…, An} of 
%% r on (or over) X is a relation with heading X and body consisting of all tuples 
%% x such that there exists a tuple t in r with X value x.
%% @end
%% -----------------------------------------------------------------------------
-spec project(relation(), [leap_var:var()] | tuple()) -> relation().
project(R, Vars) ->
    relation(Vars, leap_tuples:project(tuples(R), vars_to_fields(R, Vars))).




%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
restrict(#relation{} = R, MatchSpec) ->
    L = ets:match_spec_run(tuples(R), ets:match_spec_compile(MatchSpec)),
    relation(R#relation.head, L).



%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1, r2, …, rn (n ≥ 0) be such that no two of them have any 
%% attribute names in common. Then the expression TIMES {r1, r2,…, rn} returns 
%% a relation with heading the set theory union of the headings of r1, r2, …, rn
%% and body the set of all tuples t such that t is the set theory union of a 
%% tuple from r1, a tuple from r2, …, and a tuple from rn. Note: TIMES is really 
%% just a special case of JOIN, q.v.
%% @end
%% -----------------------------------------------------------------------------
-spec product([relation()]) -> relation().
product([]) ->
    dee();

product(L) ->
    Sets = [sofs:from_term(tuple_to_list(R#relation.head)) || R <- L],
    Sofs = sofs:from_sets(Sets),

    sofs:no_elements(Sofs) == length(L) 
    andalso sofs:is_empty_set(sofs:intersection(Sofs)) 
    orelse error(badarg, [L]),

    Head = leap_tuples:append([R#relation.head || R <- L]),
    Prod = sofs:product(list_to_tuple([R#relation.body || R <- L])),
    Body = sofs:projection({external, fun product_append/1}, Prod),
    #relation{
        head = Head,
        body = Body
    }.



%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1 and r2 have no attribute names in common. 
%% Then the expression r1 TIMES r2 returns a relation with heading the set theory
%% union of the headings of r1 and r2 and body the set of all tuples t such that 
%% t is the set theory union of a tuple from r1 and a tuple from r2. 2.
%% @end
%% -----------------------------------------------------------------------------
-spec product(relation(), relation()) -> relation().
product(#relation{} = R1, #relation{} = R2) ->
    sofs:is_disjoint(
        sofs:from_term(tuple_to_list(R1#relation.head)),
        sofs:from_term(tuple_to_list(R2#relation.head))
    ) orelse error(badarg, [R1, R2]),

    Head = leap_tuples:append(R1#relation.head, R2#relation.head),
    Prod = sofs:product(R1#relation.body, R2#relation.body),
    Body = sofs:projection({external, fun product_append/1}, Prod),
    #relation{
        head = Head,
        body = Body
    }.




%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec ungroup(relation(), leap_var:var() | [leap_var:var()]) -> relation().
ungroup(_R, _Vars) ->
    %% TODO use sofs
    ok.




%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1 and r2 have the same heading H. Then the expression 
%% r1 UNION r2 returns a relation with heading H and body the set of all tuples t 
%% such that t appears in either or both of r1 and r2. 
%% @end
%% -----------------------------------------------------------------------------
-spec union(relation(), relation()) -> relation().
union(R1, R2) ->
    R1#relation.head =:= R2#relation.head orelse error(badarg, [R1, R2]),

    #relation{
        head = R1#relation.head,
        body = sofs:union(R1#relation.body, R2#relation.body)
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% Let relations r1, r2, …, rn (n ≥ 0) all have the same heading H. 
%% Then the expression UNION {r1, r2,…, rn} returns a relation with heading H 
%% and body the set of all tuples t such that t appears in at least one of 
%% r1, r2, …, rn. 
%% @end
%% -----------------------------------------------------------------------------
-spec union([relation()]) -> relation().
union([]) ->
    %%Note: If n = 0, (a) some syntactic mechanism, not shown here, is needed to specify the pertinent heading, and (b) the result is the empty relation of the pertinent type.
    % TODO
    dum();

union(L) ->
    Heads = sofs:from_term([R#relation.head || R <- L]),
    sofs:no_elements(Heads) =:= 1 orelse error(badarg, [L]),

    #relation{
        head = (hd(L))#relation.head,
        body =  sofs:union(sofs:from_sets([R#relation.body || R <- L]))
    }.






%% -----------------------------------------------------------------------------
%% @doc
%% Let the heading of relation r be partitioned into subsets X = {X1, X2,…, Xm} 
%% and Y = {Y1, Y2 …, Yn}; also, let YT be an attribute name not appearing in X. 
%% Then the expression r WRAP ({ Y1, Y2,…, Yn} AS YT) returns a relation s. 
%% The heading of s is {X1, X2,…, Xm, YT}, where YT is of type TUPLE {Y1, Y2,…, Yn}. 
%% The body of s contains one tuple for each tuple in r, and no other tuples. 
%% Let tuple t of r have X value x, Y1 value y1, Y2 value y2, …, and Yn value yn; 
%5 then the corresponding tuple of s has X value x and YT value a tuple with Y1 
%% value y1, Y2 value y2, …, and Yn value yn. Note: Of the foregoing operators, 
%% the ones for which tuple analogs are defined are these: EXTEND, project, 
%% RENAME, UNION, UNWRAP, and WRAP (only).
%% If R is:
%% +----------+-----------+------+
%% |    A     |     B     |  C   |
%% +==========+===========+======+
%% | A1       | B1        | 85   |
%% | A2       | B1        | 49   |
%% | A1       | B2        | 49   |
%% | A3       | B3        | 66   |
%% | A1       | B4        | 93   |
%% +----------+-----------+------+
%% Then wrap(R, [A,C], Z) will return
%%
%% +-------------------------------+-----------+
%% | Z                             |     B     |
%% +===============================+===========+
%% | {A1, 85}                      | B1        |
%% | {A2, 49}                      | B1        |
%% | {A1, 49}                      | B2        |
%% | {A3, 66}                      | B3        |
%% | {A1, 93}                      | B4        |
%% +-------------------------------+-----------+
%% @end
%% -----------------------------------------------------------------------------
-spec wrap(relation(), tuple() | [leap_var:var()], leap_var:var()) -> relation().
wrap(R, Tuple, Var) when is_tuple(Tuple) ->
    wrap(R, tuple_to_list(Tuple), Var);

wrap(R, Vars, Var) ->
    lists:member(Var, Vars) == false orelse error(badarg, [R, Vars, Var]),
    Fields = vars_to_fields(R, Vars),
    Tuples = leap_tuples:wrap(sofs:to_external(R#relation.body), Fields),
    #relation{
        head = list_to_tuple([Var | Vars]),
        body = sofs:from_term(Tuples)
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% Let relation s have an attribute YT of type TUPLE {Y1, Y2,…, Yn}, and 
%% let X = {X1, X2,…, Xm} be all of the attributes of s other than YT; also, 
%% let no Xi have the same name as any Yj (0 ≤ i ≤ m, 0 ≤ j ≤ n). 
%% Then the expression s UNWRAP (YT) returns a relation r. The heading of r is 
%% {X1, X2,…, Xm, Y1, Y2,…, Yn}. The body of r contains one tuple for each tuple 
%% in s, and no other tuples. Let tuple t of s have X value x and YT value a tuple 
%% with Y1 value y1, Y2 value y2, …, and Yn value yn; then the corresponding tuple 
%% of r has X value x, Y1 value y1, Y2 value y2, …, and Yn value yn.
%% @end
%% -----------------------------------------------------------------------------
-spec unwrap(relation(), leap_var:var()) ->  relation().
unwrap(_R, _Var) ->
    %% TODO use sofs
    %% To do Vars will have to contain [B, {Z, {A, C}}]
    %% TODO we need to retain the Head of the wrapped tuples
    error(not_implemented).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec compose(relation(), relation()) -> relation().

compose(?DEE, R) ->
    R;

compose(R, ?DEE) ->
    R;

compose(?DUM, _) ->
    ?DUM;

compose(_, ?DUM) ->
    ?DUM;

compose(R1, R2) ->
    H1 = tuple_to_list(R1#relation.head),
    H2 = tuple_to_list(R2#relation.head),
    Vars = lists:append(lists:subtract(H1, H2), lists:subtract(H2, H1)),
    project(join(R1, R2, #{}), Vars).


%% =============================================================================
%% PRIVATE
%% =============================================================================

terms_to_vars(Tuple) when is_tuple(Tuple) ->
    leap_tuples:map(fun term_to_var/1, Tuple);

terms_to_vars(L) when is_list(L) ->
    [term_to_var(T) || T <- L].


%% @private
term_to_var({var, _} = Var) ->
    Var;

term_to_var({function, {_Mod, Symbol}, L}) ->
    term_to_var({function, Symbol, L});

term_to_var({function, Symbol, L}) ->
    <<A:8, Rest/binary>> = list_to_binary(atom_to_list(Symbol)), 
    Suffix = [leap_var:to_bitstring(V) || {var, _} = V <- L],
	AggVarName = iolist_to_binary([string:to_upper(A), Rest, "Of" | Suffix]),
	{var, AggVarName}.


%% @private
terms_to_fields(R, Terms) ->
    S = maps:from_list(leap_unification:sequenced_variables(R#relation.head)),
    leap_unification:apply_substitution(Terms, S).


%% @private
vars_to_fields(R, Vars) ->
    S = maps:from_list(
        leap_unification:sequenced_variables(R#relation.head)),
    leap_unification:apply_substitution(Vars, S).


% %% @private
% vars_to_fields_subst(Vars) when is_tuple(Vars) ->
%     vars_to_fields_subst(tuple_to_list(Vars));

% vars_to_fields_subst(Vars) ->
%     Fun = fun(X, Y, Acc) -> [{X,Y}|Acc] end,
%     Pairs = zipfold(Fun, Vars, lists:seq(1, length(Vars))),
%     maps:from_list(Pairs).


% %% @private
%  -spec zipfold(Combine, List1, List2) -> List3 when
%       Combine :: fun((X, Y, Acc) -> T),
%       List1 :: [X],
%       List2 :: [Y],
%       List3 :: [T],
% 	  Acc :: [T],
%       X :: term(),
%       Y :: term(),
%       T :: term().

% zipfold(F, Xs, Ys) ->
% 	zipfold(F, Xs, Ys, []).

% zipfold(F, [X | Xs], [Y | Ys], Acc) -> 
% 	zipfold(F, Xs, Ys, F(X, Y, Acc));
% zipfold(F, [], [], Acc) when is_function(F, 3) -> 
% 	lists:reverse(Acc).


%% @private
product_append(Tuple) ->
    LoTs = tuple_to_list(Tuple),
    list_to_tuple(lists:append([tuple_to_list(T) || T <- LoTs])).


