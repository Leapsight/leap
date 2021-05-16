%% =============================================================================
%% Copyright (C) Leapsight 2011 - 2021. All rights reserved.
%% =============================================================================

%% -----------------------------------------------------------------------------
%% @doc
%% This module implements the unification and matching algorithms, plus
%% ancilliary utilities such as checking for ground terms, existence of
%% variables and substitution handling.
%%
%% Unification and matching can be applied to lists, tuples and maps, and works
%% with the following special term types:
%%
%% * leap_var:var() - a variable.
%% * leap_interval:interval() - an interval whose elemenets can contain variables
%% * {function, any(), Args :: list()} - whose Args can contain variables.
%% * {const, A :: any()} - a way of telling the algorithms that the wrapped
%% term A is a constant.
%% * {min, A :: any()} - a special handling of a constant A. When the
%% unification and matching algorithms find this term together with a possibly
%% matching term B they will fail iff B is not a variable or another constant
%% whose value is more than or equal to the constant A.
%% * any() - any other term is considered a constant.
%% @end
%% -----------------------------------------------------------------------------
-module(leap_unification).
-include("leap.hrl").


-define(EMPTY_SUBSTITUTION, #{}).


-export([apply_substitution/2]).
-export([counted_variables/1]).
-export([create_substitution/0]).
-export([create_substitution/1]).
-export([create_substitution/2]).
-export([is_empty_substitution/1]).
-export([is_function_free/1]).
-export([is_ground/1]).
-export([is_idempotent_substitution/1]).
-export([is_instance/2]).
-export([is_mgu/3]).
-export([is_unifier/3]).
-export([make_idempotent_substitution/1]).
-export([match/2]).
-export([match/3]).
-export([ordered_variables/1]).
-export([distinct_terms/1]).
-export([prefix_match/2]).
-export([sequenced_variables/1]).
-export([substitution_composition/2]).
-export([substitution_domain/1]).
-export([substitution_range/1]).
-export([substitution_restriction/2]).
-export([substitution_to_list/1]).
-export([subsumes/2]).
-export([subsumes/3]).
-export([term_depth/1]).
-export([unify/2]).
-export([unify/3]).
-export([unify_lists2/3]).
-export([variables/1]).






%% -----------------------------------------------------------------------------
%% @doc
%% Applies a substitution S to term Term, returning a copy of
%% Term replacing every occurrence of each
%% variable in the term with the value mapped for that variable in the
%% Substitution.
%% @end
%% -----------------------------------------------------------------------------
apply_substitution(Term, S) when is_tuple(Term), is_map(S) ->
    apply_to_tuple(Term, S);

apply_substitution(Term, S) when is_list(Term), is_map(S) ->
    apply_to_list(Term, S);

apply_substitution(Term, S) when is_map(Term), is_map(S) ->
    apply_to_map(Term, S).


%% -----------------------------------------------------------------------------
%% @doc Returns a new empty substitution.
%% A substitution θ is a mapping from terms to terms which is the identity on
%% all constants.
%% A substitution is defined as a finite set of mappings from variables to
%% terms where each mapping must be unique,
%% because mapping the same variable to two different terms would be ambiguous.
%% For each substitution θ and atom q(tl,t2), let θ(q(tl,t2)) denote the atom q
%% (θ(tl), θ(t~)).
%% A substitution θ is called a unifier for two atoms A and B if θ(A) = θ(B).
%% Two atoms are unifiable if there is a unifier for them.
%% Elementary properties of substitutions:
%% - For all X ⊆ V,t and σ, if vars(t) ⊆ X then tσ=tσ|X
%% - For all σ, θ and t, if tσ=tθ then tσ|vars(t) = tθ|vars(t)
%% @end
%% -----------------------------------------------------------------------------
-spec create_substitution() -> map().

create_substitution() ->
	?EMPTY_SUBSTITUTION.


%% -----------------------------------------------------------------------------
%% @doc Creates and initialises a new substitution where all variables are
%% mapped to the no_substitution atom.
%% A substitution θ is a mapping from terms to terms which is the identity on
%% all constants.
%% A substitution is defined as a finite set of mappings from variables to
%% terms where each mapping must be unique,
%% because mapping the same variable to two different terms would be ambiguous.
%% For each substitution θ and atom q(tl,t2), let θ(q(tl,t2)) denote the atom q
%% (θ(tl), θ(t~)).
%% A substitution θ is called a unifier for two atoms A and B if θ(A) = θ(B).
%% Two atoms are unifiable if there is a unifier for them.
%% Elementary properties of substitutions:
%% - For all X ⊆ V,t and σ, if vars(t) ⊆ X then tσ=tσ|X
%% - For all σ, θ and t, if tσ=tθ then tσ|vars(t) = tθ|vars(t)
%% @end
%% -----------------------------------------------------------------------------
-spec create_substitution(ListOfVars::[leap_var:var()]) -> map().

create_substitution([]) ->
	?EMPTY_SUBSTITUTION;

create_substitution(L) when is_list(L) ->
	PL = [
        begin
            case X of
                {Var, _Val} when ?IS_VAR(Var) ->
                    X;
                X when ?IS_VAR(X) ->
                    {X, no_substitution}
            end
        end || X <- L
    ],
	maps:from_list(PL).


%% -----------------------------------------------------------------------------
%% @doc
%% A substitution θ is a mapping from terms to terms which is the identity on
%% all constants.
%% For each substitution θ and atom q(tl,t2), let θ(q(tl,t2)) denote the atom q
%% (θ(tl), θ(t~)).
%% A substitution θ is called a unifier for two atoms A and B if θ(A) = θ(B).
%% Two atoms are unifiable if there is a unifier for them.
%% Elementary properties of substitutions:
%% - For all X ⊆ V,t and σ, if vars(t) ⊆ X then tσ=tσ|X
%% - For all σ, θ and t, if tσ=tθ then tσ|vars(t) = tθ|vars(t)
%%
%% If any element of list L that is not an leap_var:var() will be ignored.
%% @end
%% -----------------------------------------------------------------------------
-spec create_substitution(
    Vars :: [leap_var:var()] | function(), Values :: list()) -> map().

create_substitution(L1, L2)
when is_list(L1), is_list(L2), length(L1) =:= length(L2) ->
	maps:from_list(
        [{K, V} || {K, V} <- lists:zip(L1, L2), ?IS_VAR(K)]);


%% -----------------------------------------------------------------------------
%% @doc Creates and initialised a new substitution by taking a function from
%% Variables to Substitutions,
%% a list of Variables and produces a list of Substitutions by applying the
%% function to every element in the list.
%% This function is used to obtain the return values. The evaluation order is
%% implementation dependent.
%%
%% If any element of list L that is not an leap_var:var() will be ignored.
%% @end
%% -----------------------------------------------------------------------------
create_substitution(Fun, L) when is_list(L) ->
	maps:from_list([{X, Fun(X)} || X <- L, ?IS_VAR(X)]).




%% -----------------------------------------------------------------------------
%% @doc
%% Returns whether the substitution Substitution is empty.
%% @end
%% -----------------------------------------------------------------------------
-spec is_empty_substitution(map()) -> boolean().

is_empty_substitution(S) when map_size(S) == 0 ->
	true;
is_empty_substitution(S) when is_map(S) ->
	false.





%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec is_function_free(tuple() | list() | map()) -> boolean().

is_function_free(Term) when is_tuple(Term) ->
    leap_tuples:all(fun is_function_free_element/1, Term);

is_function_free(Term) when is_list(Term) ->
    lists:all(fun is_function_free_element/1, Term);

is_function_free(Term) when is_map(Term) ->
    lists:all(fun is_function_free_element/1, maps:values(Term)).


%% @private
is_function_free_element(Fun) when is_function(Fun) ->
	false;

is_function_free_element({function, _, _}) ->
	false;

is_function_free_element({interval, _, H, T}) ->
	is_function_free_element(H) andalso is_function_free_element(T);

is_function_free_element({var, _N}) ->
	true;

is_function_free_element({const, _N}) ->
	true;

is_function_free_element({min, _N}) ->
	true.

%% -----------------------------------------------------------------------------
%% @doc
%%
%% @end
%% -----------------------------------------------------------------------------
is_ground(Term) when is_tuple(Term) ->
    is_ground_tuple(Term);

is_ground(Term) when is_list(Term) ->
    is_ground_list(Term);

is_ground(Term) when is_map(Term) ->
    is_ground_map(Term).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec is_constant_element(any()) -> boolean().

is_constant_element({const, _}) ->
    true;

is_constant_element({var, _}) ->
    false;

is_constant_element({function, _, _}) ->
    false;

is_constant_element({interval, _, H, T}) ->
    is_constant_element(H) andalso is_constant_element(T);

is_constant_element({min, Val}) ->
    is_constant_element(Val);

is_constant_element(_) ->
    true.


%% -----------------------------------------------------------------------------
%% @doc
%% Returns true if substitution is idempotent or false if it is not.
%% A substitution θ is idempotent if θθ = θ.
%% It is known that θ = {x1/t1,...,xk/tk} is idempotent if none of x1,...,xk
%% occurs in any t1,...,tk.
%% @end
%% -----------------------------------------------------------------------------
-spec is_idempotent_substitution(map()) -> boolean().

is_idempotent_substitution(S) when map_size(S) =:= 0 ->
    true;
is_idempotent_substitution(S) when is_map(S) ->
	sofs:is_disjoint(sofs:set(maps:keys(S)), sofs:set(maps:values(S))).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns whether Term1 is an instance of Term2.
%% This function is equivalent to subsumes(Term2, Term1).
%% @end
%% -----------------------------------------------------------------------------
-spec is_instance(tuple()| list()| map(), tuple()| list()| map()) ->
    {ok, map()} | false.

is_instance(A, B) ->
    subsumes(B, A) =/= false.


%% -----------------------------------------------------------------------------
%% @doc
%% Returns whether the substitution S is the most general unifier (mgu) for the
%% terms Term1 and Term2
%% @end
%% -----------------------------------------------------------------------------
is_mgu(S, Term1, Term2) when is_map(S) ->
	S =:= unify(Term1, Term2).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns whether the substitution S is a unifier of ther terms Term1 and Term2
%% @end
%% -----------------------------------------------------------------------------
is_unifier(S, Term1, Term2) when is_map(S) ->
	apply_substitution(Term1, S) =:= apply_substitution(Term2, S).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns a new substitution in which any mapping {X -> X} has been eliminated.
%% A substitution θ is idempotent if θθ = θ.
%% It is known that θ = {x1/t1,...,xk/tk} is idempotent if none of x1,...,xk
%% occurs in any t1,...,tk.
%% Our unification algorithm produces substitutions where is possible to find
%% {X -> X}, which according
%% to Ullman is the right thing to do. This function eliminates those mappings.
%% @end
%% -----------------------------------------------------------------------------
-spec make_idempotent_substitution(map()) ->map().

make_idempotent_substitution(S) ->
	maps_filter(fun(X, Y) -> X =/= Y end, S).


%% -----------------------------------------------------------------------------
%% @doc
%% Term matching algorithm from Ullman p.747
%% @end
%% -----------------------------------------------------------------------------
-spec match(Tuple1 :: tuple(), Tuple2 :: tuple()) -> {ok, map()} | false.

match(A, B) ->
    match(A, B, #{}).


%% -----------------------------------------------------------------------------
%% @doc
%% Term matching algorithm from Ullman p.747
%% @end
%% -----------------------------------------------------------------------------
-spec match(Tuple1 :: tuple(), Tuple2 :: tuple(), map()) -> {ok, map()} | false.

match(A, A, S) when is_tuple(A); is_list(A); is_map(A) ->
    {ok, S};

match(A, B, S) when tuple_size(A) == tuple_size(B) ->
    match_tuples(A, B, S);

match(A, B, S) when is_list(A), is_list(B) , length(A) == length(B) ->
    match_lists(A, B, S);

match(A, B, S) when map_size(A) == map_size(B) ->
    match_lists(maps:to_list(A), maps:to_list(B), S);

match(_, _, _) ->
    false.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec prefix_match(Tuple1 :: tuple(), Tuple2 :: tuple()) -> {ok, map()} | false.

prefix_match(A, B) when tuple_size(A) < tuple_size(B) ->
    match_tuples(A, B, tuple_size(A), 1, #{});

prefix_match(A, B) when is_list(A), is_list(B) , length(A) < length(B) ->
    match_lists(A, lists:sublist(B, length(A)), #{});

prefix_match(A, B) when map_size(A) < map_size(B) ->
    match_lists(
        maps:to_list(A), lists:sublist(maps:to_list(B), length(A)), #{});

prefix_match(A, B) ->
    match(A, B).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns the left side of the substitution.
%% Notice that domain will only return distinct terms i.e. it treats the substitution as an idempotent one.
%% @end
%% -----------------------------------------------------------------------------
-spec substitution_domain(map()) -> list().

substitution_domain(S) ->
	maps:keys(S).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns the right side of the substitution.
%% Notice that domain will only return distinct terms i.e. it treats the
%% substitution as an idempotent one.
%% @end
%% -----------------------------------------------------------------------------
-spec substitution_range(map()) -> list().

substitution_range(S) ->
	maps:values(S).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns a list of mapping pairs {Var, Substitution :: term()}.
%% @end
%% -----------------------------------------------------------------------------
-spec substitution_to_list(map()) -> list().

substitution_to_list(S) ->
	maps:to_list(S).


%% -----------------------------------------------------------------------------
%% @doc Returns the composition of two substitutions.
%% Let θ = {x1/t1, . . . , xk/tk} and δ = {y1/s1, . . . , yh/sh} be
%% substitutions (where x1, . . . , xk) are pairwise distinct variables,
%% and y1, . . . , yh are also pairwise distinct variables.
%% Then the composition θδ of θ and δ is the substitution obtained from the
%% sequence {x1/(t1δ), . . . , xk/(tkδ), y1/s1, . . . , yh/sh}
%% by deleting any binding xi/(tiδ) for which xi = (tiδ) and deleting any
%% binding yj/sj for which yj ∈ {x1,...,xk}.
%% Properties:
%% - The composition of substitutions is not commutative i.e. σθ =/= θσ.
%% - The composition of substitutions is associative i.e. t(σθ) = (tσ)θ.
%% @end
%% -----------------------------------------------------------------------------
-spec substitution_composition(A ::map(), B :: map()) -> map().

% substitution_composition(A0, B) ->
% 	%% We first apply the A and eliminate pairs where {X, Tsub}
%     Fun = fun
%         (K, {var, _} = Var, Acc) ->
%             case maps:find(Var, B) of
%                 {ok, Val} when K =/= Val ->
%                     maps:put(K, Val, Acc);
%                 _ ->
%                     Acc
%             end;
%         (_, _, Acc) ->
%             Acc
%     end,
%     A1 = maps:fold(Fun, A0, A0),
%     % L = [{X, apply_substitution(T, B)} || {X, T} <- maps:to_list(A0)],
% 	% AApplied = [{X, Tsub} || {X, Tsub} <- L, X =/= Tsub],

% 	% maps:merge(B, maps:from_list(AApplied)).
%     maps:merge(B, A1).

substitution_composition(Theta0, Delta) ->
    %% We first apply the Theta and eliminate pairs where X == Tsub
	% L1 = [{X, Tsub} ||
    %         {X, Tsub} <- [{X, apply_substitution(T, Delta)} ||
    %             {X, T} <- maps:to_list(Theta0)],
    %         X =/= Tsub],

    Apply = fun(X, T, Acc) ->
        TSub = case apply_to_element(T, Delta) of
            {ok, Val} -> Val;
            false -> T
        end,
        case {X, TSub} of
            {X, X} ->
                %% We delete any binding xi/(tiδ) for which xi = (tiδ)
                %% We deleting any binding yj/sj for which yj ∈ {x1,...,xk}.
                maps:remove(X, Acc);
            {X, TSub} ->
                %% By updating we are automatically replacing any binding
                %% yj/sj for which yj ∈ {x1,...,xk}.
                maps:put(X, TSub, Acc)
        end
    end,
    maps:fold(Apply, Delta, Theta0).

%% -----------------------------------------------------------------------------
%% @doc
%% Returns the restriction of the substitution S to the list of variables Vars
%% @end
%% -----------------------------------------------------------------------------
substitution_restriction(S, []) ->
	S;
substitution_restriction(S, Vars) ->
    maps:with(Vars, S).



%% -----------------------------------------------------------------------------
%% @doc
%% Returns whether the first term subsumes the second.
%% Notes: This mirrors the implementation of match/2 but allowing a non-ground
%% second argument and treating it as it if was.
%% @end
%% -----------------------------------------------------------------------------
-spec subsumes(
    A :: tuple() | list() | map(), B :: tuple() | list() | map()) ->
    {ok, map()} | false.

subsumes(A, B) ->
    subsumes(A, B, #{}).


%% -----------------------------------------------------------------------------
%% @doc
%% Returns whether the first term subsumes the second.
%% Notes: This mirrors the implementation of match/2 but allowing a non-ground
%% second argument and treating it as it if was.
%% @end
%% -----------------------------------------------------------------------------
-spec subsumes(
    A :: tuple() | list() | map(), B :: tuple() | list() | map(), map()) ->
    {ok, map()} | false.

subsumes(A, A, S) when is_tuple(A); is_list(A); is_map(A) ->
    {ok, S};

subsumes(A, B, S) when tuple_size(A) == tuple_size(B) ->
    subsumes_tuples(A, B, S);

subsumes(A, B, S) when is_list(A), is_list(B) , length(A) == length(B) ->
    subsumes_lists(A, B, S);

subsumes(A, B, S) when map_size(A) == map_size(B) ->
    %% We check the ranges of the substitutions
    subsumes_lists(maps:values(A), maps:values(B), S);

subsumes(_, _, _) ->
    false.


%% -----------------------------------------------------------------------------
%% @doc
%% Returns the maximal nesting depth of function symbols occurring in the term.
%% @end
%% -----------------------------------------------------------------------------
-spec term_depth(tuple() | list() | map()) -> pos_integer().

term_depth(Term) when is_tuple(Term) ->
    term_depth_tuple(Term);

term_depth(Term) when is_list(Term) ->
    term_depth_list(Term);

term_depth(Term) when is_map(Term) ->
    term_depth_list(substitution_range(Term)).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec unify(A :: tuple() | list() | map(), B :: tuple() | list() | map()) ->
    {ok, map()} | false.

unify(A, B) ->
    unify(A, B, #{}).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec unify(
    A :: tuple() | list() | map(), B :: tuple() | list() | map(), map()) ->
    {ok, map()} | false.

unify(A, A, S) when is_tuple(A); is_list(A); is_map(A) ->
    {ok, S};

unify(A, B, S) when tuple_size(A) == tuple_size(B) ->
    finish_unify(unify_tuples(A, B, S));

unify(A, B, S) when map_size(A) == map_size(B) ->
    finish_unify(unify_lists(maps:to_list(A), maps:to_list(B), S));

unify(A, B, S) when is_list(A), is_list(B) , length(A) == length(B) ->
    finish_unify(unify_lists(A, B, S));

unify(_, _, _) ->
    false.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
finish_unify(false) ->
    false;

finish_unify({ok, S}) ->
    %% Apply substitution to all function symbols
    Filter = fun
        (_K, {function, _, _}) ->
            true;
        (_K, _Val) ->
            false
    end,
    VarToFuns = maps_filter(Filter, S),
    Apply = fun(K, F0, Acc) ->
        F1 = apply_substitution(F0, Acc),
        maps:put(K, F1, Acc)
    end,
    {ok, maps:fold(Apply, S, VarToFuns)}.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec variables(tuple()) -> [leap_var:var()].

variables(Term) when is_tuple(Term) ->
    lists:usort(variables_tuple(Term));

variables(Term) when is_list(Term) ->
    lists:usort(variables_list(Term));

variables(Term) when is_map(Term) ->
    lists:usort(variables_map(maps:keys(Term))).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec counted_variables(tuple() | list() | map()) -> [leap_var:var()].

counted_variables(Term) when is_tuple(Term) ->
    % variables_tuple does not dedup nor sort
    do_counted_variables([{Var} || Var <- variables_tuple(Term)]);

counted_variables(Term) when is_list(Term) ->
    do_counted_variables([{Var} || Var <- variables_list(Term)]);

counted_variables(Term) when is_map(Term) ->
    do_counted_variables([{Var} || Var <- variables_list(maps:keys(Term))]).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec ordered_variables(tuple() | list() | map()) -> [leap_var:var()].

ordered_variables(Term) ->
    extract_ordered_variables(sequenced_variables(Term)).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec distinct_terms(tuple() | list() | map()) -> [leap_var:var()].

distinct_terms(Term) ->
    extract_distinct_terms(sequenced_terms(Term)).






%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec sequenced_variables(tuple() | list() | map()) -> [leap_var:var()].

sequenced_variables(Term) when is_tuple(Term) ->
    sequenced_variables_tuple(Term);

sequenced_variables(Term) when is_list(Term) ->
    sequenced_variables_list(Term);

sequenced_variables(Term) when is_map(Term) ->
    sequenced_variables_map(Term).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec sequenced_terms(tuple() | list() | map()) -> [leap_var:var()].

sequenced_terms(Term) when is_tuple(Term) ->
    sequenced_terms_tuple(Term);

sequenced_terms(Term) when is_list(Term) ->
    sequenced_terms_list(Term);

sequenced_terms(Term) when is_map(Term) ->
    sequenced_terms_map(Term).


%% =============================================================================
%% PRIVATE
%% =============================================================================



%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------

% TODO we can get other elements here. FIX!

apply_to_tuple({var, _} = Term, S) ->
    case apply_to_element(Term, S) of
        {ok, Val} ->
            Val;
        false ->
            Term
    end;

apply_to_tuple(T, S) ->
    Sz = tuple_size(T),
    apply_to_tuple(T, S, Sz, Sz).


%% @private
apply_to_tuple(T0, S, Sz, N) when N >= 1 ->
    T1 = case apply_to_element(element(N, T0), S) of
        {ok, Val} ->
            setelement(N, T0, Val);
        false ->
            T0
    end,
    apply_to_tuple(T1, S, Sz, N - 1);

apply_to_tuple(T, _, _, _) ->
    T.


%% @private
apply_to_element({var, _} = Term, S) ->
    case maps:find(Term, S) of
        {ok, _} = New -> New;
        error -> false
    end;

apply_to_element({interval, _, H0, T0} = Term0, S) ->
    Term1 = case apply_to_element(H0, S) of
        {ok, H1} ->
             setelement(3, Term0, H1);
        false ->
            Term0
    end,
    case apply_to_element(T0, S) of
        {ok, T1} ->
            {ok, setelement(4, Term1, T1)};
        false when Term1 =/= Term0 ->
            {ok, Term1};
        false ->
            false
    end;

apply_to_element({function, _, L} = Term, S) ->
    {ok, setelement(3, Term, apply_to_list(L, S))};

apply_to_element(_, _) ->
    %% A constant
    false.



%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
apply_to_list(L, S) ->
    apply_to_list(L, S, []).


%% @private
apply_to_list([], _, Acc) ->
    lists:reverse(Acc);

apply_to_list([H|T], S, Acc) ->
    case apply_to_element(H, S) of
        {ok, Val} ->
            apply_to_list(T, S, [Val|Acc]);
        false ->
            apply_to_list(T, S, [H|Acc])
    end.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
apply_to_map(M, S) ->
    maps:from_list(apply_to_list(maps:to_list(M), S, [])).


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec term_depth_tuple(tuple()) -> pos_integer().

term_depth_tuple(Term) ->
    leap_tuples:foldl(
        fun(E, Acc) -> erlang:max(term_depth_element(E), Acc) end,
        0,
        Term).


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec term_depth_list(list()) -> pos_integer().

term_depth_list([]) ->
    0;
term_depth_list(Term) ->
    lists:max([term_depth_element(E) || E <- Term]).


term_depth_element(Term) ->
    term_depth_element(Term, 0).

%% @private
term_depth_element({interval, _, From, To}, Acc) ->
    term_depth_element([From, To], Acc);

term_depth_element({function, _S, L}, Acc) ->
	 term_depth_element(L, Acc + 1);

term_depth_element([H|T], Acc) ->
    term_depth_element(T, term_depth_element(H, Acc));

term_depth_element([], Acc) ->
    Acc;

term_depth_element(_, Acc) ->
    Acc.

%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
unify_tuples(T1, T2, S0) ->
    unify_tuples(T1, T2, tuple_size(T1), 1, S0).


%% @private
unify_tuples(T1, T2, Sz, N, S0) when N =< Sz ->
    case unify_element(element(N, T1), element(N, T2), S0) of
        {ok, S1} ->
            unify_tuples(T1, T2, Sz, N + 1, S1);
        false ->
            false
    end;

unify_tuples(_, _, _, _, S) ->
    {ok, S}.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------

unify_lists([], [], S) ->
    {ok, S};

unify_lists([H1|T1], [H2|T2], S0) when length(T1) =:= length(T2) ->
    case unify_element(H1, H2, S0) of
		{ok, S1} ->
			unify_lists(T1, T2, S1);
		false ->
			false
	end;

unify_lists(_, _, _) ->
    false.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
unify_lists2([], [], S) ->
    {ok, S};

unify_lists2(L1, L2, S) when length(L1) =:= length(L2) ->
	%% Initially each unique term will become a member of its own equivalence
    %% class (a set).
	% DSets0 = leap_disjoint_sets:add(
    %     leap_disjoint_sets:from_map(S), lists:append(L1, L2)),
    DSets0 = leap_disjoint_sets:from_map(S),

    case unify_terms2(L1, L2, DSets0) of
		{ok, DSets1} ->
			%% From the constructed equivalence classes we need to perform
            %% a second phase in order to unify the children of the existing
            %% function symbols
			Fun = fun(Class, OuterAcc0) ->
				case [F || {function, _, _} = F <- Class] of
					[] ->
						OuterAcc0;
					[H|T] ->
						InnerFun = fun(X, InnerAcc0) ->
							case unify_terms2(H, X, InnerAcc0) of
								{ok, InnerAcc1} -> InnerAcc1;
								false -> InnerAcc0
							end
						end,
						lists:foldl(InnerFun, OuterAcc0, T)
				end
			end,
			DSets2 = leap_disjoint_sets:fold(DSets1, Fun, DSets1),
			% DSets3 = lists:foldl(Fun, DSets1, leap_disjoint_sets:to_external(DSets1)),

			%% Finally, we need to find a representative expression for each
            %% equivalence class in order to build a substitution that unifies
            %% both terms
			find_unifier(L1, L2, DSets2);
		false ->
			false
	end;

unify_lists2(_, _, _) ->
    false.




%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% This function is part of the unification algorithm.
%% It is used by unify2/2.
%% @end
%% -----------------------------------------------------------------------------
-spec unify_terms2(term(), term(), DSets :: term()) -> NewDSets :: term().

unify_terms2(T, T, DSets) ->
	{ok, DSets};

unify_terms2([], _, _) ->
	false;

unify_terms2(_, [], _) ->
	false;

unify_terms2([H|T1], [H|T2], DSets) ->
	unify_terms2(T1, T2, DSets);

unify_terms2([H1|T1], [H2|T2], DSets0) ->
    DSets1 = leap_disjoint_sets:add(DSets0, [H1, H2]),
	case unify_terms2(H1, H2, DSets1) of
		{ok, DSets2} ->
            unify_terms2(T1, T2, DSets2);
        false ->
            false
	end;


unify_terms2({function, Symbol, L1} = T1, {function, Symbol, L2} = T2, DSets0)
when length(L1) == length(L2) ->
	%% We add the function symbols and their arguments to the disjoint sets,
	%% each one belonging to their own set.
	%% If the function symbols were already in the disjoint set
    %% this has no effect.
	DSets1 = leap_disjoint_sets:add(DSets0, lists:append([[T1], [T2], L1, L2])),
	%% We define the two functions to be equivalent by merging their classes
	%% and unify their arguments
	unify_terms2(L1, L2, leap_disjoint_sets:merge(DSets1, T1, T2));

unify_terms2(
    {interval, Type, F1, To1} = T1, {interval, Type, F2, To2} = T2, DSets0) ->
    %% We add the function symbols and their arguments to the disjoint sets,
	%% each one belonging to their own set.
	%% If the intervals were already in the disjoint set
    %% this has no effect.
    L1 = [F1, To1],
    L2 = [F2, To2],
    DSets1 = leap_disjoint_sets:add(DSets0, lists:append([[T1], [T2], L1, L2])),
	%% We define the two intervals to be equivalent by merging their classes
	%% and unify their arguments
	unify_terms2(L1, L2, leap_disjoint_sets:merge(DSets1, T1, T2));

unify_terms2({var, _} = T1, T2, DSets0) ->
	%% We add the function arguments to the disjoint sets,
	%% each one belonging to their own set
    DSets1 = leap_disjoint_sets:add(DSets0, [T1, T2]),
    DSets2 = case T2 of
        {function, _, L} ->
            leap_disjoint_sets:add(DSets1, L);
        {min, Val} ->
            leap_disjoint_sets:add(DSets1, [Val]);
        {interval, _, F, T} ->
            leap_disjoint_sets:add(DSets1, [F, T]);
        _ ->
            DSets1
    end,
	unify_var2(T1, T2, DSets2);

unify_terms2(T1, {var, _} = T2, DSets) ->
	unify_terms2(T2, T1, DSets);

unify_terms2(_, _, _DSets) ->
	%% If any of the terms are labeled with two different symbols,
	%% neither of which is a variable,
	%% then there is no unifier - Ullman p.762
    %% If two functions have different symbols or arity then there is no unifier
	%% There is no way X can become "f of something" and "g of something" -
    %% Ullman p.764
	false.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% Part of the unification algorithm. This function is used by unify_terms2/3.
%% @end
%% -----------------------------------------------------------------------------
unify_var2({var, _Name} = T1, T2, DSets) ->
	leap_disjoint_sets:merge_condition(
        DSets, T1, T2, {'nand', 'any', fun is_constant_element/1}).


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% Part of the unification algorithm. This function is used by unify/2.
%% @end
%% -----------------------------------------------------------------------------
%% TODO Make this function more efficient (consider adding metadata to all datalog terms)
-spec find_unifier(list(), list(), leap_disjoint_sets:leap_disjoint_sets()) ->
	{ok, map()} | false.

find_unifier(L1, L2, DSets) ->
	%% We initialise Susbtitutions with all the variables mapped to
    %% no_substitution.
	%% By applying the algorithm we will incrementally replace no_substitution
    %% with a valid substitution for each variable map
	Vars = lists:usort(lists:append(variables(L1), variables(L2))),
    %% We merge with the received substitution S
	MGU0 = create_substitution(Vars),
	AllClasses = leap_disjoint_sets:to_external(DSets),

	%% Here we will apply the following algorithm:
	%% We classify the defined equivalent classes (disjoint sets) into 3 types:
	%% - Type 1: an equivalence class which has only variable symbols.
	%% - Type 2: an equivalence class which has a constant symbol. By
    %% definition this set should contain at most one constant symbol and
    %% cannot contain a function symbol.  Otherwise, there was an error in
    %% generating the equivalence classes.
	%% - Type 3: an equivalence class which has at least one function symbol.
	%% By definition this class cannot contain a constant symbol. Otherwise,
    %% there was an error in generating the equivalence classes.


    {Rest, Type3s} = lists:partition(
        fun(C) ->
            Pred = fun
                ({function, _, _}) -> true;
                (_) -> false
            end,
            lists:any(Pred, C) == false
        end,
        AllClasses),

	{Type2s, Type1s} = lists:partition(
        fun(Class) -> lists:any(fun is_constant_element/1,  Class) end, Rest),

    % io:format("Classes ~nType1: ~p~nType2: ~p~nType3:~p~n", [Type1s, Type2s, Type3s]),

	%% Then we need to select a leader symbol per equivalence class in order to
    %% build a representative substitution for each class. For that we apply
    %% the following rules:
	%% Rule 1: For a Type 1 set, pick any variable as a leader.
	%% Then for each variable in the class (including the leader) assign the
    %% leader as its substitution e.g. if the class is [X,Y,Z] and X is
    %% designated as leader then this operation will return the substitution
    %% [{X,X}, {Y,X}, {Z,X}]. This last step will produce a substitution that
    %% is not idempotent (see {@link make_idempotent_substitution/1}).
	%% Note: As opposed to the traditional way of implementing union-find
    %% algorithm, {@link leap_disjoint_sets.erl} does not define a leader per
    %% equivalence class, thus we need to do it here.
	MGU1 = lists:foldl(
        fun(L, Acc) -> find_substitutions_in_class(type1, L, Acc) end,
        MGU0, Type1s),

	%% Rule 2: For a Type 2 set, pick the constant as a leader.
	%% Then for each variable in the set assign the leader as its substitution.
	%% e.g. if the class is [X,Y,a] and a is designated as leader then this
    %% operation will return the substitution [{X,a}, {Y,a}].
	MGU2 = lists:foldl(
        fun(L, Acc) -> find_substitutions_in_class(type2, L, Acc) end,
        MGU1, Type2s),

	%% Rule 3: For a Type 3 set, pick as a leader, a function symbol for which
    %% all variables have had a substitution defined for them (by having
    %% applied rules 1 and 2).
	%% Then for each variable in the set assign the leader's substitution as
    %% its substitution.
	%%% The issue here is that we need to find an order to treat each Type3
    %% class, in order to be able to resolve function symbols.
	%% We are going to order the sets according to their variable count in
    %% descending order so that we can process first those sets containing the
    %% higher number of variables. In this way we maximise the chance to
    %% resolve a variable binding on the function symbols.

	% @TODO Analyse if sorting the sets according to the term depth of the function symbols would enhance
	% the efficieny and/or effectiveness of the algorithm.
	% @TODO WE STILL NEED TO DEMONSTRATE UNIFY IS UNIVERSALLY EFFECTIVE in presence of function symbols
	Sorter = fun(A, B) ->
		ALen = length(lists:filter(fun(X) -> element(1,X) == var end, A)),
		BLen = length(lists:filter(fun(X) -> element(1,X) == var end, B)),
		ALen >= BLen
	end,
	Type3sSorted = lists:sort(Sorter, Type3s),
	MGU3 = lists:foldl(
        fun(L, Acc) -> find_substitutions_in_class(type3, L, Acc) end,
        MGU2, Type3sSorted),

	% @TODO: We are not yet using the incrementally constructed MGU to check whether all variables have been resolved.
	% Could this allow us to avoid unnecessary work?

	%% If the above steps succeed in defining valid substitutions for all
    %% variables i.e. replacing all no_substitution values, then the unifier is
    %% the MGU; otherwise, there is no MGU.
	IsValid = fun
		({var, _}, no_substitution, Acc) ->
			Acc + 1;
		({var, _}, _, Acc) ->
			Acc;
		(_, _, Acc) ->
			Acc + 1
	end,
	case maps:fold(IsValid, 0, MGU3) == 0 of
		true ->
			{ok, MGU3};
		false ->
			false
	end.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
find_substitutions_in_class(type1, [H], S) ->
	%% A singleton equivalence class
	maps:put(H, H, S);

find_substitutions_in_class(type1, [Leader|_] = L, S) ->
	%% We designate the head as the leader and construct a mapping
    %% from each variable (including the leader) to it
    lists:foldl(
        fun
            (Var, Acc) when Var == Leader ->
                %% We remove the variable as it maps to itself
                %% This is to return an idempotent substitution
                maps:remove(Var, Acc);
            (Var, Acc) ->
                maps:update(Var, Leader, Acc)
        end,
        S, L);

find_substitutions_in_class(type2, L, S) when is_list(L)->
	%% We designate the head as the leader and construct a mapping
    %% from each variable to it
	%% As there is only one constant per equivalence class we just need
    %% to skip the leader
    [K] = lists:filter(fun is_constant_element/1, L),
    lists:foldl(
        fun
            (Term, Acc) when Term == K ->
                %% We do nothing becuase it is a constant
                Acc;
            (Var, Acc) ->
                maps:update(Var, K, Acc)
        end,
        S, L);

find_substitutions_in_class(type3, L, S) when is_list(L)->
	%% We first separate the function symbols from the variables
    %% in the equivalence class
	{Vars, Funs} = lists:partition(
        fun
            ({var, _}) -> true;
            (_) -> false
        end,
        L),

	HasSubstitution = fun
		({var, _} = Term) ->
			case maps:find(Term, S) of
				{ok, Value} ->
					Value =/= no_substitution;
                error ->
					false
			end;
		(_) ->
			false
	end,
	%% We need to select a function as a leader for which all variables
    %% have had an substitution defined.
	%% The other functions are equivalent to the leader so we will
    %% not do anything with them.
	LeaderSelector = fun({_S, Args}) -> lists:all(HasSubstitution, Args) end,
	Leader = case lists:filter(LeaderSelector, Funs) of
		[] ->
			no_substitution;
		[H|_T] ->
			apply_substitution(H, S)
	end,

	%% We generate substitutions with the designated leader
    %% for all variables in the class
	maps:merge(S, maps:from_list([{X, Leader} || X <- Vars])).



%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
unify_element(E, E, S) ->
    {ok, S};

unify_element('_', _, S) ->
	{ok, S};

unify_element(_, '_', S) ->
	{ok, S};

unify_element({var, _} = Var, Term, S) ->
    unify_var(Var, Term, S);

unify_element(Term, {var, _} = Var, S) ->
    unify_var(Var, Term, S);

unify_element({min, _}, {min, _}, S) ->
    %% TODO FIX - The semantics of this case are unclear
    {ok, S};

unify_element({min, V1}, V2, S) when V1 =< V2 ->
    {ok, S};

unify_element(V1, {min, V2}, S) when V1 >= V2 ->
    {ok, S};

unify_element({function, Symbol, L1}, {function, Symbol, L2}, S) ->
    unify_lists(L1, L2, S);

unify_element({interval, Type, HA, TA}, {interval, Type, HB, TB}, S0) ->
    case unify_element(HA, HB, S0) of
        {ok, S1} ->
            self_apply(unify_element(TA, TB, S1));
        false ->
            false
    end;

unify_element(_, _, _) ->
    false.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
unify_var({var, _} = T1, T2, S0) ->
    case maps:find(T1, S0) of
        {ok, T2} ->
            %% We already had the substitution T1 => T2
			{ok, S0};
		{ok, T3} ->
            %% We found T1 => T3
			self_apply(unify_element(T2, T3, S0));
		error ->
            %% We may bind T1 => T2
            S1 = maps:put(T1, T2, S0),
            %% However if T2 is a var we
            %% need to check that
			case maps:find(T2, S1)  of
				{ok, T3} ->
                    % S2 = maps:put(T1, T3, S1),
					self_apply(unify_element(T3, T2, S1));
				error ->
					self_apply({ok, S1})
			end
	end.

    self_apply(false) ->
        false;
    self_apply({ok, S}) ->
        {ok, substitution_composition(S, S)}.



% unify_var({var, _} = T1, T2, S0) ->
%     case maps:find(T1, S0) of
%         {ok, T2} ->
%             %% We already had the substitution T1 => T2
% 			{ok, S0};
% 		{ok, T3} ->
%             %% We found T1 => T3
% 			unify_var_aux(T2, T3, T1, S0);
% 		error ->
%             %% We may bind T1 => T2
%             %% However if T2 is a var we
%             %% need to check that
% 			case maps:find(T2, S0)  of
% 				{ok, T3} ->
% 					{ok, maps:put(T1, T3, S0)};
% 				error ->
% 					{ok, maps:put(T1, T2, S0)}
% 			end
% 	end.


% %% @private
% unify_var_aux({var, _} = T2, {var, _} = T3, _, S) ->
% 	{ok, maps:put(T2, T3, S)};

% unify_var_aux({var,_} = T2, T3, T1, S) ->
% 	{ok, maps:put(T2, T3, S)};

% unify_var_aux({function, _, _} = T2, {function, _, _} = T3, _, S) ->
% 	unify_element(T2, T3, S);

% unify_var_aux({function, _, _} = T2, {var, _} = T3, T1, S) ->
% 	{ok, maps:put(T3, T2, maps:put(T1, T2, S))};

% unify_var_aux(T2, {var, _} = T3, _, S) ->
%     %% Constants and {min, val}
% 	{ok, maps:put(T2, T3, S)};

% unify_var_aux(_, _, _, _) ->
%     false.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
match_tuples(T1, T2, S) ->
    match_tuples(T1, T2, tuple_size(T1), 1, S).

%% @private
match_tuples(T1, T2, Sz, N, S0) when N =< Sz ->
    case match_element(element(N, T1), element(N, T2), S0) of
        {ok, S1} ->
            match_tuples(T1, T2, Sz, N + 1, S1);
        false ->
            false
    end;
match_tuples(_, _, _, _, S) ->
    {ok, S}.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
match_lists([], [], S) ->
	{ok, S};

match_lists([H1|T1], [H2|T2], S0) ->
	case match_element(H1, H2, S0) of
		{ok, S1} ->
			match_lists(T1, T2, S1);
		false ->
			false
	end.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
match_element('_', _, S) ->
	{ok, S};

match_element(_, '_', S) ->
	{ok, S};

match_element(E, E, S) ->
    {ok, S};

match_element({min, _}, {min, _}, S) ->
    %% The semantics of this case are unclear
    {ok, S};

match_element({min, V1}, V2, S) when V1 =< V2 ->
    {ok, S};

match_element(V1, {min, V2}, S) when V1 >= V2 ->
    {ok, S};

match_element({function, Symbol, L1}, {function, Symbol, L2}, S)
when length(L1) =:= length(L2) ->
    match_lists(L1, L2, S);

match_element({interval, Type, HA, TA}, {interval, Type, HB, TB}, S0) ->
    case match_element(HA, HB, S0) of
        {ok, S1} ->
            match_element(TA, TB, S1);
        false ->
            false
    end;

match_element({var, _} = Var, Term, S) ->
    case is_ground_element(Term) of
        false ->
            false;
        true ->
            case maps:find(Var, S) of
                {ok, Term} ->
                    {ok, S};
                {ok, _} ->
                    %% The var was already mapped to another constant
                    false;
                error ->
                    {ok, maps:put(Var, Term, S)}
            end
    end;

match_element(_, _, _) ->
    false.



%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
subsumes_tuples(T, T, S) ->
    {ok, S};

subsumes_tuples(T1, T2, S) ->
    subsumes_tuples(T1, T2, tuple_size(T1), 1, S).


%% @private
subsumes_tuples(T1, T2, Sz, N, S0) when N =< Sz ->
    case subsumes_element(element(N, T1), element(N, T2), S0) of
        {ok, S1} ->
            subsumes_tuples(T1, T2, Sz, N + 1, S1);
        false ->
            false
    end;
subsumes_tuples(_, _, _, _, S) ->
    {ok, S}.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
subsumes_lists(L, L, S) ->
    {ok, S};

subsumes_lists([H1|T1], [H2|T2], S0) ->
	case subsumes_element(H1, H2, S0) of
		{ok, S1} ->
			subsumes_lists(T1, T2, S1);
		false ->
			false
	end.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
subsumes_element('_', _, S) ->
	{ok, S};

subsumes_element(_, '_', S) ->
	{ok, S};

subsumes_element(E, E, S) ->
    {ok, S};

subsumes_element({min, _}, {min, _}, S) ->
    %% The semantics of this case are unclear
    {ok, S};

subsumes_element({min, V1}, V2, S) when V1 =< V2 ->
    {ok, S};

subsumes_element(V1, {min, V2}, S) when V1 >= V2 ->
    {ok, S};

subsumes_element({function, Symbol, L1}, {function, Symbol, L2}, S)
when length(L1) =:= length(L2) ->
    subsumes_lists(L1, L2, S);

subsumes_element({interval, Type, HA, TA}, {interval, Type, HB, TB}, S0) ->
    case subsumes_element(HA, HB, S0) of
        {ok, S1} ->
            subsumes_element(TA, TB, S1);
        false ->
            false
    end;

subsumes_element({var, _} = Var, Term, S) ->
    %% We treat every term from Term2 as a distinct constant
    case maps:find(Var, S) of
        {ok, Term} ->
            {ok, S};
        {ok, _} ->
            %% The var T1 already has a substitution,
            %% if this substitution is not equal to T2 then,
            %% T1 does not subsume T2.
            false;
        error ->
            {ok, maps:put(Var, Term, S)}
    end;

subsumes_element(_, _, _) ->
    false.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
is_ground_tuple(Tuple) ->
    is_ground_tuple(Tuple, tuple_size(Tuple), 1).


%% @private
is_ground_tuple(Tuple, Sz, N) when N =< Sz ->
    case is_ground_element(element(N, Tuple)) of
        true ->
            is_ground_tuple(Tuple, Sz, N + 1);
        false ->
            false
    end;

is_ground_tuple(_, _, _) ->
    true.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
is_ground_list([]) ->
    true;
is_ground_list([H|T]) ->
    case is_ground_element(H) of
        true ->
            is_ground_list(T);
        false ->
            false
    end.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
is_ground_map(Map) ->
    is_ground_list(maps:values(Map)).


%% @private
is_ground_element({var, _}) ->
    false;

is_ground_element('_') ->
    false;

is_ground_element({function, _, L}) ->
    is_ground_list(L);

is_ground_element({interval, _, H, T}) ->
    is_ground_element(H) andalso is_ground_element(T);

is_ground_element(_) ->
    true.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
variables_tuple(T) ->
    variables_tuple(T, tuple_size(T), 1, []).

%% @private
variables_tuple(Tuple, Sz, N, Acc0) when N =< Sz ->
    Acc1 = [element_variables(element(N, Tuple))|Acc0],
    variables_tuple(Tuple, Sz, N + 1, Acc1);

variables_tuple(_, _, _, Acc) ->
    lists:append(Acc).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
variables_list(L) ->
    variables_list(L, []).


%% @private
variables_list([], Acc) ->
    lists:append(Acc);

variables_list([H|T], Acc) ->
    variables_list(T, [element_variables(H)|Acc]).


%% @private
do_counted_variables(Vars) ->
    leap_tuples:summarize(Vars, [1, {function, count, [1]}], #{}).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
variables_map(M) ->
    variables_list(maps:keys(M)).


%% @private
element_variables({var, _} = Term) ->
    [Term];

element_variables({function, _, L}) ->
    variables_list(L);

element_variables({interval, _, H, T}) ->
    variables_list([H,T]);

element_variables(_) ->
    [].


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sequenced_variables_tuple(T) ->
    sequenced_variables_tuple(T, tuple_size(T), 1, 1, []).

%% @private
sequenced_variables_tuple(Tuple, Sz, I, N, Acc0) when I =< Sz ->
    {N1, Acc1} = sequenced_variables_element(element(N, Tuple), {N, Acc0}),
    sequenced_variables_tuple(Tuple, Sz, I + 1, N1, Acc1);

sequenced_variables_tuple(_, _, _, _, Acc) ->
    Acc.



%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sequenced_terms_tuple(T) ->
    sequenced_terms_tuple(T, tuple_size(T), 1, 1, []).

%% @private
sequenced_terms_tuple(Tuple, Sz, I, N, Acc0) when I =< Sz ->
    {N1, Acc1} = sequenced_terms_element(element(N, Tuple), {N, Acc0}),
    sequenced_terms_tuple(Tuple, Sz, I + 1, N1, Acc1);

sequenced_terms_tuple(_, _, _, _, Acc) ->
    Acc.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sequenced_variables_list(L) ->
    sequenced_variables_list(L, 1, []).


%% @private
sequenced_variables_list([], _, Acc) ->
    Acc;

sequenced_variables_list([H|T], N, Acc) ->
    {N1, Acc1} = sequenced_variables_element(H, {N,Acc}),
    sequenced_variables_list(T, N1, Acc1).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sequenced_terms_list(L) ->
    sequenced_terms_list(L, 1, []).


%% @private
sequenced_terms_list([], _, Acc) ->
    Acc;

sequenced_terms_list([H|T], N, Acc) ->
    {N1, Acc1} = sequenced_terms_element(H, {N,Acc}),
    sequenced_terms_list(T, N1, Acc1).



%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sequenced_variables_map(M) ->
    sequenced_variables_list(maps:keys(M)).


%% @private
sequenced_variables_element(Value, Acc) ->
    lists:foldl(
        fun(X, {N, L}) -> M = N+1, {M, [{X, N}|L]} end,
        Acc,
        element_variables(Value)
    ).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sequenced_terms_map(M) ->
    sequenced_terms_list(maps:keys(M)).


%% @private
sequenced_terms_element(Value, Acc) ->
    lists:foldl(
        fun(X, {N, L}) -> M = N+1, {M, [{X, N}|L]} end,
        Acc,
        [Value]
    ).


%% @private
extract_ordered_variables(L) ->
    {Vs, _} = lists:unzip(
        lists:ukeysort(2, leap_tuples:summarize(L, [1, {function, min, [2]}], #{}))),
    Vs.

%% @private
extract_distinct_terms(L) ->
    {Vs, _} = lists:unzip(
        lists:ukeysort(2, leap_tuples:summarize(L, [1, {function, min, [2]}], #{}))),
    Vs.


%% -----------------------------------------------------------------------------
%% @doc
%% R17 does not have maps:filter/2
%% @end
%% -----------------------------------------------------------------------------
maps_filter(Fun, Map) ->
    case erlang:function_exported(maps, filter, 2) of
        true ->
            maps:filter(Fun, Map);
        false ->
	        maps:from_list(
                lists:filter(fun({K, V}) -> Fun(K, V) end, maps:to_list(Map)))
    end.