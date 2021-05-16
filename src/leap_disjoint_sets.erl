%% --------------------------------------------------------------
%% Copyright (C) Leapsight 2011 - 2014. All rights reserved.
%% --------------------------------------------------------------

%%-------------------------------------------------------------------
%% @author Alejandro M. Ramallo
%% Created : 26 February 2013
%%-------------------------------------------------------------------

-module(leap_disjoint_sets).

-record(leap_disjoint_sets, {
	dict = dict:new() :: lsx_dict()
}).

-ifdef(namespaced_types).
-type lsx_dict() 	:: dict:dict().
-type lsx_gbset() 	:: gb_sets:gb_set().
-else.
-type lsx_dict() 	:: dict().
-type lsx_gbset() 	:: gb_set().
-endif.

%% {Key :: key(), {root, Set :: gb_sets:gb_set()}} -> Key is the root and member of Set.
%% {Key :: key(), {Root ::key(), undefined}} -> Key is a member of a set
%% whose root is Root.
-type value() 				:: 	{root, lsx_gbset()} |
								{key(), undefined}.
-type key() 				:: 	any().
-type element() 			:: 	{key(), value()}.
-type leap_disjoint_sets() 	:: 	#leap_disjoint_sets{}.
-type merge_op() 			:: 	'and'|'or'|'xor'|'nand'.
-type merge_qualifier()		:: 	'any'|'all'.
-type merge_condition() 	:: 	{merge_op(), merge_qualifier(), function()}.


%% =======
%% EXPORTS
%% =======
-export([
	add/2,
	find/2,
	find_all/3,
	find_any/3,
	find_root/2,
	from_map/1,
	fold/3,
	get_list/2,
	get_set/2,
	get_sets/1,
	get_sets/2,
	is_equivalent/3,
	is_member/2,
	make_root/2,
	merge/3,
	merge_condition/4,
	new/0,
	partition_any/2,
	remove/2,
	segment/2,
	segment/3,
	to_dict/1,
	to_dict/2,
	to_dict/3,
	to_map/1,
	to_map/2,
	to_map/3,
	to_orddict/1,
	to_orddict/2,
	to_orddict/3,
	to_external/1,
	to_list/1
]).

%% =======
%% API
%% =======


-spec new() -> leap_disjoint_sets().

new() ->
	#leap_disjoint_sets{}.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec from_map(map()) -> leap_disjoint_sets().

from_map(Map) ->
	maps:fold(fun(K, V, Acc) -> add(Acc, [K, V]) end, new(), Map).


%% -----------------------------------------------------------------------------
%% @doc
%% Creates a new set whose leader (root) is Element.
%% In case a list is passed, it creates a set for each element of the list.
%% In both cases add/2 calls is_member/2 to ensure disjoint sets.
%% @end
%% -----------------------------------------------------------------------------
-spec add(DS::leap_disjoint_sets(), any()) ->
	leap_disjoint_sets().

add(DS, Elements) when is_list(Elements) ->
	Adder = fun(Element, Acc) ->
		case is_member(DS, Element) of
			false ->
				dict:store(Element, {root, gb_sets:singleton(Element)}, Acc);
			true ->
				Acc
		end
	end,
	Dict0 = DS#leap_disjoint_sets.dict,
	Dict1 = lists:foldl(Adder, Dict0, Elements),
	DS#leap_disjoint_sets{dict = Dict1};

add(DS, Element) ->
	case is_member(DS, Element) of
		false ->
			Dict0 = DS#leap_disjoint_sets.dict,
			Dict1 = dict:store(Element, {root, gb_sets:singleton(Element)}, Dict0),
			DS#leap_disjoint_sets{dict = Dict1};
		true ->
			DS
	end.


-spec remove(DS::leap_disjoint_sets(), Element::term()) ->
	leap_disjoint_sets().

remove(DS, Element) ->
	T = DS#leap_disjoint_sets.dict,
	case dict:find(Element, T) of
		error ->
			DS;
		{ok, {root, S1}} ->
			case gb_sets:size(S1) =:= 1 of
				true ->
					% Is the singleton set
					DS#leap_disjoint_sets{dict = dict:erase(Element, T)};
				false ->
					{NewRoot, S2} = gb_sets:take_smallest(S1),
					T2 = dict:store(NewRoot, {root, S2}, T),
					T3 = dict:erase(Element, T2),
					DS#leap_disjoint_sets{dict = T3}
			end;
		{ok, {Parent, undefined}} ->
			{root, S1} = dict:fetch(Parent, T),
			T2 = dict:store(Parent, gb_sets:delete(Element, S1)),
			T3 = dict:erase(Element, T2),
			DS#leap_disjoint_sets{dict = T3}
	end.

is_member(DS, Element) ->
	dict:is_key(Element, DS#leap_disjoint_sets.dict).

-spec find(DS::leap_disjoint_sets(), any()) ->
	list() | not_found.
%% @doc Returns the set containing the Element or not_found if one does not exist.
find(DS, Elements) when is_list(Elements) ->
	case find_element(DS, Elements) of
		not_found -> not_found;
		{_K, {root, S}} -> gb_sets:to_list(S)
	end;
find(DS, Element) ->
	find(DS, [Element]).

-spec find_any(DS::leap_disjoint_sets(), Pred::fun((Key::{key()}) -> boolean()), Elements::key() | [key()]) ->
	boolean().
%% @doc Returns true or false whether at least one evaluation of the predicate with an element in the set containing the Element returns true.
find_any(DS, Pred, Elements) when is_list(Elements) ->
	case find_element(DS, Elements) of
		not_found ->
			false;
		{_K, {root, Set}} ->
			gb_sets_any(Set, Pred)
	end;
find_any(DS, Pred, E) ->
	find_any(DS, Pred, [E]).

%% @doc Returns true or false whether all evaluations of the predicate with an element in the set containing the Element returns true.
-spec find_all(DS::leap_disjoint_sets(), Pred::fun((Key::{key()}) -> boolean()), Elements::key() | [key()]) -> boolean().
find_all(DS, Pred, Elements) when is_list(Elements) ->
	case find_element(DS, Elements) of
		not_found -> false;
		{_K, {root, Set}} ->
			gb_sets_all(Set, Pred)
	end;
find_all(DS, Pred, E) ->
	find_all(DS, Pred, [E]).


-spec partition_any(DS::leap_disjoint_sets(), Pred::fun((Key::term()) -> boolean())) ->
	{Satisfying::[term()], NotSatisfying::[term()]}.
partition_any(DS, Pred) ->
	lists:partition(fun(Set) -> gb_sets_any(Set, Pred) end, sets(DS)).


-spec find_root(DS::leap_disjoint_sets(), term()) ->
	term() | not_found.

find_root(DS, Elements) when is_list(Elements) ->
	case find_element(DS, Elements) of
		not_found -> not_found;
		{Key, {root, _S}} -> Key
	end;
find_root(DS, Element) ->
	find_root(DS, [Element]).


-spec make_root(DS :: leap_disjoint_sets(), Element :: term()) ->
	NewDS :: leap_disjoint_sets().
%% @doc Makes Element the root of its set if it exists.
%% Notice that this is not necesarily permamnent.
%% For example, a subsequent merge or remove operation might elect a new root.
make_root(DS, NewRoot) ->
	T0 = DS#leap_disjoint_sets.dict,
	case dict:find(NewRoot, T0) of
		error ->
			DS;
		{ok, {root, _S}} ->
			% Already the root
			DS;
		{ok, {OldRoot, undefined}} ->
			% We will make it the root
			{root, Set} = dict:fetch(OldRoot, T0),
			T1 = dict:store(NewRoot, {root, Set}, T0),
			T2 = dict:store(OldRoot, {NewRoot, undefined}, T1),
			DS#leap_disjoint_sets{dict = T2}
	end.


-spec find_element(DS::leap_disjoint_sets(), term()) ->
	element() | not_found.
find_element(DS, [E|Es]) ->
	T = DS#leap_disjoint_sets.dict,
	Rest = gb_sets:from_list(Es),
	case dict:find(E, T) of
		error -> not_found;
		{ok, {root, S}} ->
			case gb_sets:is_subset(Rest, S) of
				true -> {E, {root, S}};
				false -> not_found
			end;
		{ok, {Parent, undefined}} ->
			{root, S} = dict:fetch(Parent, T),
			case gb_sets:is_subset(Rest, S) of
				true -> {Parent, {root, S}};
				false -> not_found
			end
	end;
find_element(DS, Element) ->
	find_element(DS, [Element]).


-spec merge(DS::leap_disjoint_sets(), Element1::term(), Element2::term()) ->
	NewDS :: leap_disjoint_sets().
%% @doc Merge the sets whose representatives are Element1 and Element2.
%% If either Element1 or Element2 do not exist in the sets, we do nothing.
%% Returns a new disjoint set.
%% @end
merge(DS, E, E) ->
	DS;
merge(DS, E1, E2) ->
	case find_element(DS, E1) of
		not_found ->
			DS;
		{R1, {root, S1}} ->
			case find_element(DS, E2) of
				not_found ->
					DS;
				{R1, {root, _S1}} ->
					% E1 and E2 are equivalent since they share the same root
					DS;
				{_R2, {root, S2}} ->
					T2 = dict:store(R1, {root, gb_sets:union(S1, S2)}, DS#leap_disjoint_sets.dict),
					T3 = lists:foldl(fun(X, Acc0) -> dict:store(X, {R1, undefined}, Acc0) end, T2, gb_sets:to_list(S2)),
					DS#leap_disjoint_sets{dict = T3}
			end
	end.


-spec merge_condition(DS :: leap_disjoint_sets(), E1 :: term(), E2 :: term(), Cond :: merge_condition()) ->
	false |
	{ok, NewDS :: leap_disjoint_sets()}.
%% @doc Merges the sets to which E1 and E2 belong iff Condition is satisfied.
%% @end
merge_condition(DS, E, E, _Condition) ->
	{ok, DS};
merge_condition(DS, E1, E2, Condition) ->
	case find_element(DS, E1) of
		not_found ->
			{ok, DS};
		{R1, {root, S1}} ->
			case gb_sets:is_member(E2, S1) of
				true ->
					{ok, DS};
				false ->
					case find_element(DS, E2) of
						not_found ->
							{ok, DS};
						{_R2, {root, S2}} ->
							do_merge_conditional(DS, R1, S1, S2, Condition)
					end
			end
	end.

%% @private
do_merge_conditional(DS, R1, S1, S2, {Op, EQ, Pred}) ->
	MergeConditional = fun
        ('nand', true, true) -> false;
		('nand', _, _) -> true;
        ('nor', false, false) -> true;
		('nor', _, _) -> false;
		('and', C1, C2) -> C1 and C2;
		('or', C1, C2) -> C1 or C2;
		('xor', C1, C2) -> C1 xor C2
	end,
	DoMerge = case EQ of
		any ->
			MergeConditional(Op, gb_sets_any(S1, Pred), gb_sets_any(S2, Pred));
		all ->
			MergeConditional(Op, gb_sets_all(S1, Pred), gb_sets_all(S2, Pred))
	end,
	case DoMerge of
		false ->
			false;
		true ->
			T2 = dict:store(R1, {root, gb_sets:union(S1, S2)}, DS#leap_disjoint_sets.dict),
			T3 = gb_sets:fold(fun(X, Acc) -> dict:store(X, {R1, undefined}, Acc) end, T2, S2),
			{ok, DS#leap_disjoint_sets{dict = T3}}
	end.


-spec is_equivalent(DS::leap_disjoint_sets(), Element1::term(), Element2::term()) ->
	boolean().
%% @doc Returns true if the two elements belong to the same set
is_equivalent(DS, Element1, Element2) ->
	find_element(DS, [Element1, Element2]) =/= not_found.


to_external(DS) ->
	[gb_sets:to_list(S) || {_K, S} <- root_elements(DS)].

fold(DS, Fun, Acc0) ->
	Adapter = fun
		(_Key, {_Parent, undefined}, Acc) ->
			Acc;
		(_Key, {root, S}, Acc) ->
			Fun(gb_sets:to_list(S), Acc)
	end,
	dict:fold(Adapter, Acc0, DS#leap_disjoint_sets.dict).


-spec segment(DS1 :: leap_disjoint_sets(), Pred :: function()) ->
	DS2 :: leap_disjoint_sets().
%% @doc Segments the entire sets of sets by merging elements X and Y for which Pred(X,Y) returns true.
segment(DS, Pred) ->
	%% Roots = [hd(List) || List <- to_external(DS)],
	Roots = [Root || {Root,_} <- root_elements(DS)],
	segment(DS, Pred, Roots).


-spec segment(DS1 :: leap_disjoint_sets(), Pred :: function(), Elements :: list()) ->
	DS2 :: leap_disjoint_sets().
%% @doc Segments the Elements by merging elements X and Y belonging to Elements for which Pred(X,Y) returns true.
segment(DS, _Pred, []) ->
	DS;
segment(DS, Pred, Elements) when is_function(Pred, 2), is_list(Elements) ->
	Permutation = [{X, Y} || X <- Elements, Y <- Elements, X =/= Y],
	do_segment(DS, Pred, Permutation).


-spec do_segment(DS1 :: leap_disjoint_sets(), Pred :: function(), Elements :: list()) ->
	DS2 :: leap_disjoint_sets().
%% @private
do_segment(DS, _Pred, []) ->
	DS;
do_segment(DS0, Pred, [{X, Y}|T]) ->
	case is_equivalent(DS0, X, Y) of
		true ->
			do_segment(DS0, Pred, T);
		false ->
			DS1 = case Pred(X,Y) of
				true ->
					merge(DS0, X, Y);
				false ->
					DS0
			end,
			do_segment(DS1, Pred, T)
	end.


get_list(DS, Element) ->
	sofs:to_external(get_set(DS, Element)).

%% @doc Returns a list of all the sets of this disjoint-set.
get_sets(DS) ->
	sets(DS).

to_list(DS) ->
	dict:fetch_keys(DS#leap_disjoint_sets.dict).

%% @doc Returns a dictionary representation where each entry consists of every element in the union of the sets and its value the root element of the set each element belongs to.
to_dict(DS) ->
	to_dict_mod(DS, root, dict).

to_dict(DS, Pred) ->
	to_dict_mod(DS, Pred, dict).

to_dict(DS, E, Pred) ->
	to_dict_mod(DS, E, Pred, dict).


to_map(DS) ->
	to_dict_mod(DS, root, maps).

to_map(DS, Pred) ->
	to_dict_mod(DS, Pred, maps).

to_map(DS, E, Pred) ->
	to_dict_mod(DS, E, Pred, maps).


to_orddict(DS) ->
	to_dict_mod(DS, root, orddict).

to_orddict(DS, Pred) ->
	to_dict_mod(DS, Pred, orddict).

to_orddict(DS, E, Pred) ->
	to_dict_mod(DS, E, Pred, orddict).


to_dict_mod(DS, Pred, Mod)
when Pred == root; Pred == min; Pred == max; is_function(Pred, 1) ->
	do_to_dict(root_elements(DS), Pred, Mod, Mod:new()).



to_dict_mod(DS, E, Pred, Mod)
when Pred == root; Pred == min; Pred == max; is_function(Pred, 1) ->
	do_to_dict(DS, E, Pred, Mod, Mod:new()).


%% @private
do_to_dict(DS, E, Pred, Mod, Acc) ->
	case find_element(DS, E) of
		not_found ->
			Mod:new();
		{Root, {root, S}} ->
			do_to_dict([{Root, S}], Pred, Mod, Acc)
	end.



do_to_dict([], _Pred, _Mod, Acc) ->
	Acc;
do_to_dict([{Root, S}|T], Pred, Mod, Acc0) ->
	{Leader, Set} = case Pred of
		root ->
			{Root, S};
		min ->
			{gb_sets:smallest(S), S};
		max ->
			{gb_sets:largest(S), S};
		_ ->
			FS = gb_sets:filter(Pred, S),
			case gb_sets:size(FS) of
				0 ->
					{Root, S};
				_ ->
					{gb_sets:smallest(FS), S}
			end
	end,
	AddToDictFun = fun
		(X, Acc) when Mod == maps ->
			Mod:put(X, Leader, Acc);
		(X, Acc) ->
			Mod:store(X, Leader, Acc)
	end,
	Acc1 = gb_sets:fold(AddToDictFun, Acc0, Set),
	do_to_dict(T, Pred, Mod, Acc1).



sets(DS) ->
	[S || {_K, S} <- root_elements(DS)].

root_elements(DS) ->
	Fun = fun
		(Key, {root, S}, Acc) ->
			[{Key, S}|Acc];
		(_Key, {_Parent, undefined}, Acc) ->
			Acc
	end,
	dict:fold(Fun, [], DS#leap_disjoint_sets.dict).



%% @doc Returns a sofs containing the disjoint sets which contain Elements
get_sets(DS, Elements) ->
	R = sofs:restriction(sofs:canonical_relation(DS), sofs:set(Elements)),
	sofs:no_elements(R) == 2 orelse erlang:exit({internal_inconsistency}),
	sofs:range(R).

%% @doc Returns the set of elements containing Element
-spec get_set(DS::leap_disjoint_sets(), Element::term()) -> sofs:a_set().
get_set(DS, Element) ->
	sofs:set(find(DS, Element)).


%% Fun should return boolean
%% filter(Set, Fun) ->
%% 	sofs:restriction(Fun, Set, sofs:set([true])).

%% =================================================================
%% PRIVATE
%% =================================================================
gb_sets_any(Set, Pred) ->
	gb_sets_any_all_aux(gb_sets:next(gb_sets:iterator(Set)), Pred, any).

gb_sets_all(Set, Pred) ->
	gb_sets_any_all_aux(gb_sets:next(gb_sets:iterator(Set)), Pred, all).

gb_sets_any_all_aux(none, _Pred, any) -> false;
gb_sets_any_all_aux(none, _Pred, all) -> true;
gb_sets_any_all_aux({K, Iter}, Pred, EQ) ->
  case {Pred(K), EQ} of
    {true, any} -> true;
    {false, all} -> false;
    _Other -> gb_sets_any_all_aux(gb_sets:next(Iter), Pred, EQ)
  end.

