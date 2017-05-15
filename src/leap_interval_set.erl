-module(leap_interval_set).

-export([collapse/1]).
-export([equivalent/2]).
-export([expand/1]).
-export([from_list/1]).
-export([to_list/1]).


equivalent(S1, S2) ->
	points(S1) == points(S2).

from_list(L) ->
	ordsets:from_list(L).

to_list(Set) ->
	ordsets:to_list(Set).

expand(Set) ->
	case ordsets:size(Set) == 0 of
		true ->
			Set;
		false ->
			do_expand(Set)
	end.


%% Returns a canonical form of the interval set that is the unique
%% equivalent set that has the minimum possible cardinality
%% [
%% 	{interval, T, 0, 0},
%% 	{interval, T, 3, 5},
%% 	{interval, T, 4, 6}
%% ]
%% -> [{interval, T, 0, 0}, {interval, T,  3, 6}]
collapse(Set) ->
	case ordsets:size(Set) =< 1 of
		true ->
			Set;
		false ->
			do_collapse(Set)
	end.


%% @private
do_expand(Set) ->
	% We create the set of unit intervals i.e. {interval, P, P} where P
	% is a member of points(Set)
	F = fun(X, Acc) -> [{interval, X, X}|Acc] end,
	L = ordsets:fold(F, [], points(Set)),
	ordsets:from_list(L).


%% @private
do_collapse(Set) ->
	%% TODO
	do_collapse(Set, []).

do_collapse([], Acc) ->
	% Reorder the set
	ordsets:from_list(Acc);
	
do_collapse([I|Rest], []) ->
	do_collapse(Rest, [I]);

do_collapse([I2|Rest], Acc = [I1|AccRest]) ->
	case leap_interval:union(I1, I2) of
		undefined ->
			do_collapse(Rest, [I2|Acc]);
		Union ->
			do_collapse(Rest, [Union|AccRest])
	end.


points(Set) ->
	L = ordsets:fold(fun({interval, _, H, T}, Acc) -> [H,T|Acc] end, [], Set),
	ordsets:from_list(L).

