-module(leap_interval).


-type type() 		:: 	integer 
						| days
						| seconds.
-type wildcard()	:: 	'_' | infinity.
-type head() 		:: 	neg_infinity | pos_infinity | integer | leap_var:var().
-type tail() 		:: 	pos_infinity | pos_infinity | integer | leap_var:var().
-type interval()	::	{interval, type(), head(), tail()}.

-export_type([interval/0]).

-export(['='/2]).
-export([begins/2]).
-export([ends/2]).
-export([equals/2]).
-export([first/0]).
-export([head/1]).
-export([included_in/2]).
-export([includes/2]).
-export([intersects/2]).
-export([is_ground/1]).
-export([is_interval/1]).
-export([is_member/2]).
-export([last/0]).
-export([max/2]).
-export([meets/2]).
-export([merges/2]).
-export([min/2]).
-export([minus/2]).
-export([new/1]).
-export([new/3]).
-export([overlaps/2]).
-export([precedes/2]).
-export([predecessor/1]).
-export([properly_included_in/2]).
-export([properly_includes/2]).
-export([succeeds/2]).
-export([successor/1]).
-export([tail/1]).
-export([to_map/1]).
-export([type/1]).
-export([union/2]).
-export([variables/1]).

-compile({no_auto_import,[max/2]}).
-compile({no_auto_import,[min/2]}).

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec new(type()) -> interval().

new(Type) ->
    new(Type, first(), last()).

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec new(type(), head() | wildcard(), tail() | wildcard()) -> interval().

new(Type, H, T) when H == infinity orelse H == '_' ->
    new(Type, first(), T);

new(Type, H, T) when T == infinity orelse H == '_' ->
    new(Type, H, last());

new(Type, H, T) 
when Type == integer; Type == days; Type == seconds ->
    {interval, Type, to_point(Type, H), to_point(Type, T)}.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
is_interval({interval, _, _, _}) -> true;
is_interval(_) -> false.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
type({interval, Type, _, _}) -> 
	Type.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
head({interval, _, H, _T}) -> 
	H.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
tail({interval, _, _H, T}) -> 
	T.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
predecessor(pos_infinity) ->
    pos_infinity;
predecessor(neg_infinity) ->
    neg_infinity;
predecessor(Int) when is_integer(Int) ->
    Int - 1.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
successor(pos_infinity) ->
    pos_infinity;
successor(neg_infinity) ->
    neg_infinity;
successor(Int) when is_integer(Int) ->
    Int + 1.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
first() -> neg_infinity.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
last() -> pos_infinity.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
is_member({{_,_,_}, {_,_,_}} = DT, {interval, Type, neg_infinity, pos_infinity})
when Type == days; Type == seconds ->
	valid_datetime(DT) orelse error(badarg),
	true;

is_member({_,_,_} = D, {interval, _, neg_infinity, pos_infinity}) ->
	calendar:valid_date(D) orelse error(badarg),
	true;

is_member(Term, {interval, _, neg_infinity, pos_infinity}) 
when is_integer(Term) ->
	true;

is_member(P, {interval, Type, neg_infinity, T}) ->
	to_point(Type, P) =< T;

is_member(P, {interval, Type, H, T}) ->
	X = to_point(Type, P),
	X >= H andalso X =< T.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
max(neg_infinity, P) ->
    P;
max(P, neg_infinity) ->
    P;
max(infinity, _) ->
    infinity;
max(_, infinity) ->
    infinity;
max(P1, P2) when is_integer(P1), is_integer(P2) ->
    erlang:max(P1, P2).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
min(neg_infinity, _) ->
    neg_infinity;
min(_, neg_infinity) ->
    neg_infinity;
min(infinity, P) ->
    P;
min(P, infinity) ->
    P;
min(P1, P2) when is_integer(P1), is_integer(P2) ->
    erlang:min(P1, P2).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
'='(A, B) ->
	equals(A, B).

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
equals({interval, _,  _, _} = I, I) ->
	true;
equals(_, _) ->
	false.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
includes({interval, Type, neg_infinity, TA}, {interval, Type, _, TB}) 
when TA >= TB ->
	true;
includes({interval, Type, HA, TA}, {interval, Type, HB, TB}) 
when HA =< HB, TA >= TB ->
	true;
includes(_, _) ->
	false.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
included_in(A, B) ->
	includes(B, A).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
properly_includes({interval, _, _, _} = I, I) ->
	false;
properly_includes(A, B) ->
	includes(A, B).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
properly_included_in(A, B) ->
	properly_includes(B, A).


%% Before
%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
precedes({interval, Type, _, _}, {interval, Type, neg_infinity, _}) ->
	false;
precedes({interval, Type, pos_infinity}, {interval, Type, _, _}) ->
	false;
precedes({interval, Type, _, TA}, {interval, Type, HB, _}) when TA < HB ->
	true;
precedes({interval, _, _, _} = I, I) ->
	false.

%%  After
%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
succeeds(A, B) ->
	precedes(B, A).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
overlaps({interval, Type, neg_infinity, TA}, {interval, Type, neg_infinity, TB})
when TA =< TB ->
	true;
overlaps({interval, Type, neg_infinity, TA}, {interval, Type, HB, _})
when HB =< TA ->
	true;
overlaps({interval, Type, HA, TA}, {interval, Type, HB, TB}) 
when HA =< TB, HB =< TA ->
	true;
overlaps({interval, _, _, _} = I, I) ->
	false.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------	
meets({interval, Type, neg_infinity, pos_infinity}, {interval, Type, _, _}) ->
	false;
meets({interval, Type, _, _}, {interval, Type, neg_infinity, pos_infinity}) ->
	false;
meets({interval, HA, TA} = A, {interval, HB, TB} = B) ->
    (precedes(A, B) andalso HB =:= successor(TA))
    orelse
    (precedes(B, A) andalso HA =:= successor(TB)).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
merges(A, B) ->
	overlaps(A, B) orelse meets(A, B).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
%% STARTS
begins({interval, _, _, _} = I, I) ->
	false;
begins({interval, Type, HA, TA}, {interval, Type, HB, _} = B) ->
	HA =:= HB andalso is_member(TA, B).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
%% FINISHES
ends({interval, _, _, _} = I, I) ->
	false;
ends({interval, Type, HA, TA}, {interval, Type, _, TB} = B) ->
	TA == TB andalso is_member(HA, B).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
%% If merges(A, B) is false then the result is undefined.
union(A = {interval, Type, HA, TA}, {interval, Type, HB, TB} = B) ->
	case merges(A, B) of
		true ->
			{interval, Type, min(HA, HB), max(TA, TB)};
		false ->
			undefined
	end.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
%% If overlaps(A, B) is false then the result is undefined.
intersects(A = {interval, Type, HA, TA}, {interval, Type, HB, TB} = B) ->
	case overlaps(A, B) of
		true ->
			{interval, Type, max(HA, HB), min(TA, TB)};
		false ->
			undefined
	end.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
%% If neither HA < HB, TA =< TB nor HA >= HB, TA > TB is true
%% then the result is undefined.
minus({interval, Type, H, _}, {interval, Type, H, _}) ->
	% Or infinity i.e. new(Type) ?
	undefined;

minus({interval, Type, HA, TA}, {interval, Type, HB, TB})
when (HA =:= HB orelse HA =:= neg_infinity orelse HA > HB) 
andalso TA > TB ->
	{interval, Type, max(successor(TB), HA), TA};

minus({interval, Type, HA, TA}, {interval, Type, HB, TB})
when (HA == neg_infinity orelse (is_integer(HB) andalso HA < HB))
andalso TA =< TB ->
	{interval, Type, HA, min(predecessor(HB), TA)}.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec to_map(interval()) -> map().

to_map({interval, Type, H, T}) ->
	#{type => Type, head => H, tail => T}.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
is_ground({interval, _, H, T}) -> 
    is_ground_term(H) andalso is_ground_term(T).

is_ground_term({var, _}) -> false;
is_ground_term(_) -> true.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
variables({interval, _, H, T}) ->
    lists:usort([V || V = {var, _} <- [H,T]]).




%% ============================================================================
%%  PRIVATE
%% ============================================================================






%% @private
to_point(days, {{_,_,_}, {_,_,_}} = DTime) ->
	valid_datetime(DTime) orelse error(badarg),
    calendar:datetime_to_gregorian_days(DTime);

to_point(seconds, {{_,_,_}, {_,_,_}} = DTime) ->
	valid_datetime(DTime) orelse error(badarg),
    calendar:datetime_to_gregorian_seconds(DTime);

to_point(Type, Term) 
when (Type == integer orelse Type == days orelse Type == seconds) 
andalso is_integer(Term) ->
    Term;

to_point(Type, {Y,M,D}) when Type == days; Type == seconds ->
    to_point(Type, {{Y,M,D}, {0,0,0}});

to_point(_, neg_infinity) ->
    neg_infinity;

to_point(_, pos_infinity) ->
    pos_infinity;

to_point(_, {var, _} = V) ->
    V;

to_point(_, _) ->
	error(badarg).


%% @private
valid_datetime({Date, {H, M, S}}) 
when H >= 0, H =< 23 andalso
	 M >= 0, M =< 59 andalso
	 S >= 0, S =< 59 ->
	calendar:valid_date(Date);
valid_datetime(_) ->
	false.