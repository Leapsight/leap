-module(tuples).

-type group_by_opt()    ::  sort.   
-type group_by_opts()   ::  #{group_by_opt() => any()}.
-type projection()      ::  [aggregate_op() | pos_integer()] | tuple().
-type aggregate_op()    ::  {Op :: atom(), Fields :: [pos_integer()]} 
                            | {Mod :: module(), Op :: atom() , Fields :: [pos_integer()]}.


-export_type([aggregate_op/0]).
-export_type([group_by_opt/0]).
-export_type([group_by_opts/0]).
-export_type([projection/0]).

-export([all/2]).
-export([any/2]).
-export([append/1]).
-export([append/2]).
-export([append/3]).
-export([avg/2]).
-export([collect/2]).
-export([extend/2]).
-export([foldl/3]).
-export([foldr/3]).
-export([group_by/3]).
-export([intersect/1]).
-export([intersect/2]).
-export([join/4]).
-export([map/2]).
-export([mapfoldl/3]).
-export([mapfoldr/3]).
-export([max/2]).
-export([mean/2]).
-export([min/2]).
-export([prefix/2]).
-export([project/2]).
-export([sum/2]).
-export([sum_product/3]).
-export([wrap/2]).
-export([zip/2]).




%% =============================================================================
%% API
%% =============================================================================



%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec all(Pred, Tuple) -> boolean() when
    Pred    ::  fun((Elem :: T) -> boolean()),
    Tuple   ::  tuple(),
    T       ::  term().

all(Pred, Tuple) when is_tuple(Tuple) ->
    all(Pred, Tuple, tuple_size(Tuple), 1).


%% @private
all(Pred, Tuple, Sz, N) when  N =< Sz ->
    case Pred(element(N, Tuple)) of
        true -> all(Pred, Tuple, Sz, N + 1);
        false -> false
    end;

all(_, _, _, _) ->
    true.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec any(Pred, Tuple) -> boolean() when
    Pred    ::  fun((Elem :: T) -> boolean()),
    Tuple   ::  tuple(),
    T       ::  term().

any(Pred, Tuple) when is_tuple(Tuple) ->
    any(Pred, Tuple, tuple_size(Tuple), 1).


%% @private
any(Pred, Tuple, Sz, N) when  N =< Sz ->
    case Pred(element(N, Tuple)) of
        true -> true;
        false -> any(Pred, Tuple, Sz, N + 1)
    end;
any(_, _, _, _) ->
    true.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec append([tuple()]) -> tuple().

append([T|[]]) ->
    T;

append([H|T]) ->
    append(H, append(T)).




%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec append(tuple(), tuple()) -> tuple().

append(L, R) when is_tuple(L), is_tuple(R) ->
    % We use lists because it is much faster
    list_to_tuple(lists:append(tuple_to_list(L), tuple_to_list(R))).

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec append(tuple(), tuple(), [pos_integer()]) -> any().

append(L, R, [H|T]) ->
    append(erlang:append_element(L, element(H, R)), R, T);

append(L, _, []) ->
    L.
    

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec map(Fun, Tuple1) -> Tuple2 when
      Fun :: fun((A) -> B),
      Tuple1 :: tuple(),
      Tuple2 :: tuple(),
      A :: term(),
      B :: term().

map(F, Tuple) when is_function(F, 1), is_tuple(Tuple) ->
    map(F, Tuple, tuple_size(Tuple), 1).


%% @private
map(F, Tuple, Sz, N) when  N =< Sz ->
    map(F, setelement(N, Tuple, F(element(N, Tuple))), Sz, N + 1);

map(_, Tuple, _, _) ->
    Tuple.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec foldl(Fun, Acc0, Tuple) -> Acc1 when
      Fun :: fun((Elem :: T, AccIn) -> AccOut),
      Acc0 :: term(),
      Acc1 :: term(),
      AccIn :: term(),
      AccOut :: term(),
      Tuple :: tuple(),
      T :: term().

foldl(F, Acc, Tuple) when is_tuple(Tuple) ->
    foldl(F, Tuple, tuple_size(Tuple), 1, Acc).


%% @private
foldl(F, Tuple, Sz, N, Acc) when N =< Sz ->
    foldl(F, Tuple, Sz, N + 1, F(element(N, Tuple), Acc));

foldl(_, _, _, _, Acc) ->
    Acc.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec foldr(Fun, Acc0, Tuple) -> Acc1 when
      Fun :: fun((Elem :: T, AccIn) -> AccOut),
      Acc0 :: term(),
      Acc1 :: term(),
      AccIn :: term(),
      AccOut :: term(),
      Tuple :: tuple(),
      T :: term().

foldr(F, Acc, Tuple) when is_tuple(Tuple) ->
    foldr(F, Tuple, tuple_size(Tuple), 1, Acc).


%% @private
foldr(F, Tuple, Sz, N, Acc) when N =< Sz ->
    F(element(N, Tuple), foldr(F, Tuple, Sz, N + 1, Acc));

foldr(_, _, _, _, Acc) ->
    Acc.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec mapfoldl(Fun, Acc0, Tuple1) -> {Tuple2, Acc1} when
      Fun :: fun((A, AccIn) -> {B, AccOut}),
      Acc0 :: term(),
      Acc1 :: term(),
      AccIn :: term(),
      AccOut :: term(),
      Tuple1 :: [A],
      Tuple2 :: [B],
      A :: term(),
      B :: term().

mapfoldl(F, Acc, Tuple) when is_function(F, 2), is_tuple(Tuple) ->
    mapfoldl(F, Tuple, tuple_size(Tuple), 1, Acc).


%% @private
mapfoldl(F, Tuple0, Sz, N, Acc0) when N =< Sz ->
    {Val, Acc1} = F(element(N, Tuple0), Acc0),
    {Tuple1, Acc2} = mapfoldl(F, Tuple0, Sz, N + 1, Acc1),
    Tuple2 = setelement(N, Tuple1, Val),
    {Tuple2, Acc2};

mapfoldl(_, Tuple, _, _, Acc) ->
    {Tuple, Acc}.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec mapfoldr(Fun, Acc0, Tuple1) -> {Tuple2, Acc1} when
      Fun :: fun((A, AccIn) -> {B, AccOut}),
      Acc0 :: term(),
      Acc1 :: term(),
      AccIn :: term(),
      AccOut :: term(),
      Tuple1 :: [A],
      Tuple2 :: [B],
      A :: term(),
      B :: term().

mapfoldr(F, Acc, Tuple) ->
    mapfoldr(F, Tuple, tuple_size(Tuple), 1, Acc).


%% @private
mapfoldr(F, Tuple0, Sz, N, Acc0) when N =< Sz ->
    {Tuple1, Acc1} = mapfoldr(F, Tuple0, Sz, N + 1, Acc0),
    {Val, Acc2} = F(element(N, Tuple0), Acc1),
    Tuple2 = setelement(N, Tuple1, Val),
    {Tuple2, Acc2};

mapfoldr(_, Tuple, _, _, Acc) ->
    {Tuple, Acc}.



%% -----------------------------------------------------------------------------
%% @doc
%% Returns true if A is a prefix of B, otherwise false.
%% @end
%% -----------------------------------------------------------------------------
-spec prefix(tuple(), tuple()) -> boolean().

prefix(A, B) when tuple_size(A) =< tuple_size(B) ->
    case ls_unification:prefix_match(A, B) of
        {ok, _} -> true;
        false -> false
    end;
prefix(A, B) when is_tuple(A), is_tuple(B) ->
    false.

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec zip({A :: term()}, {B :: term()}) -> [{A :: term(), B :: term()}].

zip(A, B) when tuple_size(A) == tuple_size(B) ->
    zip(A, B, tuple_size(A), 1).

zip(A, B, Sz, N) when N =< Sz ->
    [{element(N, A), element(N, B)} | zip(A, B, Sz, N + 1)];
zip(_, _, _, _) ->
    [].

%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec project(tuple(), [pos_integer()]) -> [tuple()] | tuple().

project(Tuple, Fields) when is_tuple(Tuple) ->
    list_to_tuple(collect(Tuple, Fields));

project(L, Fields) when is_list(L) ->
    [project(T, Fields) || T <- L].



%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec wrap([tuple()] | tuple(), list()) -> [tuple()].

wrap(Tuple, Fields) when is_tuple(Tuple) ->
    All = lists:seq(1, tuple_size(Tuple)),
    Proj = lists:subtract(All, Fields),
    do_wrap(Tuple, Proj, Fields);

wrap(L, Fields) when is_list(L) ->
    All = lists:seq(1, tuple_size(hd(L))),
    Proj = lists:subtract(All, Fields),
    [do_wrap(T, Proj, Fields) || T <- L].


%% @private
do_wrap(Tuple, Proj, Fields) ->
    list_to_tuple([list_to_tuple(collect(Tuple, Fields)) | collect(Tuple, Proj)]).



%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec collect(tuple(), [pos_integer()]) -> list().

collect(Tuple, Fields) when is_tuple(Fields) ->
    collect(Tuple, tuple_to_list(Fields));

collect(Tuple, Fields) ->
    do_collect(Tuple, Fields).





%% =============================================================================
%% RELATIONAL OPERATORS
%% =============================================================================


%% -----------------------------------------------------------------------------
%% @doc
%% Adds a new attribute to tuple T by applying the function Fun to the value of t.
%% @end
%% -----------------------------------------------------------------------------
-spec extend(tuple() | [tuple()], function() | [function()]) -> any().

extend(L, Funs) when is_list(L) ->
    [extend(T, Funs) || T <- L];
extend(T, [Fun|T]) when is_tuple(T), is_function(Fun, 1) ->
    extend(extend(T, Fun), T);
extend(T, Fun) when is_tuple(T), is_function(Fun, 1) ->
    erlang:append_element(T, Fun(T)).





%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec group_by([tuple()], projection(), group_by_opts()) -> [tuple()].

group_by(Tuples, Projection, Opts) when is_tuple(Projection) ->
    group_by(Tuples, tuple_to_list(Projection), Opts);

group_by(Tuples, Projection, Opts) when is_list(Projection) ->
    Fun = fun
        ({Mod, Op, L}, {N, Acc}) -> 
            F = {Mod, Op, L, Mod:init(Op)},
            {N, [F|Acc]};
        ({Op, L}, {N, Acc}) -> 
            F = {
                leap_built_in_aggregates, 
                Op,
                L,
                leap_built_in_aggregates:init(Op)
            },
            {N, [F|Acc]};
        (I, {N, Acc}) when is_integer(I) ->
            %% We give it the order of the element in the resulting 
            %% grouping tuple
            {N + 1, [N|Acc]}
    end,

    {_, L} = lists:foldl(Fun, {1, []}, Projection),
    ProtoProj = lists:reverse(L),
    Fields = [I || I <- Projection, is_integer(I)],
    Res = do_group_by(Tuples, Fields, ProtoProj, dict:new()),

    case maps:get(sort, Opts, false) of
        true -> lists:sort(Res);
        false -> Res
    end.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
min(Tuples, Field) ->
    foldl(fun(T, Acc) -> erlang:min(Acc, element(Field, T)) end, pos_infinity, Tuples).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
max(Tuples, Field) ->
    foldl(
        fun
            (T, neg_infinity) -> T;
            (T, Acc) -> erlang:max(Acc, element(Field, T)) 
        end, 
        neg_infinity, Tuples).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sum(Tuples, Field) ->
    foldl(fun(T, Acc) -> Acc + element(Field, T) end, 0, Tuples).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
avg(Tuples, Field) ->
    mean(Tuples, Field).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
mean(Tuples, Field) ->
    {N, Total} = foldl(
        fun
            (T, {Count, Sum}) ->  
                Val = element(T, Field), 
                {Count + 1, Sum + Val} 
        end, 
        {0, 0}, Tuples),
    Total / N.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
sum_product(Tuples, Field1, Field2) ->
    foldl(
        fun(T, Acc) -> 
            Acc + element(Field1, T) * element(Field2, T) 
        end, 
        0, Tuples).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec join(
    [tuple()] | tuple(), 
    [tuple()] | tuple(), 
    {pos_integer(), pos_integer()}, 
    map()) -> [tuple()].

join(L, R, {LIdx, RIdx}, _Opts) ->
    sofs:to_external(sofs:join(sofs:relation(L), LIdx, sofs:relation(R), RIdx)).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec intersect([[tuple()]]) -> [tuple()].

intersect(Rs) ->
    sofs:to_external(sofs:intersection(sofs:from_term(Rs))).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec intersect([tuple()], [tuple()]) -> [tuple()].

intersect(L, R) ->
    sofs:to_external(sofs:intersection(sofs:from_term(L), sofs:from_term(R))).





%% =============================================================================
%% PRIVATE
%% =============================================================================


%% @private
do_group_by([H|T], Fields, ProtoCtxt, Acc0) ->
    GroupKey = project(H, Fields),
    Ctxt = case dict:find(GroupKey, Acc0) of
        {ok, Val} -> Val;
        error -> ProtoCtxt
    end,
    Acc1 = dict:store(
        GroupKey, 
        [iterate(OpCtxt, H) || OpCtxt <- Ctxt], 
        Acc0),
    do_group_by(T, Fields, ProtoCtxt, Acc1);

do_group_by([], _, _, Acc0) ->
    {_, Acc1} = dict:fold(fun group_by_extend/3, {[], []}, Acc0),
    Acc1.


%% -----------------------------------------------------------------------------
%% @private
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec iterate(
    {module(), atom(), [pos_integer()], any()} | integer(), tuple()) ->
    NewState :: any().

iterate({Mod, Op, [_] = L, State}, Tuple) ->
    [Value] = collect(Tuple, L),
    {Mod, Op, L, Mod:iterate(Op, Value, State)};

iterate({Mod, Op, Fields, State}, Tuple) when is_list(Fields) ->
    Value = project(Tuple, Fields),
    {Mod, Op, Fields, Mod:iterate(Op, Value, State)};

iterate(I, _) when is_integer(I) ->
    I.


%% @private
group_by_extend(GroupKey, [{Mod, Op, _, State}|T], {TAcc, Acc}) ->
    Value = Mod:terminate(Op, State),
    group_by_extend(GroupKey, T, {[Value|TAcc], Acc});

group_by_extend(GroupKey, [H|T], {TAcc, Acc}) when is_integer(H) ->
    Value = element(H, GroupKey),
    group_by_extend(GroupKey, T, {[Value|TAcc], Acc});

group_by_extend(_, [], {TAcc, Acc}) ->
    {[], [list_to_tuple(lists:reverse(TAcc))|Acc]}.



%% @private
do_collect(Tuple, [H|T]) ->
    [element(H, Tuple) | do_collect(Tuple, T)];
do_collect(_, []) ->
    [].



