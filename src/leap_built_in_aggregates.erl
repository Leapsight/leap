-module(leap_built_in_aggregates).
-behaviour(leap_aggregate_function).

-define(MARKER_LEN, 5).

-record(psqr, {
    init = false    ::  boolean(),
    quantiles       ::  [float()], % a list of quantiles to track
    tiles           ::  float(),
    avg             ::  float(),
    count = 0       ::  non_neg_integer(),
    kurt_m4         ::  float(),
    max             ::  float(),
    min             ::  float(),
    skew_m3         ::  float(),
    var_m2          ::  float()
}).

   
-record(quantile, {
    init = false    ::  boolean(),
    p               ::  float(), % p-quantile of the distribution
    len = 5         ::  pos_integer(), % number of markers
    dn              ::  float(),
    npos = {}       ::  tuple(),
    pos = {}        ::  tuple(),
    heights = {}    ::  tuple()
}).

% -type psqr()                ::  #psqr{}.
-type quantile()            ::  #quantile{}.

-type aggregate_function() ::    avg | count | max | min
                                | rand | sample | stddev | sum
                                | median.

-export_type([aggregate_function/0]).

-export([init/1]).
-export([info/1]).
-export([iterate/3]).
-export([terminate/2]).
-export([merge/3]).


-spec init(aggregate_function()) -> State :: any().

init(collect) -> [];
init(avg) -> init(mean);
init(count) -> 0;
init(max) -> undefined;
init(mean) -> {0, 0};
init(median) ->
    % median is the 0.5 quantile
    psqr([0.5]);
init(min) -> undefined;
init(rand) -> {0, 0};
init(sample) -> {0, 0};
init(stddev) -> {0, 0};
init(sum) -> 0;
init(sum_product) -> 0.


-spec info(aggregate_function()) -> leap_aggregate_function:info().


info(avg) -> 
    #{arity => 1, types => [number]};
info(count) -> 
    #{arity => 1, types => [integer]};
info(max) -> 
    #{arity => 1, types => [any]};
info(mean) -> 
    #{arity => 1, types => [number]};
info(median) -> 
    #{arity => 1, types => [number]};
info(min) -> 
    #{arity => 1, types => [any]};
info(stddev) -> 
    #{arity => 1, types => [number]};
info(sum) -> 
    #{arity => 1, types => [number]};
info(sum_product) -> 
    #{arity => 2, types => [number, number]};
% Returning collections
info(collect) -> 
    #{arity => 1, types => [any]};
info(n_rand) -> 
    #{arity => 2, types => [pos_integer, any]};
info(n_sample) -> 
    #{arity => 1, types => [pos_integer, any]}.


-spec iterate(aggregate_function(), Value :: any(), State :: any()) -> 
    NewState :: any().

iterate(collect, Value, State) ->
    [Value|State];    
iterate(avg, Value, State) ->
    iterate(mean, Value, State);

iterate(count, _, State) ->
    State + 1;

iterate(max, Value, undefined) ->
    Value;
iterate(max, Value, State) when Value > State ->
    Value;
iterate(max, _, State) ->
    State;

iterate(mean, Value, {N, Acc}) when is_number(Value) ->
    {N + 1, Acc + Value};

iterate(median, Value, State) ->
    psqr_add(Value, State);

iterate(min, Value, undefined) ->
    Value;
iterate(min, Value, State) when Value < State ->
    Value;
iterate(min, _, State) ->
    State;

iterate(rand, _Value, State) ->
    % TODO
    State;
iterate(sample, _Value, State) ->
    % TODO
    State;
iterate(stddev, _Value, State) ->
    % https://en.wikipedia.org/wiki/Standard_deviation#Rapid_calculation_methods
    % TODO
    State;
iterate(sum, Value, State) when is_number(Value) ->
    State + Value;

iterate(sum_product, {X, Y}, State)  when is_number(X), is_number(Y) ->
    State + X * Y.


%% -----------------------------------------------------------------------------
%% @doc
%% To support parallel aggregates
%% @end
%% -----------------------------------------------------------------------------
-spec merge(aggregate_function(), any(), any()) -> NewState :: any().

merge(_Fun, _State1, State2) ->
    % TODO
    State2.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec terminate(aggregate_function(), any()) -> Result :: any().

terminate(collect, State) -> 
    State;
terminate(avg, State) -> 
    terminate(mean, State);
terminate(count, State) ->
    State;
terminate(max, State) ->
    State;
terminate(mean, {N, Acc}) ->
    Acc/N;
terminate(median, State) ->
    #{quantiles := [{0.5, Median}]} = psqr_results(State),
    Median;
terminate(min, State) ->
    State;
terminate(rand, State) ->
    State;
terminate(sample, State) ->
    State;
terminate(stddev, State) ->
    State;
terminate(sum, State) ->
    State;
terminate(sum_product, State) ->
    State.




%% =============================================================================
%% PRIVATE
%% =============================================================================


%% -----------------------------------------------------------------------------
%% @doc
%% Creates a p-squared object
%% @end
%% -----------------------------------------------------------------------------
psqr(Qs) when is_list(Qs) ->
    #psqr{
        quantiles = [quantile(Q) || Q <- Qs],
        min = pos_infinity,
        max = neg_infinity,
        count = 0,
        avg = 0.0,
        var_m2 = 0.0,
        skew_m3 = 0.0,
        kurt_m4 = 0.0
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
psqr_add(Value, #psqr{} = St) ->
    Min = case St#psqr.min of 
        pos_infinity -> Value; 
        (_) -> min(St#psqr.min, Value)
    end,
    Max = case St#psqr.max of 
        neg_infinity -> Value; 
        (_) -> max(St#psqr.max, Value)
    end,
    Delta = Value - St#psqr.avg,
    Avg = (St#psqr.count * St#psqr.avg + Value) 
            / (St#psqr.count + 1),
    Var = St#psqr.var_m2 + Delta * (Value - Avg),
    Skew = St#psqr.skew_m3 + math:pow(Value - Avg, 3.0),
    Kurt = St#psqr.kurt_m4 + math:pow(Value - Avg, 4.0),
    Qs = [quantile_add(Value, Q) || Q <- St#psqr.quantiles],

    St#psqr{
        quantiles = Qs,
        min = Min,
        max = Max,
        count = St#psqr.count + 1,
        avg = Avg,
        var_m2 = Var,
        skew_m3 = Skew,
        kurt_m4 = Kurt
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
psqr_calc(QP1, Q, QM1, D, NP1, N, NM1) ->
    D1 = float(D),
    N1 = float(N),
    NP11 = float(NP1),
    NM11 = float(NM1),

    Outer = D1 / (NP11 - NM11),
    Left = (N1 - NM11 + D1) * (QP1 - Q ) / (NP11 - N1),
    Right = (NP11 - N1 - D1) * (Q - QM1 ) / (N1 - NM11),
    Q + Outer * (Left + Right).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
psqr_results(St) ->
    Var = St#psqr.var_m2 / (St#psqr.count - 1),
    Kurtosis = St#psqr.kurt_m4 / (St#psqr.count * math:pow(Var, 2.0)) - 3.0,
    Skewness = St#psqr.skew_m3 / (St#psqr.count * math:pow(Var, 1.5)),

    M = #{
        quantiles => [{P, quantile_value(Q)} || #quantile{p = P} = Q <- St#psqr.quantiles],
        max => St#psqr.max,
        min => St#psqr.min,
        mean => St#psqr.avg,
        count => St#psqr.count,
        variance => Var,
        kurtosis => Kurtosis,
        skewness => Skewness
    },
    % io:format(">>> ~p~n",[M]),
    M.


%% -----------------------------------------------------------------------------
%% @doc
%% Creates a quantile 
%% @end
%% -----------------------------------------------------------------------------
quantile(P) when is_float(P), P >= 0.0, P =< 1.0 ->
    #quantile{
        p = P,        
        len = ?MARKER_LEN,  
        dn = {0, P/2, P, (1 + P)/2, 1},    
        npos = {1, 1 + 2 * P, 1 + 4 * P, 3 + 2 * P, 5},    
        pos = list_to_tuple(lists:seq(1, ?MARKER_LEN)),
        heights = {}
    }.


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
quantile_add(Value, #quantile{len = Len, heights = H} = Q)
when tuple_size(H) =/= Len ->
    Q#quantile{heights = erlang:append_element(H, Value)};

quantile_add(Value, #quantile{init = false} = Q0) ->
    Sorted = list_to_tuple(lists:sort(tuple_to_list(Q0#quantile.heights))),
    Q1 = Q0#quantile{
        init = true,
        heights = Sorted
    },
    quantile_add(Value, Q1);

quantile_add(Value, #quantile{} = Q0) ->
    Len = Q0#quantile.len,
    Heights0 = Q0#quantile.heights,
    {Heights1, K} = case Value < element(1, Heights0) of
        true ->
            {setelement(1, Heights0, Value), 2};
        false ->
            try 
                Fun = fun
                    (I, Acc) 
                    when element(I - 1, Acc) =< Value andalso 
                    Value < element(I, Acc) ->
                        throw(2);
                    (_, Acc) ->
                        Acc
                end,
                Heights0 = lists:foldl(Fun, Heights0, lists:seq(2, Len)),

                case element(Len, Heights0) < Value of
                    true ->
                        {setelement(Len, Heights0, Value), Len};
                    false ->
                        {Heights0, Len}
                end

            catch
                throw:Val ->
                    {Heights0, Val}
            end
    end,

    Pos = lists:foldl(
        fun
            (I, Acc) when I < K ->
                Acc;
            (I, Acc) ->
                setelement(I, Acc, element(I, Acc) + 1)
        end, 
        Q0#quantile.pos,
        lists:seq(1, Len)
    ),

    NPos = list_to_tuple(
        [ X + Y || {X, Y} <- leap_tuples:zip(Q0#quantile.pos, Q0#quantile.dn)]),

    quantile_adjust(Q0#quantile{pos = Pos, npos = NPos, heights = Heights1}).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
-spec quantile_adjust(quantile()) -> quantile().

quantile_adjust(#quantile{} = St) ->
    Fun = fun(I, Acc) ->
        N = element(I, St#quantile.pos),
        Q = element(I, St#quantile.heights),
        D0 = element(I, St#quantile.npos) - N,
        case 
            (D0 >= 1 andalso element(I + 1, St#quantile.pos) - N > 1) orelse
            (D0 =< -1 andalso element(I - 1, St#quantile.pos) - N < -1) 
        of
            true ->
                D1 = trunc(D0/abs(D0)),
                QP1 = element(I + 1, St#quantile.heights),
                QM1 = element(I - 1, St#quantile.heights),
                NP1 = element(I + 1, St#quantile.pos),
                NM1 = element(I - 1, St#quantile.pos),
                QN0 = psqr_calc(QP1, Q, QM1, D1, NP1, N, NM1),
                case QM1 < QN0 andalso QN0 < QP1 of
                    true ->
                        Acc#quantile{
                            heights = setelement(I, St#quantile.heights, QN0),
                            pos = setelement(I, St#quantile.heights, N + D1)
                        };
                    false ->
                        QN1 = Q + D1 * 
                            (element(I + D1, St#quantile.heights) - Q) /
                            (element(I + D1, St#quantile.pos) - N),
                        Acc#quantile{
                            heights = setelement(I, St#quantile.heights, QN1),
                            pos = setelement(I, St#quantile.heights, N + D1)
                        }
                end;
            false ->
                Acc
        end
    end,
    lists:foldl(Fun, St, lists:seq(2, St#quantile.len)).


%% -----------------------------------------------------------------------------
%% @doc
%% @end
%% -----------------------------------------------------------------------------
quantile_value(#quantile{init = true} = Q) ->
    element(3, Q#quantile.heights);

quantile_value(Q0) ->
    Heights = Q0#quantile.heights,
    Q1 = Q0#quantile{
        heights = list_to_tuple(lists:sort(tuple_to_list(Heights)))
    },
    Len = tuple_size(Heights),
    N = trunc(min(max(Len, 1), Len * Q1#quantile.p)),
    element(N, Heights).


% test() ->
%     S = lists:foldl(fun(X, Acc) -> leap_built_in_aggregates:iterate(median, X, Acc) end, leap_built_in_aggregates:init(median), [0.02, 0.15, 0.74, 3.39, 0.83, 22.37, 10.15, 15.43, 38.62, 15.92, 34.60,10.28, 1.47, 0.40, 0.05, 11.39, 0.27, 0.42, 0.09, 11.37]).
