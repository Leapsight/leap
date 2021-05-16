%% =============================================================================
%% Copyright (C) Leapsight 2011 - 2021. All rights reserved.
%% =============================================================================

%% -----------------------------------------------------------------------------
%% @doc
%% Foo
%% @end
%% -----------------------------------------------------------------------------
-module(leap_aggregate_function).

-type info() :: #{
                    arity => pos_integer(),
                    types => atom()
                }.

-export_type([info/0]).


%% =============================================================================
%% CALLBACKS
%% =============================================================================


-callback init(atom()) -> State :: any().

-callback info(atom()) -> leap_aggregate_function:info().

-callback iterate(atom(), Value :: any(), State :: any()) -> NewState :: any().

-callback merge(atom(), any(), any()) -> NewState :: any().

-callback terminate(atom(), any()) -> Result :: any().