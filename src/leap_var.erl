%% --------------------------------------------------------------
%% Copyright (C) Leapsight 2011 - 2014. All rights reserved.
%% --------------------------------------------------------------

-module(leap_var).
-author('Alejandro M. Ramallo <alejandro.ramallo@leapsight.com>').

-type var()			::	{var, Name :: varname()}.
-type varname()		::	atom() | integer() | binary().

-export_type([var/0]).

-export([new/1]).
-export([name/1]).
-export([is_valid/1]).
-export([to_string/1]).
-export([to_bitstring/1]).





%% =============================================================================
%% API
%% =============================================================================




new(Name) when is_atom(Name) ->
	{var, Name};

new(Name) when is_integer(Name) ->
	{var, Name};

new(Name) when is_list(Name) ->
	{var, unicode:characters_to_binary(Name)};

new(Name) when is_binary(Name) ->
	{var, Name}.


name({var, Name}) ->
	Name.


is_valid({var, Name}) when is_atom(Name) ->
	true;

is_valid({var, Name}) when is_integer(Name) ->
	true;

is_valid({var, Name}) when is_bitstring(Name) ->
	true;

is_valid(_) ->
	false.


to_string({var, Name}) when is_atom(Name) ->
	atom_to_list(Name);

to_string({var, Name}) when is_integer(Name) ->
	integer_to_list(Name);

to_string({var, Name}) when is_bitstring(Name) ->
	bitstring_to_list(Name).



to_bitstring({var, Name}) when is_atom(Name) ->
	list_to_bitstring(atom_to_list(Name));

to_bitstring({var, Name}) when is_integer(Name) ->
	list_to_bitstring(integer_to_list(Name));

to_bitstring({var, Name}) when is_bitstring(Name) ->
	Name.

