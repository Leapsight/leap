%% =============================================================================
%% Copyright (C) NGINEO LIMITED 2011 - 2016. All rights reserved.
%% =============================================================================

-define(VAR(Term), leap_var:new(Term)).

-define(IS_VAR(Term), 
    tuple_size(Term) =:= 2 andalso element(1, Term) == var andalso 
    (
        is_atom(element(2, Term)) orelse 
        is_integer(element(2, Term)) orelse 
        is_binary(element(2, Term))
    )
).