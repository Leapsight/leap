H = {{var,scheme}, {var,host}, {var,realm}, {var,path}, {var,mod}, {var,state}}.
L = [
    {http, "api.com", "realm:foo", "/a", a, #{}},
    {http, "admin.api.com", "realm:bar", "/b", b, #{}},
    {https, "api.com", "realm:foo", "/b", b, #{}},
    {https, "api.com", "realm:foo", "/c", c, #{}},
    {http, "admin.api.com", "realm:bar", "/c", c, #{}}
].
R = leap_relation:relation(H, L).
RR = leap_relation:summarize(R, {{var,scheme}, {var, host}, {as, {function, collect, [{var, path}, {var, mod}, {var,state}]}, {var, foo}}}, #{}).

leap_relation:summarize(RR, {{var,scheme}, {function, collect, [{var, host}, {var,<<"CollectOfpathmodstate">>}]}}, #{}).