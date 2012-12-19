-module(main).
-behavior(application).
-export([start/2, stop/1]).

start(_Type, _Args) ->
    supdb:start().

stop(_State) ->
    ok.
