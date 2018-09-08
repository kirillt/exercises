-module(main).
-behavior(application).
-export([start/2, stop/1]).

start(_Type, _Args) ->
    super:start().

stop(_State) ->
    ok.
