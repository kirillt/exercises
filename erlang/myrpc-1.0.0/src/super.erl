-module(super).
-behavior(supervisor).
-export([start/0]).
-export([init/1]).


start() ->
    supervisor:start_link({local, ?MODULE}, ?MODULE, []).


% Callbacks.


init(_) ->
    {ok,
     {{one_for_one, 5, 1},
      [{server,
        {server, start, []},
        permanent,
        2000,
        worker,
        [server]}]}}.
