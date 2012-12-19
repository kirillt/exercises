-module(supdb).
-behavior(supervisor).
-export([start/0]).
-export([init/1]).


% API


start() ->
    supervisor:start_link({local, ?MODULE}, ?MODULE, []).


% Callbacks.


init(_) ->
    {ok,
     {{one_for_one, 5, 1},
      [{gendb,
        {gendb, start, []},
        permanent,
        2000,
        worker,
        [gendb]}]}}.
