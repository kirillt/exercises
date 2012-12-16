-module(server).
-export([master/0, slave/0]).

master() ->
   register(store, self()),
   master_loop(0, array:new(), []).

master_loop(N, Slaves, SlavesList) ->
   receive
       {slave       , From} ->
           master_loop(N+1, array:set(N, From, Slaves), [From|SlavesList]);
       {info        , From} ->
           From ! {slaves, {N, SlavesList}},
           master_loop(N  , Slaves, SlavesList);
       {{set, {K,V}}, From} ->
           send2slaves(SlavesList, {{set, {K,V}}}),
           From ! {setted, {K,V}},
           master_loop(N, Slaves, SlavesList);
       {Request     , From} ->
           random_slave(N , Slaves) ! {Request, From},
           master_loop(N  , Slaves, SlavesList)
   end.

send2slaves([   ], _  ) ->
   ok;

send2slaves([H|T], Msg) ->
   H ! Msg,
   send2slaves(T, Msg).

random_slave(N, Slaves) ->
   I = random:uniform(N)-1,
   array:get(I, Slaves).

slave() ->
   {store, master@ubuntu} ! {slave, self()},
   slave_loop(ets:new(table, [set])).

slave_loop(Table) ->
   receive
       {{set, {K,V}}} ->
           ets:insert(Table, {K,V}),
           slave_loop(Table);
       {{get,  K    }, From} ->
           Result = ets:lookup(Table, K),
           From ! {result, Result},
           slave_loop(Table);
       {_           , From} ->
           From ! bad_request,
           slave_loop(Table)
   end.