-module(gendb).
-behavior(gen_server).
-export([start/0, stop/0, write/2, read/1, delete/1, match/1, find/1]).
-export([init/1, terminate/2, handle_cast/2, handle_call/3]).


% API


start() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).


stop() ->
    gen_server:cast(?MODULE, stop).


write(K, V) ->
    gen_server:call(?MODULE, {K,V}).


delete(K) ->
    gen_server:call(?MODULE, {delete, K}).


read(K) ->
    gen_server:call(?MODULE, {read  , K}).


match(V) ->
    gen_server:call(?MODULE, {match , V}).


find(P) ->
    gen_server:call(?MODULE, {find  , P}).


% Callbacks.


init(State) ->
    {ok, State}.


terminate(_Reason, _State) ->
    ok.


handle_cast(stop, State) ->
    {stop, normal, State};

handle_cast(Message, State) ->
    {_, NewState} = process(Message, State),
    log(unknown_message, Message),
    {noreply, NewState}.


handle_call(Message, _, State) ->
    {R,NewState} = process(Message, State),
    {reply, R, NewState}.


process({read  ,Ks}, State) ->
    {lists:filter(
        fun({Kr,_}) -> Kr =:= Ks end,
        State),
     State};

process({match ,Vs}, State) ->
    {lists:filter(
        fun({_,Vr}) -> Vs =:= Vr end,
        State),
     State};

process({find  ,Pr}, State) ->
    {lists:filter(Pr, State), State};

process({delete,Ks}, State) ->
    {ok, lists:filter(
            fun({Kr,_}) -> Ks =/= Kr end,
            State)};

process({K,V}, State) ->
    {ok, [{K,V}|State]};

process(Msg  , State) ->
    log(unknown_message, Msg),
    {unknown_message, State}.


log(Type, Message) ->
    erlang:display({Type, Message}).
