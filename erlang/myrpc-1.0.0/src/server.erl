-module(server).
-behavior(gen_server).

-export([start/0, slave/5, watcher/6]).
-export([init/1, terminate/2, handle_cast/2, handle_call/3]).


start() ->
    gen_server:start_link({local, ?MODULE}, ?MODULE, [], []).


slave(From, Key, Module, Func, Args) ->
    try apply(Module, Func, Args) of
        Value -> From ! {result_ok, Key, Value}
    catch
        Class:Error -> From ! {result_bad, Key, {Class,Error}}
    end.


watcher(Key, Timeout, Client, Module, Func, Args) ->
    process_flag(trap_exit, true),
    ClientRef = monitor(process, Client),
    Slave     = spawn_link(?MODULE, slave, [Client, Key, Module, Func, Args]),
    receive
        {'DOWN', ClientRef, _, _, _} ->
            log(watcher, client_down),
            exit(Slave, kill);
        {'EXIT', Slave, normal} ->
            ok;
        {'EXIT', Slave, Reason} ->
            log(watcher, {slave_down, Reason}),
            Client ! {result_bad, Key, {slave_down, Reason}},
            ok
    after
        Timeout ->
            exit(Slave, kill),
            Client ! {result_bad, Key, server_timeout}
    end.


log(Type, Message) ->
    erlang:display({Type, Message}).


% Callbacks.


init(State) ->
    {ok, State}.


terminate(_Reason, _State) ->
    ok.


handle_cast(stop, State) ->
    {stop, normal, State};

handle_cast(Message, State) ->
    log(unknown_cast, Message),
    {noreply, State}.


handle_call({Module, Func, Args, Timeout}, {From, _}, State) ->
    Key = erlang:phash2({node(), now()}),
    spawn_link(?MODULE, watcher, [Key, Timeout, From, Module, Func, Args]),
    {reply, Key, State};

handle_call(Message, _, State) ->
    log(unknown_call, Message),
    {reply, unknown_call, State}.
