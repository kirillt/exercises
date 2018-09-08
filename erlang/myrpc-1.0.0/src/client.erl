-module(client).
-export([call/4, async_call/4, yield/1, multicall/4]).
-compile(export_all).


call(Node, Module, Func, Args) ->
    call(Node, Module, Func, Args, 20000).


call(Node, Module, Func, Args, Timeout) ->
    Key = async_call(Node, Module, Func, Args, Timeout),
    yield(Key, Timeout+100).


async_call(Node, Module, Func, Args) ->
    async_call(Node, Module, Func, Args, 20000).


async_call(Node, Module, Func, Args, Timeout) ->
    gen_server:call({server, Node}, {Module, Func, Args, Timeout}).


yield(Key) ->
    yield(Key, 20000).


yield(Key, Timeout) ->
    receive
        {result_ok , Key, Result} -> Result;
        {result_bad, Key, Info  } -> {bad_rpc, Info}
    after
        Timeout -> timeout
    end.


multicall(Nodes, Module, Func, Args) ->
    multicall(Nodes, Module, Func, Args, 20000).


multicall(Nodes, Module, Func, Args, Timeout) ->
    KeysWithNodes = lists:map(
        fun(Node) ->
            {async_call(Node, Module, Func, Args, Timeout), Node}
        end,
        Nodes),
    multiyield([], KeysWithNodes, Timeout+100).

multiyield(Acc, [], _) ->
    Acc;

multiyield(Acc, [{Key,Node}|Tail], Timeout) ->
    Start = now(),
    Entry = receive
        {result_ok , Key, Result} -> {Node, Result};
        {result_bad, Key, Info  } -> {Node, {bad_rpc, Info}}
    after
        Timeout -> {Node, {bad_rpc, node_timeout}}
    end,
    multiyield(
        [Entry|Acc], Tail,
        max(0, Timeout - timer:now_diff(now(), Start))).
