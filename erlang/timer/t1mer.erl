-module(t1mer).
-export([start/0]).

start() ->
    register(timer_service, self()),
    loop([]).

loop(Entries) ->
    Entries1 = process(Entries, []),
    Entries2 = receive
        {register, Pid, Period} -> [ {Pid, Period, now()} | Entries1 ]
    after
        1 -> Entries1
    end,
    loop(Entries2).

process([   ], Acc) ->
    Acc;
process([ {Pid, Period, Start} | T ], Acc) ->
    NewStart = case timer:now_diff(now(), Start) >= Period of
        true  -> Pid ! timer_event, now();
        false -> Start
    end,
    process(T, [ {Pid, Period, NewStart} | Acc ]).
