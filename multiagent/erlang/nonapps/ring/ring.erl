-module(ring).
-export([run/1, start/1]).

run(N) ->
    Head = spawn(?MODULE, start, [N-1]),
    Head ! Head,
    Head.

start(N) ->
    erlang:display({self(), created}),
    Head = receive
        Pid when is_pid(Pid)-> Pid
    end,
    Next = case N of
        _ when N > 0 ->
             Spawn = spawn(?MODULE, start, [N-1]),
             Spawn ! Head,
             Spawn;
        _ -> Head
    end,
    erlang:display({self(), chained_with, Next}),
    loop(Next).

loop(Next) ->
    receive
        {NewN, new} ->
            erlang:display({self(), chained_with, NewN}),
            loop(NewN);
        {From, 1, Msg} ->
            handle(From, Msg, Next);
        {      1, Msg} ->
            handle(root, Msg, Next);
        {_   , M, Msg} ->
            Next ! {self(), M-1, Msg},
            loop(Next);
        {      M, Msg} ->
            Next ! {self(), M-1, Msg},
            loop(Next)
    after
        1 -> loop(Next)
    end.

handle(From, Msg, Next) ->
    case Msg of
        die ->
            case From of
                root ->
                    erlang:display({self(), cant_die}),
                    loop(Next);
                Prev ->
                    erlang:display({self(), died}),
                    Prev ! {Next, new}
            end;
        Txt ->
            erlang:display({self(), received, Txt}),
            loop(Next)
    end.