-module(quick).
-import(array, [
    get/2, set/3,
    to_list/1, from_list/1,
    size/1, fix/1, is_array/1]).
-export([sort/1, test/3, plot/3, read_lines/1]).

-compile({no_auto_import,[size/1]}).

sort(List ) when is_list (List) ->
    to_list(sort(from_list(List)));
sort(Array) ->
    case size(Array) of
        0 -> Array;
        _ -> sort_(fix(Array))
    end.

sort_(Array) ->
    sort_(0, size(Array)-1, Array).
sort_(L, R, Array) when L >= R ->
    Array;
sort_(L, R, Array) when R == L + 1 ->
    Lv = get(L, Array),
    Rv = get(R, Array),
    case Lv > Rv of
        false -> Array;
        true  -> set(L, Rv, (set(R, Lv, Array)))
    end;
sort_(L, R, Array) ->
    P  = (L + R) div 2, Array,
    Pv = get(P, Array),
    {NewP, NewArray} = reorder(L, R, P, Pv, Array),
    sort_(NewP+1, R, sort_(L, NewP-1, NewArray)).


% Reorder array such way that
% all elements from left  are less    than pivot
% and
% all elements from right are greater than pivot.

reorder(         L, R, P, Pv, Array) ->
    Lv = get(L, Array),
    case Lv < Pv of
        true  -> reorder(         L+1, R  , P, Pv, Array);
        false -> reorder({Lv},    L  , R  , P, Pv, Array)
    end.
reorder({Lv   }, L, R, P, Pv, Array) ->
    Rv = get(R, Array),
    case Rv > Pv of
        true  -> reorder({Lv},    L  , R-1, P, Pv, Array);
        false -> reorder({Lv,Rv}, L  , R  , P, Pv, Array)
    end;
reorder({Lv,Rv}, L, R, P, Pv, Array) ->
    case {L,R} of
        _ when L >= R ->
             {P, Array};
        _ ->
             NewArray = set(L, Rv, set(R, Lv, Array)),
             {NewL, NewR, NewP, NewPv} = case {L,R,P} of
                 _ when L == P -> {L+1, R, R, Lv}; % Lv is value of new P
                 _ when R == P -> {L, R-1, L, Rv}; % Rv is value of new P
                 _ -> {L+1, R-1, P, Pv}
             end,
             reorder(NewL, NewR, NewP, NewPv, NewArray)
    end.


% Testing and performance measuring function.
% Generates Count random lists of length = Length
% with elements from 1 to MaxValue and compares
% quick sort with bubble sort on them.

test(MaxValue, Length, Count) ->
    test(MaxValue, Length, Count, 0, {0,[]}, {0,0}).
test(MaxValue, Length, Count, I, {N,List}, Time) ->
    case I =< Count of
        true  -> 
            case {N,Length} of
                _ when N < Length ->
                    NewElement = random:uniform(MaxValue),
                    test(MaxValue, Length, Count, I, {N+1,[NewElement|List]}, Time);
                _ ->
                    OurStart  = now(),
                    OurResult = sort(List),
                    OurFinish = now(),
                    OurDiff   = timer:now_diff(OurFinish, OurStart),

                    ReqStart  = now(),
                    ReqResult = lists:sort(List),
                    ReqFinish = now(),
                    ReqDiff   = timer:now_diff(ReqFinish, ReqStart),

%                   erlang:display({test  , List  }),
%                   erlang:display({result, {our_time, OurDiff}, {erlang_time, ReqDiff}, OurResult}),
                    case OurResult == ReqResult of
                        true  ->
                            {OurTime, ReqTime} = Time,
                            test(MaxValue, Length, Count, I+1, {0,[]}, {OurTime + OurDiff, ReqTime + ReqDiff});
                        false ->
                            {test_failed, List}
                    end
            end;
        false ->
            {OurTime, ReqTime} = Time,
            {   {tests_amount, Count},
                {average_time,
                    {our   , OurTime / Count},
                    {erlang, ReqTime / Count},
                    {propor, OurTime / ReqTime}}}
    end.


% Builds list with elements (N,Time) for input list of Ns.

plot(MaxValue, Count, Ns) ->
    Lambda = fun(N) ->
        erlang:display({length,N}),
        {_,{_,{our,OurTime},{erlang, ReqTime},_}} = quick:test(MaxValue, N, Count),
        {OurTime,ReqTime}
    end,
    lists:map(Lambda, Ns).


% Reading lines from specified file.

read_lines(Path) when is_list(Path) ->
    {ok, File} = file:open(Path, [read]),
    read_lines(File, []).
read_lines(File, Acc) ->
    case file:read_line(File) of
        {ok, Data} -> read_lines(File, [Data|Acc]);
        eof -> Acc
    end.