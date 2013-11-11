-module(client).
-export([run/0, mail/0]).
 
run() ->
   case is_alive() of
       true  ->
           Mail = spawn(client, mail, []),
           loop(Mail);
       false -> not_alive
   end.
 
mail() ->
   receive
       Respond ->
           erlang:display(Respond),
           mail()
   end.
 
loop(Mail) ->
   case io:read("request$ ") of
       {ok, leave} ->
           leave;
       {ok, Data } ->
           {store, master@ubuntu} ! {Data, Mail},
           loop(Mail);
       _ ->
           erlang:display(bad_request),
           loop(Mail)
   end.