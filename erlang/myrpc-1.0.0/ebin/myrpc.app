{application, myrpc,
 [{description, "RPC TEST 123 45"},
  {vsn, "1.0.0"},
  {modules, [server, super, client]},
  {registered, [server, super]},
  {applications, [kernel, stdlib]},
  {mod, {main, []}}]}.
