{application, db,
 [{description, "DB TEST 123 45"},
  {vsn, "1.0.0"},
  {modules, [gendb, supdb]},
  {registered, [gendb, supdb]},
  {applications, [kernel,stdlib]},
  {mod, {main,[]}}]}.
