The application is designed with multi-user setting in mind.
File-based H2 database selected as storage. Account "badumtss" is created by default.
You can add accounts with "create" endpoint. Specify name when use other endpoints (see examples below).

The application creates database files "accounts.storage.*" in current directory.
If you want to clean up the storage -- just do "rm accounts.storage.*".

====================================================================================================================

Build and run:
$ sbt run

====================================================================================================================

Create account:
curl -X POST localhost:9000/create/username

Get balance:
curl -X GET localhost:9000/balance/username

Deposit:
curl -X POST localhost:9000/deposit -H "Content-Type: application/json" -d '{"name":"username", "amount":"10"}'

Withdrawal:
curl -X POST localhost:9000/withdrawal -H "Content-Type: application/json" -d '{"name":"username", "amount":"10"}'

====================================================================================================================