# --- !Ups

create table "account" (
  "name" varchar not null primary key,
  "balance" decimal not null,
  "deposited" decimal not null,
  "deposits" smallint not null,
  "lastDeposit" date not null,
  "withdrawn" decimal not null,
  "withdrawals" smallint not null,
  "lastWithdrawal" date not null,
);

insert into "account" ("name", "balance",
    "deposited", "deposits", "lastDeposit",
    "withdrawn", "withdrawals", "lastWithdrawal")
  values ('badumtss', 1337,
    3000, 1, '2017-12-21',
    1663, 1, '2017-12-21');

# --- !Downs

drop table "account" if exists;