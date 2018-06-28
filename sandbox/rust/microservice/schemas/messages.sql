create table messages (
    id serial primary key,
    username varchar(128) not null,
    message text not null,
    timestamp bigint not null default extract('epoch' from current_timestamp)
)
