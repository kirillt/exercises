#![feature(proc_macro_non_items)]
#![feature(proc_macro)]
extern crate maud;

extern crate url;
extern crate hyper;
extern crate futures;

#[macro_use]
extern crate log;
extern crate env_logger;

#[macro_use]
extern crate serde_json;
#[macro_use]
extern crate serde_derive;
#[macro_use]
extern crate diesel;

mod schema;
mod models;

use models::{Message, NewMessage};

use maud::html;

use hyper::{StatusCode, Chunk};
use hyper::Method::{Get, Post};
use hyper::header::{ContentType, ContentLength};
use hyper::server::{Request, Response, Service};

use diesel::pg::PgConnection;
use diesel::prelude::*;

use futures::future::{Future, FutureResult};
use futures::Stream;

use std::collections::HashMap;
use std::error::Error;
use std::env;
use std::io;

struct Microservice;

impl Service for Microservice {
    type Request = Request;
    type Response = Response;
    type Error = hyper::Error;
    type Future = Box<Future<Item = Self::Response, Error = Self::Error>>;

    fn call(&self, request: Request) -> Self::Future {
        let db = match connect_to_db() {
            Some(connection) => connection,
            None => return Box::new(futures::future::ok(
                Response::new().with_status(StatusCode::InternalServerError)
            ))
        };

        match (request.method(), request.path()) {
            (&Post, "/") => {
                let future = request.body()
                    .concat2()
                    .and_then(parse_form)
                    .and_then(move |msg| write_to_db(&db, msg))
                    .then(make_post_response);
                Box::new(future)
            }
            (&Get, "/") => {
                let range = request.query()
                    .map(parse_query)
                    .unwrap_or(Ok(TimeRange {
                        before: None,
                        after: None
                    }));

                let response = match range {
                    Ok(range) => make_get_response(query_db(&db, range)),
                    Err(msg) => make_error_response(&msg[..])
                };
                Box::new(response)
            }
            _ => {
                info!("Received: {:?}", request);
                Box::new(futures::future::ok(Response::new()
                    .with_status(StatusCode::NotFound)))
            }
        }
    }
}


fn parse_fields(bytes: &[u8]) -> HashMap<String, String> {
    url::form_urlencoded::parse(bytes)
        .into_owned()
        .collect()
}

struct TimeRange {
    before: Option<i64>,
    after: Option<i64>
}

fn parse_query(query: &str) -> Result<TimeRange, String> {
    let query = parse_fields(query.as_bytes());

    let before = query.get("before").map(|value| value.parse::<i64>());
    if let Some(ref result) = before {
        if let Err(ref error) = *result {
            return Err(format!("Can't parse 'before' argument: {}", error));
        }
    }

    let after = query.get("after").map(|value| value.parse::<i64>());
    if let Some(ref result) = after {
        if let Err(ref error) = *result {
            return Err(format!("Can't parse 'after' argument: {}", error));
        }
    }

    Ok(TimeRange {
        before: before.map(|b| b.unwrap()),
        after: after.map(|a| a.unwrap())
    })
}

fn query_db(db: &PgConnection, range: TimeRange) -> Option<Vec<Message>> {
    use schema::messages;

    let TimeRange { before, after } = range;

    let mut query = messages::table.into_boxed();

    if let Some(after) = after {
        query = query.filter(messages::timestamp.gt(after as i64));
    }
    if let Some(before) = before {
        query = query.filter(messages::timestamp.lt(before as i64));
    }

    let result = query.load::<Message>(db);
    match result {
        Ok(result) => Some(result),
        Err(error) => {
            error!("Couldn't retrieve messages from database: {}", error);
            None
        }
    }
}

fn parse_form(form_chunk: Chunk) -> FutureResult<NewMessage, hyper::Error> {
    let mut form = parse_fields(&form_chunk[..]);

    if let Some(message) = form.remove("message") {
        let username = form.remove("username").unwrap_or("anonymous".to_string());
        futures::future::ok(NewMessage {
            username, message
        })
    } else {
        futures::future::err(hyper::error::Error::from(io::Error::new(
            io::ErrorKind::InvalidInput, "Missing field 'message'")))
    }
}

fn write_to_db(db: &PgConnection, msg: NewMessage) -> FutureResult<i64, hyper::Error> {
    use schema::messages;
    let timestamp = diesel::insert_into(messages::table)
        .values(&msg)
        .returning(messages::timestamp)
        .get_result(db);

    match timestamp {
        Ok(timestamp) => futures::future::ok(timestamp),
        Err(error) => {
            error!("Couldn't write to database: {}", error.description());
            futures::future::err(hyper::Error::from(
                io::Error::new(io::ErrorKind::Other, "service error")
            ))
        }
    }
}

fn make_error_response(msg: &str)
    -> FutureResult<hyper::Response, hyper::Error> {

    let payload = json!({"error": msg}).to_string();
    let response = Response::new()
        .with_status(StatusCode::InternalServerError)
        .with_header(ContentLength(payload.len() as u64))
        .with_header(ContentType::json())
        .with_body(payload);

    debug!("{:?}", response);
    futures::future::ok(response)
}

fn make_post_response(result: Result<i64, hyper::Error>)
    -> FutureResult<hyper::Response, hyper::Error> {

    match result {
        Ok(timestamp) => {
            let payload = json!({"timestamp": timestamp}).to_string();
            let response = Response::new()
                .with_header(ContentLength(payload.len() as u64))
                .with_header(ContentType::json())
                .with_body(payload);

            debug!("{:?}", response);
            futures::future::ok(response)
        }
        Err(error) => make_error_response(error.description())
    }
}

fn make_get_response(messages: Option<Vec<Message>>)
    -> FutureResult<hyper::Response, hyper::Error> {

    let response = match messages {
        Some(messages) => {
            let body = render_page(messages);
            Response::new()
                .with_header(ContentLength(body.len() as u64))
                .with_body(body)
        }
        None => Response::new().
            with_status(StatusCode::InternalServerError)
    };
    debug!("{:?}", response);
    futures::future::ok(response)
}

const DEFAULT_DATABASE_URL: &'static str = "postgresql://postgres@localhost:5432";

fn connect_to_db() -> Option<PgConnection> {
    let url = env::var("DATABASE_URL").unwrap_or(String::from(DEFAULT_DATABASE_URL));
    info!("db url: {}", url);
    match PgConnection::establish(&url) {
        Ok(connection) => Some(connection),
        Err(error) => {
            error!("Couldn't connect to database: {}", error.description());
            None
        }
    }
}

fn render_page(messages: Vec<Message>) -> String {
    (html! {
        head {
            title "microservice"
            style "body { font-family: monospace }"
        }
        body {
            ul {
                @for message in &messages {
                    li {
                        (message.username) " (" (message.timestamp) "): " (message.message)
                    }
                }
            }
        }
    }).into_string()
}


fn main() {
    env_logger::init();
    let address = "127.0.0.1:8080".parse().unwrap();
    let server = hyper::server::Http::new()
        .bind(&address, || Ok(Microservice {}))
        .unwrap();
    info!("Starting at {}", address);
    server.run().unwrap();
}
