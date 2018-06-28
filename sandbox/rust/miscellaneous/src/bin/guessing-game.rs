extern crate rand;

use std::{io, thread, time};
use std::cmp::Ordering;
use rand::Rng;

fn main() {
    let secret: u32 = rand::thread_rng().gen_range(1, 101);

    loop {
        println!("What's your guess?");
        let mut input = String::new();

        io::stdin()
            .read_line(&mut input)
            .expect("[Can't read user's input]");

        match input.trim().parse() {
            Ok(guess) => {
                println!("Your guess is {}", guess);

                let delay = time::Duration::from_millis(1000);
                thread::sleep(delay);
                println!("... aaaannndddd ...");
                thread::sleep(delay);

                match secret.cmp(&guess) {
                    Ordering::Less => println!("The goal is lower."),
                    Ordering::Equal => {
                        println!("This is correct answer!!!");
                        break;
                    }
                    Ordering::Greater => println!("The goal is higher.")
                }
            }
            Err(_) => println!("Try to guess a number!")
        }
    }
}
