use std::thread;
use std::sync::{Mutex, Arc};
use std::time::Duration;

struct Table {
    forks: Vec<Mutex<()>>
}

struct Philosopher {
    name: String,
    left: usize,
    right: usize
}

impl Philosopher {
    fn new(name: &str, left: usize, right: usize) -> Philosopher {
        Philosopher {
            name: name.to_string(),
            left: left, right: right
        }
    }

    fn eat(&self, table: &Table) {
        let _left = table.forks[self.left].lock().unwrap();
        thread::sleep(Duration::from_millis(100));
        let _right = table.forks[self.right].lock().unwrap();


        println!("{} started eating", self.name);

        thread::sleep(Duration::from_millis(1000));

        println!("{} finished eating", self.name);
    }
}

fn main() {
    let table = Arc::new(Table {
        forks: vec![
            Mutex::new(()),
            Mutex::new(()),
            Mutex::new(()),
            Mutex::new(()),
            Mutex::new(()),
        ]
    });

    let philosophers = vec![
        Philosopher::new("Glavny Filosof", 0, 1),
        Philosopher::new("Bolshoy Filosof", 1, 2),
        Philosopher::new("Sredny Filosof", 2, 3),
        Philosopher::new("Maly Filosof", 3, 4),
        Philosopher::new("Tral", 0, 4) //swapping 4 and 0 is the trick
    ];

    let handles: Vec<_> = philosophers.into_iter().map(|p| {
        let table= table.clone();
        thread::spawn(move || { p.eat(&table); })
    }).collect();

    for h in handles {
        h.join().unwrap();
    }
}