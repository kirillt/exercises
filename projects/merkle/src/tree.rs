#[derive(Debug)]
#[derive(Clone)]
pub enum Tree<T> {
    Nil, Leaf(T),
    // sacrificing code simplicity for the sake of structure compactness

    Join {
        left: Box<Tree<T>>,
        right: Box<Tree<T>>,
        value: T
    }
}

impl<T> Tree<T> {
    fn nil() -> Box<Tree<T>> {
        Box::new(Tree::Nil)
    }

    fn leaf(value: T) -> Box<Tree<T>> {
        Box::new(Tree::Leaf(value))
    }

    fn join(left: T, right: T) -> Tree<Option<T>> {
        Tree::Join {
            left: Tree::leaf(Some(left)),
            right: Tree::leaf(Some(right)),
            value: None
        }
    }

    fn from_forest(forest: Vec<Tree<Option<T>>>) -> Tree<Option<T>> {
        let chunks: Vec<&[Tree<Option<T>>]> = forest.chunks(2).collect();
        match chunks.split_last() {
            Some((last, pairs)) => {
                let mut forest: Vec<Tree<Option<T>>> = pairs.into_iter().map({ |chunk|
                    Tree::Join {
                        left: Box::new(chunk[0]), right: Box::new(chunk[1]),
                        value: None
                    }
                }).collect();

                let odd: Tree<_> = last[0];
                let last = match last.get(1) {
                    Some(even) => Tree::Join {
                        left: Box::new(odd), right: Box::new(*even),
                        value: None
                    },
                    None => odd
                };

                //todo: recursive call
                forest.push(last);
                forest
            },
            None => Tree::Nil
        }
    }

    fn from_leaves(values: Vec<T>) -> Tree<Option<T>> {
        let forest: Vec<Tree<_>> = values.into_iter().map(|v| Tree::leaf(v)).collect();
        Tree::from_forest(forest)
    }
}

pub fn test() {
    println!("{:?}", Tree::leaf(1));

//    let v = vec![1,2,3];
//    let x: Vec<&[u8]> = v.chunks(2).collect();
//    println!("{:?}", x);

    println!("{:?}", Tree::join(1,2));
}