#![allow(unused)]

use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::cell::{Cell, RefCell};
use std::pin::Pin;
use std::marker::PhantomPinned;
use std::ptr::NonNull;

type Res<T> = Option<T>;

trait Cont {
    fn call(&self, res: Res<&'static str>);
}

impl<T> Cont for T
where
    T: Fn(Res<&'static str>)
{
    fn call(&self, res: Res<&'static str>) {
        self(res)
    }
}

trait Parser {
    fn parse(&self, input: &'static str, cont: Rc<dyn Cont>);
}

impl<F> Parser for F
where
    F: Fn(&'static str, Rc<dyn Cont>)
{
    fn parse(&self, input: &'static str, cont: Rc<dyn Cont>) {
        self(input, cont)
    }
}

impl<T: Parser> Parser for Rc<T> {
    fn parse(&self, input: &'static str, cont: Rc<dyn Cont>) {
        <T>::parse(&**self, input, cont)
    }
}

#[derive(Clone, Copy)]
struct Terminal {
    t: &'static str
}

impl Parser for Terminal {
    fn parse(&self, input: &'static str, cont: Rc<dyn Cont>) {
        if input.starts_with(self.t) {
            let ret = &input[self.t.len()..];
            cont.call(Some(ret))
        } else {
            cont.call(None)
        }
    }
}

fn terminal(t: &'static str) -> Terminal {
    Terminal { t }
}

fn epsilon(input: &'static str, cont: Rc<dyn Cont>) {
    cont.call(Some(input))
}

fn seq<A, B>(a: A, b: B) -> impl Fn(&'static str, Rc<dyn Cont>)
where
    A: Parser,
    B: Parser + Clone + 'static,
{
    // TODO cache results
    move |input, cont| {
        let b = b.clone();
        let cont = cont.clone();
        let k = move |res| {
            if let Some(next) = res {
                b.parse(next, cont.clone())
            } else {
                cont.call(None)
            }
        };
        a.parse(input, Rc::new(k))
    }
}

fn alt<A, B>(a: A, b: B) -> impl Fn(&'static str, Rc<dyn Cont>)
where
    A: Parser,
    B: Parser,
{
    move |input, cont| {
        a.parse(input, cont.clone());
        b.parse(input, cont);
    }
}

type Table<T> = RefCell<HashMap<&'static str, T>>;

type RcMut<T> = Rc<RefCell<T>>;

struct Fix {
    cache: Table<(RcMut<HashSet<Res<&'static str>>>, RcMut<Vec<Rc<dyn Cont>>>)>,
    parser: RefCell<Option<Rc<dyn Parser>>>,
    builder: Box<dyn Fn(&'static Fix) -> Rc<dyn Parser>>,
    // pointing to self
    ptr: Cell<NonNull<Fix>>,
    _marker: PhantomPinned,
}

impl Parser for Fix {
    fn parse(&self, input: &'static str, cont: Rc<dyn Cont>) {
        if let Some((rs, ks)) = self.cache.borrow().get(&input) {
            // Self has been called at this position before
            ks.borrow_mut().push(cont.clone());
            for &res in rs.borrow().iter() {
                cont.call(res)
            }
            return;
        } 
        // First called at this position

        // create cache entry
        let rs = Rc::new(RefCell::new(HashSet::new()));
        let ks = Rc::new(RefCell::new(vec![cont.clone()])); // Just store the contiuation.

        // make a new contiuation for all sub branches.
        let rs_ = Rc::downgrade(&rs);
        let ks_ = Rc::downgrade(&ks);
        let k_i = move |res| {
            let rs = rs_.upgrade().unwrap();
            let new_result = !rs.borrow().contains(&res);
            if new_result {
                rs.borrow_mut().insert(res);
                let ks = ks_.upgrade().unwrap();
                for cont in ks.borrow().iter() {
                    cont.call(res);
                }
            }
        };

        self.cache.borrow_mut().insert(input, (rs, ks));
        let parser = self._build();
        parser.parse(input, Rc::new(k_i))
    }
}

impl Parser for &Fix {
    fn parse(&self, input: &'static str, cont: Rc<dyn Cont>) {
        <Fix>::parse(*self, input, cont)
    }
}

impl Fix {
    fn _build(&self) -> Rc<dyn Parser> {
        let key = self as *const Fix;
        if let Some(parser) = self.parser.borrow().as_ref() {
            // use cached
            let ptr = self.ptr.get().as_ptr() as *const Fix;
            assert_eq!(ptr, key);
            return parser.clone();
        }
        // called first time
        let fix = unsafe { key.as_ref().unwrap() }; // cast lifetime to 'static
        let parser = (*self.builder)(fix);
        let _ = self.parser.borrow_mut().replace(parser.clone());
        self.ptr.set(self.into());
        parser
    }

    fn new<P, F>(f: F) -> Pin<Box<Fix>>
    where
        P: Parser + 'static,
        F: 'static + Fn(&'static Fix) -> P
    {
        let cache = RefCell::new(HashMap::new());
        let ptr = Cell::new(NonNull::dangling());
        let parser = RefCell::new(None);
        let builder = move |fix| -> Rc<dyn Parser> {
            Rc::new(f(fix))
        };
        let builder = Box::new(builder);
        let fix = Fix {
            cache,
            ptr,
            parser,
            builder,
            _marker: PhantomPinned,
        };
        Box::pin(fix)
    }
}

macro_rules! fix {
    ($name:ident := $body:expr) => {
        Fix::new(move |$name: &'static Fix| $body)
    }
}

#[cfg(test)]
mod test {
    use super::{*, Parser, Cont};

    macro_rules! k {
        () => {{
            let k = |res| {
                println!("{:?}", res);
            };
            Rc::new(k)
        }}
    }

    fn expect(res: Option<&str>) {
        println!("expect {:?}", res);
    }

    #[test]
    fn parser_test() {
        let cont = k!();
        let ab = terminal("ab");
        expect(Some("c"));
        ab.parse("abc", cont.clone());

        let rule = seq(ab, terminal("/"));
        expect(Some("c"));
        rule.parse("ab/c", cont.clone());

        expect(None);
        rule.parse("abc", cont.clone());

        let rule = alt(rule, terminal("ab"));
        expect(Some(""));
        rule.parse("ab", cont);
    }

    #[test]
    fn fix_test() {
        let cont = k!();
        let rule = fix!(s := alt(terminal("a"), seq(terminal("b"), s)));
        expect(Some(""));
        rule.parse("ba", cont);
    }

    #[test]
    fn left_recursive() {
        let cont = k!();
        let a = terminal("a");
        let rule = fix!(s := alt(seq(s, a), a));
        rule.parse("aaa", cont);
    }
}
