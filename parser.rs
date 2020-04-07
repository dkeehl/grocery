use std::marker::PhantomData;
use std::rc::Rc;
use std::collections::{HashMap, HashSet};
use std::cell::RefCell;
use std::hash::Hash;

trait Cont<T> {
    fn run(&self, t: T);
}

impl<T, F> Cont<T> for F where F: Fn(T) {
    fn run(&self, t: T) {
        (self)(t)
    }
}

trait ParseResult {
    type Val;
    fn apply(&self, k: Rc<dyn Cont<Self::Val>>);
}

impl<T, R> ParseResult for Rc<R> where
    R: ParseResult<Val=T>
{
    type Val = T;

    fn apply(&self, k: Rc<dyn Cont<T>>) {
        <R>::apply(&*self, k)
    }
}

trait ParseResultAdapter: Sized {
    fn map<F>(self, map_f: F) -> Map<Self, F> {
        Map {
            res: self,
            map_f
        }
    }

    fn flat_map<F>(self, map_f: F) -> FlatMap<Self, F> {
        FlatMap {
            res: self,
            map_f
        }
    }

    fn or_else<F, U>(self, alt: F) -> OrElse<Self, F, U> where
        F: Fn() -> U
    {
        OrElse {
            res: self,
            alt,
            u: RefCell::new(None),
        }
    }
}

impl<T: ParseResult + Sized> ParseResultAdapter for T {}

struct Success<T> {
    t: T
}

impl<T: Clone> Success<T> {
    fn new(t: T) -> Self {
        Success { t }
    }
}

impl<T: Clone> ParseResult for Success<T> {
    type Val = T;
    fn apply(&self, k: Rc<dyn Cont<T>>) {
        k.run(self.t.clone())
    }
}

struct Failure<T> {
    _marker: PhantomData<T>
}

impl<T> Failure<T> {
    fn new() -> Self {
        Failure {
            _marker: PhantomData
        }
    }
}

impl<T> ParseResult for Failure<T> {
    type Val = T;
    fn apply(&self, _: Rc<dyn Cont<T>>) {}
}

fn success<T: Clone + 'static>(t: T) -> Rc<dyn ParseResult<Val=T>> {
    Rc::new(Success { t })
}

fn failure<T: 'static>() -> Rc<dyn ParseResult<Val=T>> {
    Rc::new(Failure::new())
}

struct Map<T, F> {
    res: T,
    map_f: F
}

impl<R, T, U, F> ParseResult for Map<R, Rc<F>> where
    U: 'static,
    R: ParseResult<Val=T>,
    F: 'static + ?Sized + Fn(T) -> U
{
    type Val = U;

    fn apply(&self, k: Rc<dyn Cont<U>>) {
        let map_f = self.map_f.clone();
        let k = move |t| k.run((map_f)(t));
        self.res.apply(Rc::new(k))
    }
}

struct FlatMap<T, F> {
    res: T,
    map_f: F,
}

impl<R, T, U, S, F> ParseResult for FlatMap<R, Rc<F>> where
    R: ParseResult<Val=T>,
    F: 'static + ?Sized + Fn(T) -> U,
    U: ParseResult<Val=S>,
    S: 'static
{
    type Val = S;

    fn apply(&self, k: Rc<dyn Cont<S>>) {
        let map_f = self.map_f.clone();
        let k_ = k.clone();
        let k = move |t| (map_f)(t).apply(k_.clone());
        self.res.apply(Rc::new(k))
    }
}

struct OrElse<T, F, U> {
    res: T,
    alt: F,
    u: RefCell<Option<U>>
}

impl<R, T, U, F> ParseResult for OrElse<R, F, U> where
    R: ParseResult<Val=T>,
    F: Fn() -> U,
    U: ParseResult<Val=T>
{
    type Val = T;

    fn apply(&self, k: Rc<dyn Cont<T>>) {
        let first_run = self.u.borrow().is_none();
        if first_run {
            let u = (self.alt)();
            let _ = self.u.borrow_mut().replace(u);
        }
        self.res.apply(k.clone());
        self.u.borrow().as_ref().unwrap().apply(k);
    }
}

type Ret = usize;

trait Recognizer {
    fn recognize(&self, input: &str, i: usize)
        -> Rc<dyn ParseResult<Val=Ret>>;
}

struct MemoizedResult<T, R> {
    rs: Rc<RefCell<HashSet<T>>>,
    ks: Rc<RefCell<Vec<Rc<dyn Cont<T>>>>>,
    res: R
}

impl<T, R> ParseResult for MemoizedResult<T, Rc<R>> where
    R: ParseResult<Val=T> + ?Sized,
    T: Clone + Hash + Eq + 'static
{
    type Val=T;

    fn apply(&self, k: Rc<dyn Cont<T>>) {
        let first_call = self.ks.borrow().is_empty();
        if first_call {
            self.ks.borrow_mut().push(k);
            let rs = Rc::downgrade(&self.rs);
            let ks = Rc::downgrade(&self.ks);
            let k_i = move |t| {
                let rs = rs.upgrade().unwrap();
                let ks = ks.upgrade().unwrap();
                let called_here = rs.borrow().contains(&t);
                if !called_here {
                    rs.borrow_mut().insert(t.clone());
                    for k in ks.borrow().iter() {
                        k.run(t.clone());
                    }
                }
            };
            //  Maybe res should init at this time?
            self.res.apply(Rc::new(k_i));
        } else {
            self.ks.borrow_mut().push(k.clone());
            for t in self.rs.borrow().iter() {
                k.run(t.clone());
            }
        }
    }
}

impl<T> MemoizedResult<T, Rc<dyn ParseResult<Val=T>>> where
    T: Clone + Hash + Eq + 'static
{
    fn new(res: Rc<dyn ParseResult<Val=T>>) -> Self {
        let rs = Rc::new(RefCell::new(HashSet::new()));
        let ks = Rc::new(RefCell::new(vec![]));
        MemoizedResult { rs, ks, res }
    }
}

struct MemoizedRecognizer<T> {
    cache: RefCell<HashMap<usize, Rc<dyn ParseResult<Val=Ret>>>>,
    rec: T
}

impl<T> Recognizer for MemoizedRecognizer<T> where
    T: Recognizer
{
    fn recognize(&self, input: &str, i: usize)
        -> Rc<dyn ParseResult<Val=Ret>>
    {
        let t = self.cache.borrow();
        if let Some(res) = t.get(&i) {
            return res.clone();
        }
        let res = self.rec.recognize(input, i);
        let res = MemoizedResult::new(res);
        let res: Rc<dyn ParseResult<Val=Ret>> = Rc::new(res);
        self.cache.borrow_mut().insert(i, Rc::clone(&res));
        res
    }
}
