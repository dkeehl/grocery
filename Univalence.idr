%default total

data Id : {ty: Type} -> ty -> ty -> Type where
  Refl : Id x x

j : {ty : Type} ->
    (a : (x, y: ty) -> Id x y -> Type) ->
    (f : (z: ty) -> a z z Refl) ->
    (x', y': ty) -> (p: Id x' y') ->
    a x' y' p
j a f x' _ Refl = f x'

IsSingleton : Type -> Type
IsSingleton ty = (c: ty ** (x: ty) -> Id c x)

Fiber : (a -> b) -> b -> Type
Fiber {a} f y = (x: a ** Id (f x) y)

IsEquiv : (a -> b) -> Type
IsEquiv {b} f = (y: b) -> IsSingleton (Fiber f y)

Eq : Type -> Type -> Type
Eq a b = (f: (a -> b) ** IsEquiv f)

SingletonType : a -> Type
SingletonType {a} x = (y: a ** Id y x)

eta : (x: a) -> SingletonType x
eta x = (x ** Refl)

singletonTypesAreSingletons : (x: a) -> IsSingleton (SingletonType x)
singletonTypesAreSingletons x {a} = (eta x ** g x)
  where
    A : (y, z: a) -> Id y z -> Type
    A y z p = Id (eta z) (y ** p)

    phi : (y, z: a) -> (p: Id y z) -> Id (eta z) (y ** p)
    phi = j A (\x => Refl)

    g : (z: a) -> (sig: SingletonType z) -> Id (eta z) sig
    g z (y ** p) = phi y z p
    
idIsEquiv : (a: Type) -> IsEquiv (id {a=a})
idIsEquiv a = singletonTypesAreSingletons

idToEq : (a, b: Type) -> Id a b -> Eq a b
idToEq = j A f
  where
    A : (a: Type) -> (b: Type) -> Id a b -> Type
    A a b _ = Eq a b

    f : (ty: Type) -> A ty ty Refl
    f ty = (id {a=ty} ** idIsEquiv ty)

IsUnivalent : Type
IsUnivalent = (a, b: Type) -> IsEquiv (idToEq a b)

k : (a, b: Type) -> (p, q: Id a b) -> Id p q
k b b Refl Refl = Refl

uaUninhabited: IsUnivalent -> Void
uaUninhabited ua = contraToK
  where
    Point : Type
    Point = SingletonType ()

    pointEq : Eq Unit Point
    pointEq = (f ** p)
      where
        f : Unit -> Point
        f _ = eta ()

        p : IsEquiv f
        p (_ ** Refl) = (fiber ** fiberId)
          where
            fiber : Fiber f (() ** Refl)
            fiber = (() ** Refl)

            fiberId : (q: Fiber f (() ** Refl)) -> Id fiber q
            fiberId = \(() ** Refl) => Refl

    kBuiltin : Id Unit Point -> Void
    kBuiltin Refl impossible

    contraToK : Void
    contraToK = let ((pid ** _) ** _) = ua Unit Point pointEq in
                    kBuiltin pid

