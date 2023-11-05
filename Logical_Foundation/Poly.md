## POLYMORPHISM ADN HIGHER-ORDERED FUNCTIONS

### Polymorphism

Polymorphic lists

``` Coq
Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).
  
Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.
  
Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.
  
Fixpoint repeat'' X x count : list X :=
  match count with
  | 0 ⇒ nil _
  | S count' ⇒ cons _ x (repeat'' _ x count')
  end.
  
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.
```



``` Coq
Fail Definition mynil := nil.


Check @nil : forall X : Type, list X.
Definition mynil' := @nil nat.
```

Polymorphic pair

``` Coq
Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y}.

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.
```





Polymorphic Options

``` Coq
Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X}.
Arguments None {X}.
```



### Function as Data

Functions that manipulate other functions are often called *higher-order* functions.

``` Coq
Definition doit3times {X : Type} (f : X->X) (n : X) : X :=
  f (f (f n)).
```

filter

``` Coq
Fixpoint filter {X:Type} (test: X->bool) (l:list X) : list X :=
  match l with
  | [] => []
  | h :: t =>
    if test h then h :: (filter test t)
    else filter test t
  end.
```

Anonymous function

``` Coq
Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
(*   (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted. *)
:=
(filter test l, filter (fun X => negb (test X)) l).
```

Map

``` Coq
Fixpoint map {X Y : Type} (f : X->Y) (l : list X) : list Y :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.
```

Fold

```Coq
Fixpoint fold {X Y: Type} (f : X->Y->Y) (l : list X) (b : Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.
```

Functions that construct functions

```Coq
Definition constfun {X: Type} (x: X) : nat -> X :=
  fun (k:nat) => x.


Check plus : nat -> nat -> nat.
Definition plus3 := plus 3.
Check plus3 : nat -> nat.
```

keyword *unfold*

``` Coq
Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
(*   (* FILL IN HERE *) Admitted. *)
  intros X Y Z f x y.
  unfold prod_uncurry.
  unfold prod_curry.
  simpl.
  reflexivity.
Qed.


Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
(*   (* FILL IN HERE *) Admitted. *)
  intros X Y Z f p.
  unfold prod_curry.
  unfold prod_uncurry.
  destruct p.
  simpl.
  reflexivity.
Qed.
```