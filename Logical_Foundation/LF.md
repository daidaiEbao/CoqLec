

# VOLUME1: LOGICAL FOUNDATIONS

## FUNCTIONAL PROGRAMMING IN COQ

### Introduction

### Data and Functions

Enumerated Types

a type

```Coq
Inductive day : Type :=
	| monday
	| tuesday
	| wednesday
	| thursday
	| friday
	| saturday
	| sunday.
```

a function

>  the argument and return types of this function are explicitly declared

``` Coq
Definition next_weekday (d:day) : day :=
	match d with
	| monday => tuesday
	| tuesday => wednesday
	| wednesday => thursday
	| thursday => friday
	| friday => monday
	| saturday => monday
	| sunday => monday
	end.
```

using ways

``` Coq
Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)
```

``` Coq
Example test_next_weekday: 
	(next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.
```

Third, we can ask Coq to *extract*, from our Definition, a program in another, more conventional, programming language (OCaml, Scheme, or Haskell) with a high-performance compiler.



Booleans

``` Coq
Inductive bool : Type :=
	| true
	| false.
	
Definition andb (b1: bool) (b2: bool) : bool :=
	match b1 with
	| true => b2
	| false => false
	end.

Definition andb' (b1: bool) (b2: bool) : bool :=
	if b1 then b2
	else false.
	
Notation "x && y" := (andb x y).

Example test_andb: true && false = false.
Proof. simpl. reflexivity. Qed.
```

The last illustrate Coq's syntax for multi-argument function definitions.



Types

```Coq
Check true.
Check true
	: bool.
Check (negb true)
	: bool.
Check negb
	: bool -> bool.
Check andb 
	: bool -> bool -> bool.
```



New Types from Old

The types we have defined so far are examples of "enumerated types": their definitions explicitly enumerate a finite set of elements, called *constructors*. 

~~~ Coq
Inductive rgb : Type :=
	| red
	| green
	| blue.
	
Inductive color : Type :=
	| black
	| white
	| primary (p : rgb).
~~~

Inductive: defines and groups

Since the primary constructor takes an argument, a pattern matching primary should include either a variable or a constant of appropriate type.

```
Definition monochrome (c: color) : bool :=
	match c with
	| black => true
	| white => true
	| primary p => false
	end.
	
Definition isred (c: color) : bool :=
	match c with
	| black => false
	| white => false
	| primary red => true
	| primary _ => false
	end.
```

The pattern "primary _" here is shorthand for "the constructor primary applied to any rgb constructor except red." (The **wildcard pattern** _ has the same effect as the **dummy pattern** variable p in the definition of monochrome.)



Modules

If we enclose a collection of declarations between Module X and End X markers, then, **in the remainder of** the file after the End, these definitions are referred to by names like X.foo instead of just foo.

``` Coq
Module Playground.
  Definition myblue : rgb := blue.
End Playground.

Definition myblue : bool := true.

Check Playground.myblue : rgb.
Check myblue : bool.
```



Tuples

A single constructor with multiple parameters can be used to create a tuple type.

``` Coq
Inductive bit : Type :=
	| B0
	| B1.

Inductive nybble : Type :=
	| bits (b0 b1 b2 b3 : bit).

Check (bits B1 B0 B1 B0)
	: nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) ⇒ true
  | (bits _ _ _ _) ⇒ false
  end.
```

We use **underscore** (_) as a *wildcard pattern* to avoid inventing variable names that will not be used.



Numbers

``` Coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```

- the constructor expression O belongs to the set nat;
- if n is a constructor expression belonging to the set nat, then S n is also a constructor expression belonging to the set nat;

The names O and S are **arbitrary**, and at this point they have no special meaning

``` Coq
Definition pred (n : nat) : nat :=
  match n with
  | O ⇒ O
  | S n' ⇒ n'
  end.
  
Check (S (S (S (S O)))).
(* ===> 4 : nat *)
```

Because natural numbers are such a **pervasive** form of data, Coq provides a tiny bit of built-in magic for parsing and printing them

recursion

``` Coq
Fixpoint even (n:nat) : bool :=
	match n with
	| 0 => true
	| S 0 => false
	| S (S n') => even n'
	end.
```

### Proof by Simplification

 The proofs of these claims were always the same: use simpl to simplify both sides of the equation, then use reflexivity to check that both sides contain identical values.

because **reflexivity** can perform some simplification automatically when checking that two sides are equal; **simpl** was just added so that we could see the intermediate state -- after simplification but before finishing the proof. 

the keywords Example and Theorem (and a few others, including Lemma, Fact, and Remark) mean pretty much the same thing to Coq. 

``` Coq
Theorem mult_0_l : forall n:nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.
```

### Proof by Rewriting

``` Coq
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
  
Proof.
  (* move both quantifiers into the context: *)
  intros n m.
  (* move the hypothesis into the context: *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite -> H.
  reflexivity. Qed.
```

Since n and m are arbitrary numbers, we can't just use simplification to prove this theorem. Instead, we prove it by observing that, if we are assuming n = m, then we can replace n with m in the goal statement and obtain an equality with the same expression on both sides.



We can use the rewrite tactic with a previously proved theorem instead of a hypothesis from the context.



``` Coq
Check mult_n_O.
(* ===> forall n : nat, 0 = n * 0 *)

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  reflexivity. Qed.
```

### Proof by Case Analysis

``` Coq
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b eqn:Eb.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
  - destruct c eqn:Ec.
    + reflexivity.
    + reflexivity.
Qed.
```



More on Notation * Optional * 

For each notation symbol in Coq, we can specify its *precedence level* and its *associativity*.

Each notation symbol is also associated with a *notation scope*.

Pro tip: Coq's notation mechanism is not especially powerful. Don't expect too much from it.



Fixpoints and Structural Recursion * Optional *

Coq demands that some argument of *every* Fixpoint definition is "decreasing."



## PROOF BY INDUCTION

### Separate Compilation

``` Coq
From LF Require Export Basics.
```

This file is analogous to the .class files compiled from .java source files and the .o files compiled from .c files.

``` Coq
Theorem add_0_r_firsttry : ∀ n:nat,
  n + 0 = n.
```

using simpl. or destruct n. makes no sense. 

``` Coq
Theorem add_0_r : ∀ n:nat, n + 0 = n.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite → IHn'. reflexivity. Qed.
```

which IHn' means Induction Hypothesis for n' (n' + 0 = n')



the *principle of induction over natural numbers*

- show that P(O) holds;
- show that, for any n', if P(n') holds, then so does P(S n');
- conclude that P(n) holds for all n.



A typical example

``` Coq
Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n. induction n as [|n' IHn'].
  - intros m. induction m as [|m' IHm'].
    + simpl. reflexivity.
    + rewrite <- IHm'. simpl. reflexivity.
  - intros m. induction m as [|m' IHm'].
    + simpl. rewrite -> IHn'. reflexivity. 
    + rewrite <- IHm'. simpl. rewrite <- IHn'. rewrite <- IHn'. reflexivity.
  Qed.
```



### Proofs Within Proofs

But sometimes a proof will involve some **miscellaneous** fact that is too **trivial** and of too little general interest to bother giving it its own top-level name. In such cases, it is convenient to be able to simply state and prove the needed "sub-theorem" right *at the point where it is used*.

``` Coq
Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite -> H.
  reflexivity. Qed.
```

The *assert (H: n + 0 + 0 = n )* can be replaced by *assert (n + 0 + 0 = n) as H*.

``` Coq
Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
  { rewrite add_comm. reflexivity. }
  rewrite H. reflexivity. Qed.
```

So, assert has two features: 

- proof the trivial facts at the point where they are used. 
- precisely use the rewrite to the desired place. 



### Formal vs. Informal Proof

A proof of a mathematical proposition P is a written (or spoken) text that instills in the reader or hearer the certainty that P is true -- an unassailable argument for the truth of P. 

Some readers may be particularly pedantic, inexperienced, or just plain thick-headed; the only way to convince them will be to make the argument in painstaking detail.





## WORKING WITH STRUCTURED DATA

### Pair of Numbers

``` Coq
Inductive natprod : Type :=
  | pair (n1 n2 : nat).
```

This declaration can be read: "The one and only way to construct a pair of numbers is by applying the constructor pair to two arguments of type nat."

``` Coq
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y ⇒ x
  end.
  
Definition snd (p : natprod) : nat :=
  match p with
  | pair x y ⇒ y
  end.
  
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p. destruct p as [n m]. simpl. reflexivity. Qed.
```

Using p is the most natural way, but we should replace the p with [n m] by instruction destruct.



### List of Numbers

``` Coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```

``` Coq
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O ⇒ nil
  | S count' ⇒ n :: (repeat n count')
  end.
(* construct and manipulate *)

Fixpoint length (l:natlist) : nat :=
  match l with
  | nil ⇒ O
  | h :: t ⇒ S (length t)
  end.
(* calculate the length *)

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil ⇒ l2
  | h :: t ⇒ h :: (app t l2)
  end.
(* concatenate two lists *)

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
  | nil ⇒ default
  | h :: t ⇒ h
  end.
(* return the first element or default *)

Definition tl (l : natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ t
  end.
(* return everything but the first element *)
```

bags via lists

bags means multiset

``` Coq
Definition sum : bag -> bag -> bag
  (*(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.*)
:= 
(*alternate*) app
.
```



### Reasoning About Lists

``` Coq
Search (rev).
Search (_+_) in Induction.
Search (?x+?y = ?y+?x).
```

Using keyword *search* to find the theorem which has been proofed quickly. 



``` Coq
Theorem bag_count_sum: forall (n: nat) (s1 s2: bag), 
  count n s1 + count n s2 = count n (sum s1 s2).
Proof.
  intros n s1 s2. induction s1 as [|t s1' IHs1'].
  - simpl. reflexivity.
  - destruct (t =? n) eqn:E.
    + simpl. rewrite E. simpl. rewrite IHs1'. reflexivity.
    + simpl. rewrite E. rewrite IHs1'. reflexivity.
Qed.
```

The keyword *destruct* can works on arbitrary expressions as well. 



``` Coq
Theorem involution_injective : forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2 : nat, f n1 = f n2 -> n1 = n2).
Proof.
(*   (* FILL IN HERE *) Admitted. *)
  intros rev. intros H.
  intros n1 n2. intros H'.
  rewrite H. rewrite <- H'. rewrite <- H. reflexivity.
Qed.
```

Using keyword *intros* appropriately. 



### Partial Maps

```Coq
Inductive id : Type :=
  | Id (n : nat).

Theorem eqb_id_refl : forall x, eqb_id x x = true.
Proof.
(*   (* FILL IN HERE *) Admitted. *)
  intros (n). simpl. rewrite eqb_refl. reflexivity.
Qed.
```

The type id is just a wrapper for the type nat. We can using type nat with parentheses, following *intro*, so that to operate on type nat directly.  



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

## MORE BASIC TACTICS

### The apply Tactic
~~~Coq
apply x.
(*equals to*) 
rewrite -> x. reflexivity.
(*---------*)
symmetry. apply x.
(*switch the left and right sides of the goal*)
~~~

If you don't need 'reflexivity', you can use 'apply' wherever you used 'rewrite' before.  
Can **not** add lemma following 'apply'.

### The apply with Tactic
~~~Coq
Theorem trans_eq : ∀ (X:Type) (n m o : X),
  n = m → m = o → n = o.
Proof.
  intros X n m o eq1 eq2. rewrite → eq1. rewrite → eq2.
  reflexivity. Qed.

Example trans_eq_example' : ∀ (a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).(*'m:=' could be omiited*)
  apply eq1. apply eq2. Qed.

  Example trans_eq_example'' : ∀ (a b c d e f : nat),
     [a;b] = [c;d] →
     [c;d] = [e;f] →
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  transitivity [c;d].
  apply eq1. apply eq2. Qed.
  (*'transitivity' has accomplished the same purpose as using 'apply with'*)
~~~
'apply with' emphasize the match of the **type**. 
