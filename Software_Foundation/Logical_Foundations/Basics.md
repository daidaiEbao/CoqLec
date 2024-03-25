## FUNCTIONAL PROGRAMMING IN COQ

### Introduction
- If a procedure or method has no side effects, then (ignoring efficiency) all we need to understand about it is how it maps inputs to outputs -- that is, we can think of it as just a concrete method for computing a mathematical function.

- The other sense in which functional programming is "functional" is that it emphasizes the use of functions as first-class values -- i.e., values that can be passed as arguments to other functions, returned as results, included in data structures, etc. 

### Data and Functions

#### Enumerated Types
Coq offers a powerful mechanism for defining new data types from scratch, with all these familiar types as instances.  

**e.g.** a type

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

**e.g.** a function

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

**e.g.** using ways

- First
``` Coq
Compute (next_weekday friday).
(* ==> monday : day *)

Compute (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)
```

- Second
``` Coq
Example test_next_weekday: 
	(next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.
```

- Third  
We can ask Coq to *extract*, from our Definition, a program in another, more conventional, programming language (OCaml, Scheme, or Haskell) with a high-performance compiler.



#### Booleans

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



#### Types

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



#### New Types from Old

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



#### Modules

If we enclose a collection of declarations between Module X and End X markers, then, **in the remainder of** the file after the End, these definitions are referred to by names like X.foo instead of just foo.

``` Coq
Module Playground.
  Definition myblue : rgb := blue.
End Playground.

Definition myblue : bool := true.

Check Playground.myblue : rgb.
Check myblue : bool.
```



#### Tuples

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



#### Numbers

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

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
(*   (* FILL IN HERE *) Admitted. *)
  intros b c.
  destruct b eqn:Eb.
  - simpl. intros H. rewrite H. reflexivity.
  - destruct c eqn:Ec.
    + simpl. intros H. reflexivity.
    + simpl. intros H. rewrite H. reflexivity.
Qed.
```



### More on Notation * Optional * 

For each notation symbol in Coq, we can specify its *precedence level* and its *associativity*.

Each notation symbol is also associated with a *notation scope*.

**Pro tip**: Coq's notation mechanism is not especially powerful. Don't expect too much from it.

> Personal Note:
How to erase the parentheses on the two sides of an operator? 
- The precedence level of the expression on the side same as associativity is less than or equal to the operator.
- The variable denoted by the expression could be computed in the definition of operator once at least. 

But how to add the parentheses could be confused sometime...

### Fixpoints and Structural Recursion * Optional *

Coq demands that some argument of *every* Fixpoint definition is "decreasing."

### Exs
- Exercise: 2 stars, standard (andb_true_elim2)
- Exercise: 3 stars, standard, optional (andb_eq_orb)  
- Exercise: 3 stars, standard (binary)
