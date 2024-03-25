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

When Coq matches the current goal against the conclusion of H, it will try to find appropriate values for these variables.

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

### The injection and discriminate Tactics
~~~Coq
Inductive nat : Type :=
| O
| S (n : nat).
~~~

- The constructor S is injective (or one-to-one). That is, if S n = S m, it must also be that n = m.
- The constructors O and S are disjoint. That is, O is not equal to S n for any n.

~~~Coq
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2: n = pred (S n)). { reflexivity. }
  rewrite H2. rewrite H1. simpl. reflexivity.
Qed.
~~~

We are asking Coq to generate all equations that it can infer from H using the injectivity of constructors. Each such equation is added as a hypothesis into the context.

~~~Coq
Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H.
  (* WORKED IN CLASS *)
  injection H as H1 H2.
  rewrite H1. rewrite H2. reflexivity.
Qed.
~~~

The discriminate tactic embodies this principle: It is used on a hypothesis involving an equality between different constructors (e.g., false = true), and it solves the current goal immediately. 

~~~Coq
Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m contra. discriminate contra. Qed.
~~~

The principle of explosion, which asserts that a contradictory hypothesis entails anything (even manifestly false things!).

~~~Coq
Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A),
  x = y -> f x = f y.
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed.
~~~

Indeed, there is also a tactic named `f_equal` that can prove such theorems directly.

### Using Tactis on Hypotheses

The tactic "simpl in H" performs simplification on the hypothesis H in the context.
~~~Coq
Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b  ->
  (n =? m) = b.
Proof.
  intros n m b H. simpl in H. apply H.  Qed.
~~~

Similarly, apply L in H matches some conditional statement L (of the form X → Y, say) against a hypothesis H in the context. However, unlike ordinary apply (which rewrites a goal matching Y into a subgoal X), apply L in H matches H against X and, if successful, replaces it with Y.

~~~Coq
Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q EQ H.
  symmetry in H. apply EQ in H. symmetry in H.
  apply H.  Qed.
~~~

### Specializing Hypotheses
If H is a quantified hypothesis in the current context -- i.e., H : ∀ (x:T), P -- then specialize H with (x := e) will change H so that it looks like [x:=e]P, that is, P with x replaced by e.

~~~Coq
Example trans_eq_example''' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  specialize trans_eq with (m:=[c;d]) as H.
  apply H.
  apply eq1.
  apply eq2. Qed. 
~~~

### Varying the Induction Hypothesis
We may need to be careful about which of the assumptions we move (using intros) from the goal to the context before invoking the induction tactic.

~~~Coq
Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = O *) simpl. intros m eq. destruct m as [| m'] eqn:E.
    + (* m = O *) reflexivity.
    + (* m = S m' *) discriminate eq.

  - (* n = S n' *)
    intros m eq.
    destruct m as [| m'] eqn:E.
    + (* m = O *)
      discriminate eq.
    + (* m = S m' *)
      f_equal.
  apply IHn'. simpl in eq. injection eq as goal. apply goal. 
Qed.
~~~
The thing to take away from all this is that you need to be careful, when using induction, that you are not trying to prove something too specific.

What we can do instead is to first introduce all the quantified variables and then re-generalize one or more of them, selectively taking variables out of the context and putting them back at the beginning of the goal. The `generalize dependent` tactic does this.


### Unfolding Definitions

It sometimes happens that we need to manually unfold a name that has been introduced by a Definition so that we can manipulate the expression it stands for.


We already have observed that tactics like simpl, reflexivity, and apply will often unfold the definitions of functions automatically when this allows them to make progress.

But if the definition is quite complex(e.g. match included), `simpl` will not work. There are two ways to make progress: 

- destruct the variable to match 
- use unfold directly

### Using destruct on Compound Expressions

In general, the destruct tactic can be used to perform case analysis of the results of arbitrary computations.

If you will use the eqn expression shortly, you should write the eqn down, otherwise, Coq will erase all the occurence of eqn. 

- substitute away all existing occurrences of n =? 3, 
- add an equation to the context that records which case we are in. 
### Exs
- Exercise: 3 stars, standard, optional (trans_eq_exercise)
- Exercise: 3 stars, standard (injection_ex3)
- Exercise: 3 stars, standard, especially useful (plus_n_n_injective)
- Exercise: 3 stars, standard, especially useful (gen_dep_practice)