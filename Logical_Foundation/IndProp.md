## INDUCTIVELY DEFINED PROPOSITIONS
### Inductively Defined Propositions

~~~Coq
Inductive Collatz_holds_for : nat -> Prop :=
  | Chf_done : Collatz_holds_for 1
  | Chf_more (n : nat) : Collatz_holds_for (f n) -> Collatz_holds_for n.
~~~

~~~Coq
Reserved Notation "n <= m" (at level 70).

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)   : n <= n
  | le_S (n m : nat) : n <= m -> n <= (S m)

  where "n <= m" := (le n m).
~~~
You can define the notation first with *Reserved Notation* and then use it in the *Inductive* and link it to the definition finally. 

Another classic example: Transitive Closure. 

In an Inductive definition, an argument to the type constructor on the left of the colon is called a "parameter", whereas an argument on the right is called an "index" or "annotation."


### Using Evidence in Proofs
Coq provides a handy tactic called inversion that factors out this common pattern, saving us the trouble of explicitly stating and proving an inversion lemma for every Inductive definition we make.

The inversion tactic can apply the principle of explosion to "obviously contradictory" hypotheses involving inductively defined properties, something that takes a bit more work using our inversion lemma.
~~~Coq
Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H. inversion H. Qed.
~~~

*Inversion* does the work of both discriminate and injection.

Here we are being a bit lazy by omitting the as clause from inversion.

For each of the constructors of P, inversion H generates a subgoal in which H has been replaced by the specific conditions under which this constructor could have been used to prove P.

