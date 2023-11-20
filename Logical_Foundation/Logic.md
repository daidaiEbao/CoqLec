## LOGIC IN COQ
Any statement we might try to prove in Coq has a type, namely Prop, the type of propositions.

we can give a name to a proposition using a Definition:  
~~~Coq
Definition plus_claim : Prop := 2 + 2 = 4.
~~~

parameterized propositions 
~~~Coq
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.
~~~

In Coq, functions that return propositions are said to define properties of their arguments.
- explicit
- polymorphic
### Logical Connectives
#### Conjunction
To prove a conjunction, use the *split* tactic.  

We can *apply conj* to achieve the same effect as split.

~~~Coq
Check @conj : ∀ A B : Prop, A → B → A ∧ B.
~~~


When the current proof context contains **a hypothesis H of the form A ∧ B**, writing destruct H as [HA HB] will remove H from the context and replace it with two new hypotheses: HA, stating that A is true, and HB, stating that B is true.

If HA or HB is unneeded, use an underscore pattern _ to indicate that the unneeded conjunct should just be thrown away.

How to rearrage the order of conjunctions? 
- commutativity
- associativity

~~~Coq
(*conjunction is the syntactic sugar for *and* *)
Check and : Prop → Prop → Prop.
~~~

#### Disjunction
To use a disjunctive hypothesis in a proof, we proceed by case analysis. 

destruct H as [HA | HB]

Conversely, to show that a disjunction holds, it suffices to show that one of its sides holds. This can be done via the tactics *left* and *right*.

#### Falsehood and Negation
If we assume a contradiction, then any other proposition can be derived.

If we can get False into the context, we can use destruct on it to complete any goal:
~~~Coq
Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.
~~~
Inequality is a very common form of negated statement, so there is a special notation for it:

Notation "x <> y" := (~(x = y)).

If you are trying to prove a goal that is nonsensical (e.g., the goal state is false = true), apply ex_falso_quodlibet to change the goal to False.

Since reasoning with ex_falso_quodlibet is quite common, Coq provides a built-in tactic, *exfalso*, for applying it.

#### Truth
To prove it, we use the constant I : True, which is also defined in the standard library:

~~~Coq
Lemma True_is_true : True.
Proof. apply I. Qed.

Definition disc_fn (n: nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.

Theorem disc_example : forall n, ~ (O = S n).
Proof.
  intros n H1.
  assert (H2 : disc_fn O). { simpl. apply I. }
  rewrite H1 in H2. simpl in H2. apply H2.
Qed.
~~~

The built-in *discriminate* tactic takes care of all this for us!

#### Logical Equivalence


### Exs
- Exercise: 2 stars, standard (and_exercise)
- Exercise: 2 stars, standard, optional (not_implies_our_not)
- Exercise: 2 stars, standard (de_morgan_not_or)