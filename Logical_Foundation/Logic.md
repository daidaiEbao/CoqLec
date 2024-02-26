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
The *apply* tactic can also be used with *< - >*. We can use apply on an *< - >* in either direction, without explicitly thinking about the fact that it is really an *and* underneath.

~~~Coq
Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
  intros P Q R Hiff H HP. apply H.  apply Hiff. apply HP.
Qed.

Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
  intros P Q R Hiff H HQ. apply H.  apply Hiff. apply HQ.
Qed.
~~~

**Hiff** was used in two different directions, but we didn't point it out explicitly. 

#### Setoids and Logical Equivalence
Similarly, the logical equivalence relation *< - >* is reflexive, symmetric, and transitive, so we can use it to replace one part of a proposition with another: if P *< - >* Q, then we can use *rewrite* to replace P with Q, or vice-versa.

#### Existential Quantification
To prove a statement of the form ∃ x, P, we must show that P holds for some specific choice for x, known as the witness of the existential. This is done in two steps: First, we explicitly tell Coq which witness t we have in mind by invoking the tactic ∃ t. Then we prove that P holds after all occurrences of x are replaced by t.


~~~ Coq
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note the implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

~~~

Conversely, if we have an existential hypothesis ∃ x, P in the context, we can destruct it to obtain a witness x and a hypothesis stating that P holds of x.

### Programming with Propositions
To illustrate, let's look at how to express the claim that an element x occurs in a list l. Notice that this property has a simple recursive structure:
- If l is the empty list, then x cannot occur in it, so the property "x appears in l" is simply false.
- Otherwise, l has the form x' :: l'. In this case, x occurs in l if it is equal to x' or if it occurs in l'.
~~~Coq
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
~~~

### Applying Theorems to Arguments
One feature that distinguishes Coq from some other popular proof assistants (e.g., ACL2 and Isabelle) is that it treats proofs as first-class objects.

We have seen that we can use Check to ask Coq to print the type of an expression. We can also use it to ask what theorem a particular identifier refers to.

The type of this object is the proposition that it is a proof of.

A more elegant alternative is to apply add_comm directly to the arguments we want to instantiate it with, in much the same way as we apply a polymorphic function to a type argument.

~~~Coq
Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  rewrite (add_comm y z).
  reflexivity.
Qed.
~~~

### Exs
- Exercise: 2 stars, standard (and_exercise)
- Exercise: 2 stars, standard, optional (not_implies_our_not)
- Exercise: 2 stars, standard (de_morgan_not_or)
- Exercise: 1 star, standard, especially useful (dist_not_exists)
- Exercise: 3 stars, standard, optional (leb_plus_exists)