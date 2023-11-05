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
