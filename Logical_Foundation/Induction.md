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
