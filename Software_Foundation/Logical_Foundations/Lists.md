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
#### useful functions
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
(* why default? *)

Definition tl (l : natlist) : natlist :=
  match l with
  | nil ⇒ nil
  | h :: t ⇒ t
  end.
(* return everything but the first element *)
```

#### bags via lists

bags means multiset

``` Coq
Definition sum : bag -> bag -> bag
  (*(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.*)
:= 
(*alternate*) app
.
```



### Reasoning About Lists
#### Induction on Lists
- First, show that P is true of l when l is nil.
- Then show that P is true of l when l is cons n l' for some number n and some smaller list l', assuming that P is true for l'.
~~~Coq
Theorem app_assoc : ∀ l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3. induction l1 as [| n l1' IHl1'].
  - (* l1 = nil *)
    reflexivity.
  - (* l1 = cons n l1' *)
    simpl. rewrite → IHl1'. reflexivity. Qed.
~~~
#### Search
``` Coq
Search (rev).
Search (_+_) inside Induction.
Search (?x+?y = ?y+?x).
```

Using keyword *search* to find the theorem which has been proofed quickly. 


#### More in Lists
The keyword *destruct* can works on arbitrary expressions as well. 
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

### Exs
- Exercise: 3 stars, advanced (alternate)
- Exercise: 3 stars, standard, especially useful (bag_functions)
> Personal Note: 
How to understand the first question in bag_functions?
- Exercise: 2 stars, standard, especially useful (add_inc_count)
- Exercise: 3 stars, standard (list_exercises)
- Exercise: 3 stars, advanced (remove_does_not_increase_count)
- Exercise: 3 stars, standard, optional (bag_count_sum)