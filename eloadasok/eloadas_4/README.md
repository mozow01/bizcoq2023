# Fák
## Függvények fákon

````coq
Lemma drinker_dual : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ (forall x : U, ~ P x))
-> exists (x : U), (exists y : U, P y )-> P x.
Proof.
intros.
elim H.
intros.
destruct H0 as [H1|H2].
- inversion H1.
  exists x.
  intros.
  exact H0.
- exists X.
  intros.
  elim H0.
  intros.
  enough (K : ~ P x).
  contradiction.
  { (* exact (H2 X). *) specialize (H2 x). auto. } 
  (* assert (K : ~ P x). 
  { (* exact (H2 X). *) specialize (H2 x). auto. }
  contradiction.*)
Qed.

Inductive binTree : Set :=
  | leaf : binTree
  | node : binTree -> binTree -> binTree.

Fixpoint leafLength (t : binTree) {struct t} : nat :=
  match t with 
    | leaf => 1
    | node t1 t2 => (leafLength t1) + (leafLength t2)
  end.

Lemma leafLengthSound_1 : leafLength leaf = 1.
Proof.
simpl. auto.
Qed.

Lemma leafLengthSound_2 : forall t1 t2, leafLength (node t1 t2) = leafLength t1 + leafLength t2.
Proof.
induction t1, t2.
all: simpl; auto.
Qed.

Fixpoint revertBinTree (t : binTree) : binTree :=
  match t with
  | leaf => leaf
  | node t1 t2 => node (revertBinTree t2) (revertBinTree t1)
  end.

Theorem revertBinTreeSound : forall t, revertBinTree (revertBinTree t) = t.
Proof.
induction t.
- simpl. auto.
- simpl. rewrite IHt2. rewrite IHt1. auto. 
Qed.

Fixpoint mostRightAppend (t s : binTree) {struct t} : binTree :=
  match t with 
   | leaf => s
   | node t1 t2 => node t1 (mostRightAppend t2 s)
  end.

Definition mostRightAppend_correct (t s result : binTree) : Prop :=
  forall t1 t2, t = node t1 t2 ->
  result = node t1 (mostRightAppend t2 s).

Lemma mostRightAppend_correct_proof :
  forall t s, mostRightAppend_correct t s (mostRightAppend t s).
Proof.
  intros t s.
  induction t.
  - (* leaf *)
    unfold mostRightAppend_correct.
    intros t1 t2 H.
    discriminate H. (* discriminate does it too *)
  - (* node *)
    unfold mostRightAppend_correct.
    intros t1' t2' H.
    (* inversion! subst! *)
    inversion H. 
    rewrite <- H.
    rewrite <- H1.
    rewrite <- H2.
    (* subst. *)
    simpl.
    reflexivity.
Qed.

Require Import Lia.

Lemma Right_leafLength : forall t s, leafLength (mostRightAppend t s) + 1 = leafLength t + leafLength s.
Proof.
  intros t s.
  induction t.
  - (*  leaf *)
    simpl. lia.
  - (* node *)
    simpl mostRightAppend.
    simpl leafLength.
    Search ( (_ + _) + _ = _ + (_ + _)).
    rewrite Arith_prebase.plus_assoc_reverse_stt.
    rewrite Arith_prebase.plus_assoc_reverse_stt.
    rewrite IHt2.
    auto.
    (* Search ( (_ + _) + _ = _ + (_ + _)) . *)
Qed.
````

