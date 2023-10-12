````coq
(*Listák, spéci jelölés nélkül*)
Require Import List. 

(*Listák spéci beépített függvényekkel:*)
Import ListNotations.

(*Polimorf típus, akármik listája, de csak A-k listája*)
Print list.
(*Inductive list (A : Type) : Type :=
    nil : list A
  | cons : A -> list A -> list A.
*)

(*Vegyes lista csak úgy nem mükszik: 
Definition m_l := true :: 3 :: nil *)

(*Vegyes listához összegtípus kell:*)
Inductive A_nat_bool : Set :=
 | cons_nat : nat -> A_nat_bool 
 | cons_bool : bool -> A_nat_bool.

Definition m_l := cons_bool true :: cons_nat 3 :: nil.

Check m_l.
(*m_l
     : list A_nat_bool*)

(*Jel definíciójának lekérdezése (köszi Mátyás!)*)
Locate "++".
(*Notation "x ++ y" := (app x y) : list_scope
  (default interpretation)*)

Print app.
(*app =
fun A : Type =>
fix app (l m : list A) {struct l} :
    list A :=
  match l with
  | [] => m
  | a :: l1 => a :: app l1 m
  end
     : forall A : Type,
       list A -> list A -> list A*)

(*Felvételi feladat Ericssonnál: írjunk egy  programot, ami tükröz egy listát!*)
Fixpoint reverse {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | h :: t => (reverse t) ++ [h]
  end.

Locate "[ ]".
(*Notation "[ ]" := nil : list_scope)*)

Locate "[ _ ]".
(*Notation "[ x ]" := (cons x nil)
  : list_scope (default interpretation)*)

(*Ugorj a következőre, ez csak egy lemma, ami kell a helyességhez, de kell, ezért majd ugorj vissza*)
Lemma reverseApp : forall (A : Type) (x : A) (l : list A),
  reverse (l ++ [x]) = x :: reverse l.
Proof.
  intros. 
  induction l.
  - compute. reflexivity.
  - simpl. rewrite IHl. reflexivity.
Defined.

(*Lista tükrözés helyes, ha *)
Theorem reverseCorrect : forall (A : Type) (l : list A),
  reverse (reverse l) = l.
Proof.
  intros. 
  induction l.
  - simpl. auto.
  - simpl. rewrite reverseApp. rewrite IHl. reflexivity.
Defined.

(*n magasságú fa, ami ugyanolyan magas ágakból áll*)
Inductive hbTree : nat -> Set :=
  | hleaf : bool -> hbTree 0
  | hnode : forall n:nat, (bool->bool->bool) -> hbTree n -> hbTree n -> hbTree (S n).

(*n magasságú fa, ami különböző magasságú ágakból áll*)
Inductive HbTree : nat -> Set :=
  | Hleaf : bool -> HbTree 0
  | Hnode : forall n m:nat, (bool->bool->bool) -> HbTree n -> HbTree m -> HbTree (S (max n m)).

(* pl.: *)
Check hleaf true.
(*hleaf true
     : hbTree 0 *)

Check hnode 0 andb (hleaf true) (hleaf true).
(*hnode 0 andb (hleaf true) (hleaf true)
     : hbTree 1 *)

Check Hnode 0 1 andb (Hleaf true) (Hnode 0 0 andb (Hleaf true) (Hleaf true)).
(*Hnode 0 1 andb (Hleaf true)
  (Hnode 0 0 andb (Hleaf true) (Hleaf true))
     : HbTree (S (Nat.max 0 1))*)

(*mivel természetes számok vannak benne, jó ha betöltjük a liát*)
Require Import Lia.

(*... mert ez kiszámolja*)
Eval compute in (HbTree (S (Nat.max 0 1))).

Fixpoint height (n : nat) (t : hbTree n) : nat :=
  match t with
    | hleaf b => 0
    | hnode n bf t1 t2 => (max (height n t1) (height n t2)) + 1
  end.

Lemma height_lemma : forall (n : nat) (t : hbTree n), height n t = n.
Proof.
intros.
induction t.
- compute; auto.
- simpl.
  rewrite IHt1.
  lia.
Defined.

Fixpoint Height (n : nat) (t : HbTree n) : nat :=
  match t with
    | Hleaf b => 0
    | Hnode n m bf t1 t2 => (max (Height n t1) (Height m t2)) + 1
  end.

Lemma Height_lemma : forall (n : nat) (t : HbTree n), Height n t = n.
Proof.
intros.
induction t.
- compute; auto.
- simpl.
  rewrite IHt1.
  rewrite IHt2.
  lia.
Defined.
````
