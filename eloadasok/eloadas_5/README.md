# Fák 2

## Fák, mint nyelv szintaxisa

````coq
Inductive Exp : Set :=
  | AT : nat -> Exp  
  | NOT : Exp -> Exp
  | AND : Exp -> Exp -> Exp 
  | OR : Exp -> Exp -> Exp.

Inductive UnOp : Set :=
  | NOT_c : UnOp.

Inductive BinOp : Set :=
  | AND_c : BinOp
  | OR_c : BinOp.

Inductive AST : Set :=
  | leaf : nat -> AST
  | node1 : UnOp -> AST -> AST
  | node2 : BinOp -> AST -> AST -> AST.

Fixpoint ExpDenote (e : Exp) (v : nat -> bool ) {struct e} :=
match e with 
  | AT n => v n 
  | NOT e1 => negb (ExpDenote e1 v)
  | AND e1 e2 => andb (ExpDenote e1 v) (ExpDenote e2 v)
  | OR e1 e2 => orb (ExpDenote e1 v) (ExpDenote e2 v)
end.

Fixpoint ASTDenote (t: AST) (v : nat -> bool ) {struct t} :=
match t with
  | leaf n => v n
  | node1 _ t1 => negb (ASTDenote t1 v)
  | node2 x t1 t2 => match x with
           | AND_c => andb (ASTDenote t1 v) (ASTDenote t2 v)
           | OR_c => orb (ASTDenote t1 v) (ASTDenote t2 v)
                     end
end.

Fixpoint Translater1 (e : Exp) :=
match e with
  | AT n => leaf n 
  | NOT e1 => node1 NOT_c (Translater1 e1)
  | AND e1 e2 => node2 AND_c (Translater1 e1) (Translater1 e2)
  | OR e1 e2 => node2 OR_c (Translater1 e1) (Translater1 e2)
end.

Fixpoint Translater2 (t : AST) :=
match t with
  | leaf n => AT n
  | node1 _ t1 => NOT (Translater2 t1)
  | node2 AND_c t1 t2 => AND (Translater2 t1) (Translater2 t2)
  | node2 OR_c t1 t2 => OR (Translater2 t1) (Translater2 t2) 
end.

Theorem Soundness1 : forall t v, ASTDenote t v = ExpDenote (Translater2 t) v.
Proof.
intros.
induction t.
compute.
auto.
simpl.
rewrite IHt.
auto.
induction b.
all: simpl; rewrite IHt1; rewrite IHt2; auto.
Qed.
````
## n magasságú fák és magasságuk

````coq
Inductive hbTree : nat -> Set :=
  | hleaf : bool -> hbTree 0
  | hnode : forall n:nat, (bool->bool->bool) -> hbTree n -> hbTree n -> hbTree (S n).

(* pl.: *)

Check hleaf true.
Check hnode 0 andb (hleaf true) (hleaf true).

Fixpoint height (n : nat) (t : hbTree n) : nat :=
  match t with
    | hleaf b => 0
    | hnode m bf t1 t2 => (max (height m t1) (height m t1)) + 1
  end.

Require Import Lia.

Lemma height_lemma : forall (n : nat) (t : hbTree n), height n t = n.
Proof.
intros.
induction t.
compute. auto.
simpl.
rewrite IHt1.
lia.
Qed.
````

# Üres és egyelemű típus

````coq
Inductive False : Prop :=  .

False_ind =
fun (P : Prop) (f : False) =>
match f return P with
end
     : forall P : Prop, False -> P

Inductive True : Prop :=  I : True.

False_ind =
fun (P : Prop) (f : False) =>
match f return P with
end
     : forall P : Prop, False -> P
````

# Listák

````coq
Require Import List.
Import ListNotations.

Fixpoint reverse {A : Type} (lst : list A) : list A :=
  match lst with
  | [] => []
  | h :: t => (reverse t) ++ [h]
  end.


(* Lemma 1: Reversing an empty list yields an empty list *)
Lemma reverse_nil : forall (A : Type),
  reverse (@nil A) = (@nil A).
Proof.
  intros A. simpl. reflexivity.
Qed.

(* Lemma 2: Reversing a list and appending an element is the same as appending the element and reversing *)
Lemma reverse_app : forall (A : Type) (x : A) (lst : list A),
  reverse (lst ++ [x]) = x :: reverse lst.
Proof.
  intros A x lst. induction lst as [| h t IHt].
  - simpl. reflexivity.
  - simpl. rewrite IHt. reflexivity.
Qed.

(* The main theorem: The reverse function is correct *)
Theorem reverse_correct : forall (A : Type) (lst : list A),
  reverse (reverse lst) = lst.
Proof.
  intros A lst. induction lst as [| h t IHt].
  - simpl. apply reverse_nil.
  - simpl. rewrite reverse_app. rewrite IHt. reflexivity.
Qed.
````

