# Nyers kódok

## Coq

````coq
(*

A           B
-------------
    A/\B




    A/\B
------------
     A

   A/\B
------------
     B



     A
--------------
    A\/B




       A   B
       

A\/B   C   C 
------------
      C

A -> B   A
-----------------
B





A

.
.
.

B
------
A -> B





*)

Theorem dist_2 : forall A B C : Prop, A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
intros.
destruct H as [K1 K2].
destruct K2 as [H1|H2].
(*
left.
split.
exact K1.
exact H1.
*)
all: intuition.
Qed.

Theorem dist_3 : forall A B C : Prop, A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
intros.
destruct H as [K1 K2].
elim K2.
all: intro.
Focus 2.
Abort.

Theorem DM_1 : forall A B C : Prop, ~ A /\ ~ B -> ~ (A \/ B).
Proof.
intros.
unfold not.
unfold not in H.
intro.
elim H0.
all: intuition.
Qed.
````

## Lean 3

````lean

````
