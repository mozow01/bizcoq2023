# Prop típus

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

Lean beviteli segítség VS Code-ban vagy online: ha beírjuk a latex parancsot, az első space lenyomásával átalakítja html-lé, pl.: \to , \and , \or , \forall , \pi ... Próbáljuk ki!

````lean
theorem DM_2 (A B : Prop ) : (¬ A ∨ ¬ B) → ¬(A ∧ B) :=
begin
  intros H,
  intros K,
  cases H with H1 H2,
   begin  
    -- apply H1 alkalmazza H1-et a goal-ra. H1 típusa most ¬A, ez a Lean-ben is A → False -t jelent, csak itt nem kell unfold... 
    apply H1,
    exact K.left,
   end,
   begin 
    apply H2,
    exact K.right,
   end
end

#print DM_2

````
# HF: Igazoljuk a következő állításokat!

Azt hogy érvényesek vagy sem, nem dönti el a firstorder taktika, de segít, mert ha nem fut le, akkor gyanakodhatunk, hogy nem érvényesek az intuicionista logikában. 

Segítség: ha klasszikussá akarjuk tenni, próbálkozzunk az "````(~ A \/ A) -> ...````" plusz feltétellel az állítás előtt!

A CoqIDE is tud latex betűket csinálni, pl: \Xi és utána egy shift+space egy nagy Xi-t csinál.

````
1. forall A B C : Prop, A \/ (B /\ C) -> (A \/ B) /\ (A \/ C)
2. forall A B C : Prop, ~ A \/ ~ B -> ~ (A /\ B)
3. forall A B C : Prop, ~ (A /\ B) -> ~ A \/ ~ B
4. forall A B C : Prop, ~ (A \/ B) -> ~ A /\ ~ B
````
Lean-ben is megpróbálhatjuk, erre van példa.
