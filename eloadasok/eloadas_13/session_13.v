(*SOGAT*)

Class Conj_logic := mk_conj_logic {

  (*szort*)
  Fm : Set;

  (*műveletek*)
  Top : Fm;
  Pf : Fm -> Set;
  Cnj : Fm -> Fm -> Fm;
  TopInt : Pf Top;
  CnjInt : forall A B : Fm, Pf A -> Pf B -> Pf (Cnj A B);
  CnjEli : forall A B C : Fm, Pf (Cnj A B) -> (Pf A -> Pf B -> Pf C) ->
  Pf C;

  Imp : Fm -> Fm -> Fm;
  ImpInt : forall A B : Fm, (Pf A -> Pf B) -> Pf (Imp A B);
  ImpEli : forall A B : Fm, Pf (Imp A B) -> Pf A -> Pf B;
  
  Dis : Fm -> Fm -> Fm;
  DisInt1 : forall A B : Fm,  Pf A -> Pf (Dis A B);
  DisInt2 : forall A B : Fm,  Pf B -> Pf (Dis A B);
  DisEli : forall A B C : Fm, Pf (Dis A B) -> (Pf A -> Pf C) -> (Pf B -> Pf C) -> Pf C;
}.

Infix "∧" := Cnj (at level 100, right associativity). 
Infix "→" := Imp (at level 90, right associativity). 
Infix "∨" := Dis (at level 80, right associativity). 

Context (CL : Conj_logic).



Lemma Currying : forall A B C : Fm,  
          Pf (A → B → C) -> Pf ((A ∧ B) → C).
Proof.
intros.
apply ImpInt.
intro.
apply CnjEli with (A := A) (B := B) (C := C).
auto.
intros. 
assert (K : Pf (B → C)).
apply ImpEli with (A:=A) (B:=(B → C)).
auto. auto. 
apply ImpEli with (A:=B) (B:=C).
auto. auto. 
Qed.

Lemma unCurrying : forall A B C : Fm,  
          Pf ((A ∧ B) → C) -> Pf (A → B → C).




