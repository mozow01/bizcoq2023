Nyers kód:

Coq:

````coq
Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.

Definition és (b1 b2 : Boole) := 
    match b1 with 
      | igaz => match b2 with 
                  | igaz => igaz
                  | hamis => hamis
                end
      | hamis => hamis
    end.

Definition vagy b1 b2 :=
    match b1 with 
      | igaz => igaz
      | hamis => match b2 with 
                  | igaz => igaz
                  | hamis => hamis
                 end
    end.

Theorem dist_1 : forall b1 b2 b3 : Boole, és b1 (vagy b2 b3) = vagy (és b1 b2) (és b1 b3).
Proof.
induction b1, b2, b3.
all: compute; reflexivity.
Qed.
````
Lean4 kód:

````lean
inductive Boole : Type
  | igaz : Boole
  | hamis : Boole

open Boole

def es (b1 : Boole ) (b2 : Boole) : Boole := match b1 with  
  | igaz  => match b2 with
                | igaz => igaz 
                | hamis => hamis
  | hamis => hamis

def vagy b1 b2 := match b1 with 
  | igaz => igaz
  | hamis => match b2 with 
                | igaz => igaz
                | hamis => hamis
   
theorem dist_Boole_1 : forall b1 b2 b3 : Boole,
  es b1 (vagy b2 b3) = vagy (es b1 b2) (es b1 b3) := by {
intros b1 b2 b3 
induction b1
induction b2
induction b3
all_goals trivial
}
````
