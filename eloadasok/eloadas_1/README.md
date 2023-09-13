# My Type: Boole

## Coq

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
## Lean3 kód 

Itt vannak kommentek is, mert jobban különbözik a Coq-tól, mint a Lean 4, így magyarázatra szorul

````lean
-- "Boole" mert itt is van beépített "bool" típus

#print bool

inductive Boole : Type
| igaz : Boole 
| hamis : Boole 

-- Az új Boole konstruktoraira nem "igaz"-ként, hanem "Boole.igaz"-ként kell(ene) hivatkozni, azaz a "Boole" egy mezőt vagy "namespace"-t hoz létre: 

#print Boole

-- tehát nem ismert, "#check igaz" hibát ad vissza. Persze ez leküzdhető, ha megnyitjuk a Boole namespace-t:

open Boole

#print igaz

-- a lean a natív Coq -> függvénytípus helyett a LaTeX kódot használja, "\to", ami után a space-t megnyomva azonnal generálódik a → . 

def es : Boole →  Boole → Boole
| igaz igaz := igaz
| hamis _ := hamis
| _ hamis := hamis

-- az online verzió nem bír el a kiértékeléssel, a második Boole konstruktort adja vissza a "hamis"-ra, aminek jele: #1 (az elsőt a #0-t az "igaz"-ra)

#eval es hamis hamis

#eval es igaz igaz

def vagy : Boole →  Boole → Boole
| igaz _ := igaz
| _ igaz := igaz
| hamis hamis := hamis

theorem dist_1 (a b c : Boole) : es a (vagy b c) = vagy (es a b) (es a c) :=
begin
  induction a; induction b; induction c; 
  all_goals { exact rfl }
end

-- Lean3 begin-kel kezdi a proofmode-ot
-- Lean3 deklarálta és definiálta is a prooftermet:

#check dist_1
#print dist_1
````

## Lean4 kód

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
