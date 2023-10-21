# Első házi példasor

Határidő: nov. 7

1. a) Elemezzük a következtő kódot, mit csinál a kövi program?

````coq
Fixpoint FuncBool (n : nat) :=
  match n with
  | 0 => bool
  | S m => bool -> FuncBool m
  end.

Fixpoint isAlwaysTrue (n : nat) : FuncBool n -> bool :=
  match n as m return (FuncBool m -> bool) with
    | 0 => (fun (x: (FuncBool 0)) => x)
    | S m => ( (fun (x: FuncBool (S m)) =>
       (andb ( (isAlwaysTrue m)( x true ) ) ( (isAlwaysTrue m)(x false) ))))
  end.
````

b) Folytassuk a helyességi bizonyítást n=2-re:

````coq
Lemma isAlwaysTrueIsCorrectFor2 : forall f, (forall b1 b2, f b1 b2 = true) -> isAlwaysTrue 2 f = true.
Proof.
intros.
simpl.
assert (H1 : f true true = true).
Abort.
````
c) Írjuk meg az "isNotAlwaysFalse (n)" függvényt és n=2-re igazoljuk a helyességét!

2. Bizonyítsd be Coq-ban és Lean3-ban (vagy Lean 4-ben)! Ha konstruktívan nem igaz, igazold klasszikus feltétellel!

a)
   ````coq
   forall A B : Prop,  (~ A \/ B) -> A -> B.
   ````

b)
   ````coq
   forall A B : Prop,  A -> B -> (~ A \/ B).
   ````

c)
   ````coq
   forall A B : Prop,  ((A -> B) -> A) -> A.
   ````
4. Bizonyítsd be!

a)
````coq
Lemma quant_1 : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ ~ (exists x : U, P x))
-> ~ (forall x : U, ~ P x) -> (exists x : U, P x).
````

b)
````coq
Lemma quant_2 : forall (U : Type) (P : U -> U -> Prop),
inhabited U -> (exists x, forall y, P x y) -> (forall y, exists x, P x y).
````

4. Olvassunk egy kicsit utána, mit csinál a típusosztályt (egyszerre több típust) definiáló Class parancs. @ a rejtett olsztályváltozót előhozó parancs, pl. ha T egy parciális rendezés, P a típus, amelynek az elemei rendezve vannak és R a rendezés, akkor @P T -vel hivatkozunk az rendezett elemek típusára, @R T -val a rendezésre. Olvassuk el, mit jelnet Binary Search Tree-nek lenni:

````coq
Require Import Relation_Definitions.

(*P egy "halmaz", R egy kétváltozós reláció, amely rendezés: R x y (R : P -> P -> Prop), ezek együtt egy
 rendezett struktúrát alkotnak, kiegészítve az axiómákkal. *)
Class PartialOrder := PO_mk { 
    P : Type;
    R : relation P;
    PO_Reflexive : @reflexive P R;
    PO_Transitive : @transitive P R;
    PO_Antisymmetric : @antisymmetric P R;
  }.

(*(@P T) a halmaz, aminek az elemei rendezve vannak a T rendezett struktúrában*)
Inductive tree (T : PartialOrder) :=
  | leaf : (@P T) -> tree T
  | node : (@P T) -> tree T -> tree T -> tree T.

(*Egy fa gyökerének értékei definíciója*)
Definition value (T : PartialOrder) (t : tree T) : @P T :=
match t with 
  | leaf _ a => a 
  | node _ a t1 t2 => a
end. 

(*Figyeljünk itt is arra, hogy a T rendezett struktúrában @R T hivatkozik a rendezésre.*)
Definition isBST (T : PartialOrder) (t : tree T) : Prop :=
match t with 
  | leaf _ _ => True
  | node _ a t1 t2 => (@R T (value T t1) a) /\ (@R T a (value T t2))
end.
````
Bizonyítsunk be egy korrektségi tételt, azaz hogy ha egy t fa egy BST, akkor tényleg rendelkezik a megfelelő tulajdonsággal! 

5.

a) Definiáljuk az előző bináris fa típusú fák tükörképét. Igazoljuk, hogy egy isBST fa tükörképe olyan, ahol a relációk iránya rendre megváltozik.

b) Definiáljuk nat értékű fákra is ezeket és igazoljuk a tételt ott is.

c) Ez utóbbit készítsük el TypeScript-ben is.
  
(*) Ha tudjuk, igazoljuk, hogy nat a kisebb egyenlő relációval PartialOrder.

6.

a) Defíniáljuk az n hosszúságú listák típusát (vektorok)! Igazoljuk, hogy egy n hosszúságú lista hossza n.

b) Definiáljuk egy n hosszúságú lista tüktözését és igazoljuk, hogy a definíció jó.
