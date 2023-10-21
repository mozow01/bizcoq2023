# Első házi példasor

Határidő: nov. 7

1. Elemezzük a következtő kódot, mit csinál a kövi program?

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

Folytassuk a helyességi bizonyítást n=2-re:

````coq
Lemma isAlwaysTrueIsCorrectFor2 : forall f, (forall b1 b2, f b1 b2 = true) -> isAlwaysTrue 2 f = true.
Proof.
intros.
simpl.
assert (H1 : f true true = true).
Abort.
````
Írjuk meg az "isNotAlwaysFalse (n)" függvényt és n=2-re igazoljuk a helyességét!

2. 


