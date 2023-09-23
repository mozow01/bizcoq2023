## Megoldott feladat:

````coq
Lemma drinker : forall (U : Type) (P : U -> Prop),
inhabited U -> ((forall x : U, P x) \/ (exists x : U, ~ P x))
-> exists (x : U), P x -> forall y : U, P y.
````
## Házi feladatok

1.

````coq
Lemma drinker_dual : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ (forall x : U, ~ P x))
-> exists (x : U), (exists y : U, P y )-> P x.
````

2.

````coq
Lemma dec_1 : forall (U : Type) (P : U -> Prop),
inhabited U -> ((forall x : U, P x ) \/ (forall x : U, ~ P x))
-> (forall x : U, P x) \/ (exists x : U, ~ P x).
````

3.

````coq
Lemma ex_dist_1 : forall (U : Type) (A B : U -> Prop),
(exists x, A x \/ B x) -> (exists x, A x) \/ (exists x, B x).
````

4.

````coq
Lemma deM_quant_4 : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ ~ (exists x : U, P x))
-> ~ (forall x : U, ~ P x)-> (exists x : U, P x).
````

