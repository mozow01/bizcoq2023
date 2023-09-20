````coq
Lemma drinker : forall (U : Type) (P : U -> Prop),
inhabited U -> ((forall x : U, P x) \/ (exists x : U, ~ P x))
-> exists (x : U), P x -> forall y : U, P y.
````

````coq
Lemma drinker_dual : forall (U : Type) (P : U -> Prop),
inhabited U -> ((exists x : U, P x) \/ (forall x : U, ~ P x))
-> exists (x : U), (exists y : U, P y )-> P x.
````

````coq
Lemma dec_1 : forall (U : Type) (P : U -> Prop),
inhabited U -> ((forall x : U, P x ) \/ (forall x : U, ~ P x))
-> (forall x : U, P x) \/ (exists x : U, ~ P x).
````

````coq
Lemma deM_4 : forall (U : Type) (P : U -> Prop), inhabited U -> ((exists x : U, P x) \/ ~ (exists x : U, P x)) -> ~ (forall x : U, ~ P x)-> (exists x : U, P x).
````

