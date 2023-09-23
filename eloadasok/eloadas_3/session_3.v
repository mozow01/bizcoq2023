Lemma deM_1 : forall A B, ~ A \/ ~ B -> ~ (A /\ B).
Proof.
intros.
unfold not.
intros.
destruct H as [K|L].
destruct H0.
unfold not in K.
apply K.
exact H.
destruct H0.
contradiction.
Qed.

(* Currying: A -> B -> C -| (A /\ B) -> C; 
un Currying:  A -> B -> C |- (A /\ B) -> C *)

Lemma deM_2 : forall A B, (A \/ ~ A) -> ~ (A /\ B) -> ~ A \/ ~ B .
Proof.
intros.
elim H.
all: intro.
unfold not in H0.
right.
unfold not.
intro.
auto.
left.
auto.
Qed.

Lemma drinker : forall (U : Type) (P : U -> Prop), inhabited U -> ((forall x : U, P x) \/ (exists x : U, ~ P x)) -> exists (x : U), P x -> forall y : U, P y.
Proof.
intros.
elim H.
intro.
destruct H0 as [K|L].
exists X.
intro.
auto.
elim L.
intros.
exists x.
intro.
intro.
contradiction.
Qed.
