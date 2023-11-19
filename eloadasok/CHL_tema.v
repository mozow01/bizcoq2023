Class Category := mk_cat {

  (*kategória szortok*)
  Obj : Set;
  uHom := Set : Type;
  Hom : Obj -> Obj -> uHom;
  
  (*kategória műveletek*)
  Id : forall x, Hom x x;
  Compose : forall {x y z}, (Hom y z)->(Hom x y)->(Hom x z);

  (*kategória egyenlőségek*)
  Dom {x y} (f: Hom x y) := x;
  CoDom {x y} (f: Hom x y) := y;
  assoc : forall x y z w (f : (Hom z w)) (g:(Hom y z)) (h:(Hom x y)),
        (Compose f (Compose g h) ) = (Compose (Compose f g) h);
  id_1 : forall x y (f : (Hom x y)), (Compose f (Id x)) = f ;
  id_2 : forall x y (f : (Hom x y)), (Compose (Id y) f) = f ;
}.

(*A morfizmus jele a LaTeX \to *)
Notation "x → y" := (Hom x y) (at level 90, right associativity) :
type_scope.

(*A kompozíció jele a LaTeX \circle *)
Notation "f ∘ g" := (Compose f g) (at level 40, left associativity) :
type_scope.

(*Kartéziusi kategória*)
Class Cartesian (C : Category) := mk_cc {

  (*műveletek*)
  Terminal_obj : Obj;
  Terminal_mor : forall {x}, x → Terminal_obj;

  Prod_obj : Obj -> Obj -> Obj;
  Prod_mor : forall {x y z} (f:x → y) (g:x → z), x → Prod_obj y z;
  Pr_1 {x y} : (Prod_obj x y) → x;
  Pr_2 {x y} : (Prod_obj x y) → y;

  (*egyenlőségek: terminális objektum*)
  unique_terminal : forall {x} (f : x → Terminal_obj), f = Terminal_mor;

  (*egyenlőségek: szorzat objektum*)
  prod_ax : forall {x y z} (f : x → y) (g : x → z), 
    (Pr_1 ∘ (Prod_mor f g) = f) /\ (Pr_2 ∘ (Prod_mor f g) = g);
  prod_eq : forall {x y z} (g : x → Prod_obj y z),
    Prod_mor (Pr_1 ∘ g) (Pr_2 ∘ g) = g;
}.

(*A konjunkció logikájának általános algebrai elmélete (GAT-ja)*)
Class Conj_logic := mk_conj_logic {

  (*szort*)
  Fm : Set;

  (*műveletek*)
  Top : Fm;
  Pf : Fm -> Set;
  Cnj : Fm -> Fm -> Fm;
  TopInt : Pf Top;
  CnjInt : forall A B : Fm, Pf A -> Pf B -> Pf (Cnj A B);
  CnjEli1 : forall A B : Fm, Pf (Cnj A B) -> Pf A; 
  CnjEli2 : forall A B : Fm, Pf (Cnj A B) -> Pf B; 
}.

(*Conj_logic-nak van kartéziusi kategorikus modellje*)
Theorem Cartesian_cat_is_a_Conj_logic (C : Category) (CC : Cartesian C) : Conj_logic.
Proof.
  apply mk_conj_logic with (Fm := Obj) (Top := Terminal_obj) (Pf := Hom Terminal_obj) (Cnj := Prod_obj).
  - exact (@Terminal_mor C CC Terminal_obj).
  - intros.
    exact (Prod_mor H H0).
  - intros.
    exact (Pr_1 ∘ H).
  - intros.
    exact (Pr_2 ∘ H).
Qed.

(*Az, hogy a Conj_logic egy kartéziánus macska, az egy másik felépítésben igazolandó, de simán megoldható.*)

(*És persze lehet logikázni bármennyit pl. Conj_logic-ban is.*)
Context (L : Conj_logic).

(*Az és jele a LaTeX \wedge *)
Infix "∧" := Cnj (at level 80, right associativity). 

(*Az és kommutatív, persze*)
Theorem and_comm : forall (A B : Fm), Pf (A ∧ B) ->  Pf (B ∧ A).
Proof.
  intros.
  apply CnjInt.
  apply CnjEli2 in H.
  - auto.
  - apply CnjEli1 in H.
    auto.
Qed.