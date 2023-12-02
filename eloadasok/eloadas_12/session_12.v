Require Import List.
Import ListNotations.


(*Listákat fogunk definiálni cimkékkel. Ezek lesznek a címkék:*)
Inductive Key : Set :=
  | Anna : Key
  | Béla : Key
  | Cili : Key
  | Dani : Key.

(*Véges típus egyenlősége eldönthető. Fontos a Defined.*)
Theorem Key_eq_dec : forall k1 k2 : Key, {k1 = k2} + {k1<>k2}.
Proof.
induction k1,k2.
all: tryif left; reflexivity then auto else right; discriminate.
Defined.

Print option.

Print list.

(*Megkeressük a címkéhez tartozó számot.*)
Fixpoint find_key_return_value (key : Key) (data : list (nat*Key)) : option nat :=
  match data with 
    | [] => None
    | dh :: dt => match (Key_eq_dec (let (_,k) := dh in k) key) with 
                    | left _ => Some (let (n,_) := dh in n)
                    | right _ => find_key_return_value key dt
                  end
  end.

Fixpoint find_key_return_list (key : Key) (data : list (nat*Key)) (stack : list nat) {struct data} : list nat :=
  match data with 
    | [] => stack
    | dh :: dt => match (Key_eq_dec (let (n,k) := dh in k) key) with 
                    | left _ => find_key_return_list key dt ((let (n,k) := dh in n) :: stack)
                    | right _ => find_key_return_list key dt stack
                  end
  end. 


(*Példák*)
Definition data1 := [ (23, Anna) ; (32, Béla) ].

Definition data2 := [ (27, Anna) ; (32, Béla) ;  (28, Anna) ; (18, Béla) ].

Definition data3 := [ (52, Cili) ; (32, Béla) ].

Compute (find_key_return_value Anna data2).

Compute (find_key_return_list Anna data2 []).

Definition find_key_return_list' (key : Key) (data : list (nat*Key)) (stack : list nat) := find_key_return_list key data [].

(*Tehát az option egy jó dolog a kivételek kezelésére. De ez egy általános CS dolog, az úgy nevezett Kleisli-monád.

Egy M Kleisli-monád egy Type -> Type típusú dolog, azaz típust eszik és típust ad vissza, vagyis egy polimorf típuskonstruktor, pl. 

  -- option, 
  -- list.

tartozik hozzá két érdekes operáció: 

  -- unit : A -> M A, az egységleképezés
  -- bind, ami egy kötő leképezés

                 unit
              A ----> M A  bind ma unit = ma
                \      |
                 \     |
                  \ f  |   bind (unit a) f = f a
                   \   |
                unit\  |  
              B ----> M B
                \      |
                 \     |
                  \ g  |   bind (bind ma f) g = bind ma (fun x => bind (f x) g)
                   \   |
                    \  |  
              C       M C
*)

(*Kleisli-monád, polimorf típuskonstruktor, map : (A -> B) -> M A -> M B *)
Class Monad : Type := mk_monad
{
  (*szort*)
  M : Type -> Type;
  
  (*operátorok*)
  bind : forall {A B : Type}, M A -> (A -> M B) -> M B;
  unit : forall {A : Type}, A -> M A;

  (*egyenlőségek*)  
  left_id_law : forall (A B : Type) (a : A) (f : A -> M B), 
                    bind (unit a) f = f a; 

  right_id_law : forall (A : Type) (ma : M A),
                    bind ma (unit) = ma; 

  assoc_law : forall (A B C : Type) (ma : M A) (f : A -> M B) (g : B -> M C),
                    bind (bind ma f) g = bind ma (fun x => bind (f x) g)
}.

Definition unit_opt (A : Type) := fun (a : A) => Some a.

Definition bind_opt (A B: Type) := fun (ma : option A) (f : A -> option B) =>
                     match ma with
                       | Some a => f a
                       | None => None
                     end.


Theorem Option_is_a_Monad : Monad.
Proof.
apply mk_monad with (M := option) (bind := bind_opt) (unit := unit_opt).
  - intros; simpl; auto.
  - intros; induction ma; compute; auto.
  - intros; induction ma; compute; auto.
Qed.

Require Import Arith.

Locate "<?".

Definition safe_minus (a b : nat) : option nat :=
  if a <? b then None else Some (a - b).

Definition safe_minus_bind (a b : nat) : option nat :=
  bind_opt nat nat (safe_minus a b) (unit_opt nat).

Definition return_opt := unit_opt.

Definition safe_minus_bind' (a b : nat) : option nat :=
  bind_opt nat nat (safe_minus a b) (return_opt nat).

Definition option_subtract_chain (a b c : nat) : option nat :=
  bind_opt nat nat (safe_minus a b) (fun output1 =>
    bind_opt nat nat (safe_minus output1 c) (return_opt nat)
  ).

Compute (option_subtract_chain 1 2 3).