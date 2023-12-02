Structure Group : Type := mk_Group
{
A :> Set;

op : A -> A -> A ;
inv : A -> A ;
z : A ;

op_assoc : forall a b c, op a (op b c) = op (op a b) c;
op_z : forall a, op a z = a /\ op z a = a ;
op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z
}.

Inductive Z_3 : Set :=
  | n : Z_3 
  | a : Z_3
  | b : Z_3.

Check a.

Require Import Coq.Arith.PeanoNat.

Definition op_Z_3 x y :=
  match x , y with
  | n , y => y
  | x , n => x
  | a , b => n
  | b , a => n 
  | a , a => b
  | b , b => a
  end.

Definition inv_Z_3 x :=
  match x with
  | n => n
  | a => b
  | b => a
  end.

Definition z_Z_3 :=n.

Theorem Z_3_group : Group.
Proof.
  apply (mk_Group Z_3 op_Z_3 inv_Z_3 z_Z_3).
  induction a0, b0, c; compute; auto.
  induction a0; auto. 
  induction a0; auto.
Defined.

Theorem Z_3_eq_dec : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y.
  all: auto. all: right. all: discriminate.
Defined.


Definition GroupMorphism (G:Group) (H:Group) (f:G->H) : Prop :=  
    f(z G)=z H /\
    forall a:G, f(inv G a)=inv H (f(a)) /\
    forall a b : G, f(op G a b) = op H (f(a)) (f(b)).
