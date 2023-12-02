## Konkrét véges típusok

bool a kételemű típus volt. Példaként nézzünk egy háromelemű típust!

<img src="https://render.githubusercontent.com/render/math?math=%5Cmathbf%7BZ%7D_3%5E%2B%20%5Cequiv%20%5Cmathbf%7BZ%7D%2F3%5Cmathbf%7BZ%7D%2C%5C%3B%5C%3B%5C%3BZ_3%3D%5C%7B0%3B1%3B2%5C%7D">

Ez a hárommal való osztás maredékainak halmaza, illetve most tekintsünk erre úgy, hogy ő egy additív jelölésű csoport. Be fogjuk látni, hogy ez a maradékok összeadásával, a megfelelő inverz elemekkel és a 0-van, mint neutrális elemmel valóban csoportot alkot. Ezt a matematikusok kedvéért. A mérnökökkel azt nézzük meg, hogy ebben is (mind minden konstruktív megadású véges típusban) igaz, hogy az egyenlőség algoritmikusan eldönthető.

A Z_3 induktív típus:

````coq
Inductive Z_3 : Set :=
  | n : Z_3 
  | a : Z_3
  | b : Z_3.
````

Efelett a műveletek:

````coq
Definition ope x y :=
  match x , y with
  | n , y => y
  | x , n => x
  | a , b => n
  | b , a => n 
  | a , a => b
  | b , b => a
  end.

Definition inve x :=
  match x with
  | n => n
  | a => b
  | b => a
  end.
  ````
  Structure 
  
  ````coq
  Structure Group : Type := const_kozos
{
  A :> Set;

  op : A -> A -> A ;
  inv : A -> A ;
  z : A ;

  op_assoc : forall a b c, op a (op b c) = op (op a b) c;
  op_z : forall a, op a z = a /\ op z a = a ;
  op_inverse : forall a, op a (inv a) = z /\ op (inv a) a = z
}.
  ````

**1.** Z_3 a megfelelő műveletekkel valóban a Group típus lakója.

````coq
Theorem Z_3_group : Group.
Proof.
  apply (const_kozos Z_3 ope inve n).
  induction a0, b0, c; compute; auto.
  induction a0; auto. 
  induction a0; auto.
Defined.
````

**2.** Az egyenlőség Z_3-ban (is) eldönthető.

````coq
Theorem Z_3_eq_dec : forall (x y: Z_3), x = y \/ x <> y.
Proof. 
  induction x, y; auto; right; discriminate.
Defined.
````
````coq
(*Morfizmusok*)

Definition GroupMorphism (G:Group) (H:Group) (f:G->H) : Prop :=  
    f(z G)=z H /\
    forall a:G, f(inv G a)=inv H (f(a)) /\
    forall a b : G, f(op G a b) = op H (f(a)) (f(b)).

(*Pl. a Z_1->Z_3, e|--->n leképezés is egy csoportmorfizmus *)


Inductive Z_1 : Set :=
  | e : Z_1.

Definition ope_1 (x:Z_1) (y:Z_1) :=
  match x , y with
  | e , e => e
  end.

Definition inve_1 x:Z_1 :=
  match x with
  | e => e
  end.

Theorem Z_1_group : Group.
Proof.
  apply (const_kozos Z_1 ope_1 inve_1 e).
  induction a0, b0, c; compute; auto.
  induction a0; auto. 
  induction a0; auto.
Defined.

Definition f_Z_1_Z_3 : Z_1->Z_3 := fun (x:Z_1) => match x with e => n end.

Theorem f_Z_1_Z_3_csoportmorfizmus : GroupMorphism (Z_1_group) (Z_3_group) f_Z_1_Z_3.
Proof.
  unfold GroupMorphism.
  split.
  compute; auto.
  split.
  induction a0.
  compute; auto.
  induction a0, b0.
  induction a0.
  compute; auto.
Qed.
````



