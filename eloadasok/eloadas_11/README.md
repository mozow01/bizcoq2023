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




## Egy ,,One-Shot DETERMINISTIC Decision Problem'' 

Kajálni szeretnénk ,,pizzáért indultam, de giros lett belőle'' szellemben. A vállalkozók áldozatai vagyunk. Hogy mit sikerül kapnunk, azt teljes egészében ők határozzák meg. 

<img src="https://render.githubusercontent.com/render/math?math=%5Cboxed%7Bs%3A%5Cmathrm%7BState%7D%7D%5C%3B%5C%3B%5Cxrightarrow%7Ba%3A%5Cmathrm%7BAction%7D%7D%5C%3B%5C%3B%20%5Cboxed%7Bs'%3A%5Cmathrm%7BState%7D%7D">

Ennek ellenére megpróbálunk racionális döntést hozni, melyben az is szerepet játszik, hogy milyen korábbi tapasztalataink vannak. A számunkra kedvező eseteket bónuszponttal jutalmazni fogjuk. (Úgy is fogalmazhatunk, kognitív tudományi szempontból, hogy megpróbáljuk kideríteni, hogy az agy ezt gyorsan dönti-e el: ha triviális a választás, akkor igen, ha nem, akkor nem.

Az állapotok a kaják lesznek: State = {pizza, bécsi, giros}, a tettek, hogy melyik kajáldába megyünk: Action = {Carlo, Margo, Artak}. Az átmenetfüggvény határozza meg, hogy mi, akik introvertáltak vagyunk, és az *s* kaját akarjuk és az *a* kajáldát választjuk, akkor milyen kaját kapunk ott. 

````transition (s:State) (a:Action) : State :=````

| |Carlo|Margo|Artak|
|---|---|---|---|
|pizza| pizza | pizza | giros|
|bécsi| pizza | bécsi | bécsi|
|giros| pizza | pizza | giros|

Preferenciáink is vannak: pl. tudjuk, hogy Margó baromi jó rántotthúst süt, de rossz pizzát és nem veszi föl a maszkot, mert vírustagadó. A többi árús kb. OK. Ezt a juti függvény adja meg:

````utility (s:State) (a:Action) : nat :=````

| |Carlo|Margo|Artak|
|---|---|---|---|
|pizza| 9 | 2 | 0 |
|bécsi| 0 | 10 | 7 |
|giros| 0 | 0 | 10|

A *modell* szerint úgy döntük, hogy készítünk egy ágens ( :trollface: ) döntési függvényt, amit a következő optimalizációs számítást végzi el:

<img src="https://render.githubusercontent.com/render/math?math=%5Cmathrm%7BAgentAction%7D(s)%3D%5Cunderset%7Ba%3A%5Cmathrm%7BAction%7D%7D%7B%5Cmathrm%7Bargmax%7D%7D%5Cmathrm%7Butility%7D(%5Cmathrm%7Btransition(s%2Ca)%2Ca%7D)">

vagyis megmondja, mi az *s* kaja függvényében egy olyan *a* tett, amelyhez a legtöbb jutalompont tartozik. 

## Az ArgMax megvalósítása két lépésben -- pár vs lista, konkrét eset

````coq
Inductive H : Set :=
  | Carlo : H
  | Margo : H
  | Artak : H.

Print pair.

Require Import Omega List.

Definition MaxPairTwo (x y : H*nat) : H*nat :=
  match x, y with
    | pair a n, pair b m => 
       if (le_lt_dec m n) then pair a n else pair b m
  end.

Eval compute in MaxPairTwo (Margo,7) (Carlo,6).

Definition ArgMaxTwo (x y : H*nat) : H := fst(MaxPairTwo x y).

Eval compute in ArgMaxTwo (Margo,7) (Artak,6).

Definition MaxPairThree (x y z : H*nat) : H*nat := 
  MaxPairTwo (MaxPairTwo x y) z.

Eval compute in MaxPairThree (Margo,7) (Carlo,6) (Artak, 8).

Fixpoint MaxPair (l : list (H*nat)) : H*nat := 
  match l with 
   | nil => (Margo,0)
   | cons x l' => MaxPairTwo x (MaxPair l')
  end.

Eval compute in 
MaxPair ((Margo,7)::(Margo,8)::(Artak,6)::(Carlo,10)::nil).

(*A véges halmazon függvény, mint lista *)

Definition listing (f: H -> nat) : list (H*nat) := 
  (Carlo,f(Carlo))::(Margo,f(Margo))::(Artak,f(Artak))::nil. 

Definition f (x:H) : nat :=
  match x with
    | Carlo => 0
    | Margo => 2
    | Artak => 2
  end.

Eval compute in MaxPair (listing f).

Eval compute in fst (MaxPair (listing f)).
````

````coq
Fixpoint MaxPair' (l : list (H*nat)) : option (H*nat) := 
  match l with 
   | nil => None
   | cons x l' => match (MaxPair' l') with 
                   | None => None
                   | Some c => Some (MaxPairTwo x c)
                  end
  end.
````

## Az ArgMax megvalósítása két lépésben -- opcionális típus, általános eset

````coq
Require Import Lia Arith List.

Fixpoint MaxPair' (l : list (H*nat)) : option (H*nat) := 
  match l with 
   | nil => None
   | cons x l' => match (MaxPair' l') with 
                   | None => None
                   | Some c => Some (MaxPairTwo x c)
                  end
  end.

Definition MaxPairTwo'' {X:Set} (x y : option (X*nat)) : option (X*nat) :=
  match x, y with
    | None, None => None
    | None, Some b => Some b
    | Some a, None => Some a
    | Some (pair a n), Some (pair b m) => 
       if (le_lt_dec m n) then Some (pair a n) else Some (pair b m)
  end.

Fixpoint MaxPair'' {X:Set} (l : list (option(X*nat))) : option (X*nat) := 
  match l with 
   | nil => None
   | cons x l' => MaxPairTwo'' x (MaxPair'' l')
  end.
````

## A probléma megoldása

(folyt.)

````coq
Inductive Action : Set :=
  | Margo : Action
  | Carlo : Action
  | Artak : Action.

Inductive State : Set :=
  | pizza : State
  | bécsi : State
  | giros : State.

Definition transition (s:State) (a:Action) : State :=
  match s, a with
   | _ , Carlo => pizza
   | pizza , Margo => pizza
   | bécsi , Margo => bécsi   
   | _ , Margo => pizza
   | bécsi , Artak => bécsi
   | giros , Artak => giros
   | _ , Artak => giros
  end.

Eval compute in (transition pizza Artak).

Definition utility (s:State) (a:Action) : nat :=
  match s, a with
   | pizza , Carlo => 9
   | bécsi , Artak => 6
   | bécsi , Margo => 10
   | pizza , Margo => 2
   | giros , Artak => 10
   | _ , Margo => 0
   | _ , Carlo => 0
   | _ , Artak => 0
  end.

Definition listing (f: Action -> nat) : list (option(Action*nat)) := 
  Some (Carlo,f(Carlo))::Some (Margo,f(Margo))::Some (Artak,f(Artak))::nil. 

(*AgentAction(s) := arg max_a {utility(transition(s a) a)} *)

Definition AgentAction(s:State) : option Action := 
  ArgMax (listing (fun x:Action => utility (transition s x) x) ).

Eval compute in AgentAction pizza.
````
