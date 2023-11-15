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
