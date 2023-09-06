(*Megnézi a nat (természetes szám) adattítus definícióját*)

Print nat.

(*Megnézi a nat indukciós szabályát realizáló program (teljes indukció) típusát*)

Check nat_ind.

(*Az induktív definíció egyfajta Backus--Naur Form, ilyen módon definiálunk egy új adattípust, a Boole-t.*)

Inductive Boole : Set :=
  | igaz : Boole
  | hamis : Boole.

(*Megnézi a Boole típus indukciós szabályát realizáló program (Boole indukció) típusát*)

Print Boole_ind.

(*A Boole feletti "és" művelet rekurziómentes definíciója*)

Definition és (b1 b2 : Boole) := 
    match b1 with 
      | igaz => match b2 with 
                  | igaz => igaz
                  | hamis => hamis
                end
      | hamis => hamis
    end.

(* A b változó típusát Boole-ként deklaráljuk, ez nem definíció, csak "axióma", ezért lesz sárga a kód a futtatás után.*)

Parameter b : Boole.

(*Az "(és b hamis)" ill. "(és hamis b)" értékének kiszámítása, mindaddig, amíg a redukciók (konverziók) képesek eljutni.*)

Eval compute in (és hamis b).

(*
 = hamis
     : Boole
ez ment, "normálformára" redukálta
*)

Eval compute in (és b hamis).

(*
 = match b with
       | igaz | _ => hamis
       end
     : Boole
*)

(* Ez a kifejezés nem tud "normálformává" konvertálódni, mert a b komputációsan határozatlan és a definíciót lefuttatva, nem tudja őt kikerülni.*)

Eval simpl in (és b hamis).

(*
  = és b hamis
     : Boole

a simpl kiértékelési stratégia csak addig csinálja a konverziót, amíg olvasható nem lesz (a végén kihagyja az ι-konverziót, látható, hogy nem megy neki sokáig.)
*)

(*A Boole feletti "és" művelet rekurziómentes definíciója*)

Definition vagy b1 b2 :=
    match b1 with 
      | igaz => igaz
      | hamis => match b2 with 
                  | igaz => igaz
                  | hamis => hamis
                 end
    end.

(*A Coq automatikusan inferálja ennek a típusát a program szerkezete alapján.*)

(*Disztributív szabály 1*)

Theorem dist_1 : forall b1 b2 b3 : Boole, és b1 (vagy b2 b3) = vagy (és b1 b2) (és b1 b3).
(*Itt beindul a "Proof Mode". Áttérünk a típusos termek funkcionális Gallina nyelvéről a taktikák Ltac nyelvére. De esztétikai okokból oda szoktuk írni a Proof parancsot. Utána a nyelv imperatívvá válik, de a korábban definiált függvényeket akármikor használhatjuk *)
Proof.
induction b1, b2, b3.
all: compute; reflexivity.
Qed.

(*Mivel látjuk, hogy "forall" a külső művelet, az indukciós séma feltételeit fogjuk bebizonyítani: indduction ... Utána 2^3=8 eset keletkezik, mert a Boole-nak 2 eleme van, a tétel 3 változós. all: minden goal-ra ugyanazt alkalmazza, compute kiszámítja az és és vagy függvényeket a Boole adott lakóin, reflexivity az egyenlőségről mondja, hogy triviálisan érvényes. Az ; jel a parancsok egymásután fűzését jelenti.*)

Theorem dist_2 : forall b1 b2 b3 : Boole, vagy b1 (és b2 b3) = és (vagy b1 b2) (vagy b1 b3).
Proof.
induction b1, b2, b3.
all: simpl; auto.
Defined.

(* Picit másként: simpl is célt ér (sőt, a call-by-value, call-by-name redukció us (cbv, cbn)). auto a legegyszerűebb automatikus taktika a legtriviálisabb lépések elvégzésére. *)

(* Házi Feladat:

1. Telepítsük a Coq-ot és ismerkedjünk a CoqIDE-vel
2. Definiáljuk a Boole feletti negációt! Esetleg a ha-akkor-t.
3. Bizonyítsuk be a De Morgan azonosságokat.
4. Kérdezzünk, örüljünk, ha sikerült :) *)




