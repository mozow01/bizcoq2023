1. a) Implementáld a Z_6 maradékosztályt, mint véges induktív adattípust, definiáld a csoportműveleteit (additív csoportművelet, neutrális elem, inverz elem) úgy, hogy nem mind a 36 esetet írod le, hanem átviszed nat-ba és az ottani moduló műveleteken keresztül hozod vissza az induktív típusba. Igazold, hogy a Z_6 egyenlősége eldönthető. ( https://coq.inria.fr/doc/V8.18.0/stdlib//Coq.Arith.PeanoNat.html )
	
2. Készítsd el a kommutatív csoportok ComGroup struktúráját. Adj meg egy olyan h ComGroup-morfizmust, amelyik Z_6 -> Z_3 ráképezés (epimorfizmus = szürjektív morfizmus), ez utóbbi azt jelenti, hogy minden Z_3-beli elemet felvesz értékként. Igazold, hogy h valóban morfizmus és hogy ráképezés.

3.  Írj egy olyan
list nat -> nat -> list (option nat)
típusú függvényt, ami természetes számok egy listáját eszi, majd egy természetes számot, amit kivon minden listaelemből és visszaad egy listát, amielynek eleme None, ha kivezet a kivonás natból és Some x-et, ha a kivonás eredménye x.

4. Az option bind lekötő operátor felhasználásával írj egy programot, ami természetes számok egy listáját eszi, és egy option nat-ot ad vissza, amiben az eredmény, hogy egymás után libasorban kivonva az lista elemeit mit kapunk. Legyen a kivonás safe, azaz option értékű. pl. [2 ; 3 ; 6 ; 2] eredménye legyen: 2-3 => None, tehát None,  [3 ; 1 ; 6 ; 2]-ben 3-1 = 2, 2-6 => None, [6 ; 3 ; 1 ; 2]  6-3=3, 3-1=2, 2-2=0 => Some 0.
