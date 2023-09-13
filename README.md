# bizcoq2023

**Bizonyításelmélet és Coq programcsomag**

**BMETE91AM58**

szerda 16-18, H405a

A funkcionális programozási paradigma áttekinthetővé, a tiszta típusrendszer bolondbiztossá teszi a programozási nyelveket (pl. Haskell, Rust). A Coq nyelv és társai (Lean, Agda, Idris) azzal fejelik meg ezt, hogy olyan erős a típusrendszerük, hogy kifejezhetők bennük a legkülönbözőbb bonyolultságú matematikai állítások is, konkrétan az egész matematika beléjük fér tételestül, bizonyításostul. Ezzel viszont nem csak tételbizonyításra, hanem kritikus informatikai rendszerek modellezésére és formális hitelesítésére is alkalmasak. A kurzus során informatikai, logikai ill. matematikai példákon keresztül nyerünk betekintést a Coq és Lean nyelvek programozásába. 

Molnár Zoltán Gábor,

BME TTK Algebra és Geometria Tsz., 

mozow@math.bme.hu

## Bővebben

A funkcionális programozási paradigma olyan megközelítést jelent az informatikában, ahol a programokra függvényekként tekintünk, amik adatokat esznek és adatokat adnak vissza. Az imperatív paradigmához képest, amely szerint a programok utasítások sorozata, a funkcionális programozás nem enged állapotparamétereket szerepeltetni (for i ...) és mellékhatásokat érvényesítani (print, non-defined), minden ilyen működést beépít vagy az inputba vagy az outputba vagy a függvénybe magába (monadizáció). Előnyei közé tartozik a kód jó olvashatósága és karbantarthatósága, a hibák könnyebb azonosíthatósága és a párhuzamosíthatósága.

A típusos funkcionális programozás a statikus típusrendszert ötvözi a funkcionális paradigmával, ami lehetővé teszi a kód minőségének és megbízhatóságának növelését. Az alkalmazások között megtalálhatóak a webes alkalmazások, adatfeldolgozó rendszerek és mesterséges intelligencia alkalmazások is. Például a Haskell és a Scala nyelvek funkcionális megközelítést alkalmaznak. Az adatfeldolgozásban a funkcionális programozás hasznos, mert az adattranszformációk egyszerűen leírhatók függvényekkel. Az alkalmazások erősebb típusrendszerekkel és megbízhatóbb kóddal rendelkezhetnek, ami különösen fontos kritikus rendszerek, pl. repülőgépek irányítási szoftvere vagy orvosi eszközök programozása esetén. A típusos funkcionális megközelítés lehetővé teszi a programok megbízható működését és a rendszer biztonságának biztosítását.

Ebben a kontextusban találkozunk a Coq bizonyításasszisztens programnyelvvel, amely magában foglalja a funkcionális programozás és a formális bizonyítások előnyeit is. A Coq egy olyan eszköz, amely lehetővé teszi a matematikailag pontos és formálisan igazolt programok írását és helyességük bizonyítását. A programokat és bizonyításokat a Coq nyelven írjuk, ami egy funkcionális programnyelv és egy formális levezetési nyelv kombinációja.

A Coq Thierry Coquand Calculus of Inductive Constructions nevű programozási nyelvének implementációja és a Curry-Howard izomorfizmust aknázza ki. Ez egy érdekes kapcsolat a számítástudomány és a matematika között: arra mutat rá, hogy a típusok állítások, a programok pedig bizonyítások. Ez az izomorfizmus praktikus alkalmazásokhoz is vezethet. Például a Coq nevű programnyelv és bizonyításasszisztens felhasználja ezt az összefüggést a formális bizonyítások készítéséhez és a megbízható szoftverfejlesztéshez. Ezenkívül a Curry-Howard izomorfizmus mélyebb betekintést nyújt abba, hogy hogyan működnek a programok és a matematikai bizonyítások, és hogyan lehet őket formálisan és rendszeresen vizsgálni.

## Telepítés

Mindenféle szoftverek, manualok, modulok, stb. elérhetősége alapvetően itt:

> https://coq.inria.fr/

_Win_: [Get Coq](https://coq.inria.fr/download) fül alatt a Win verzió letöltő linkje, már az első bekezdésben megvan. Aki Emacs-ot használ vagy használna, annak további ismertető: [pdf](http://staff.ustc.edu.cn/~xyfeng/teaching/TOPL/reading/ProofGeneral.pdf). Ehhez szükséges a Proof General nevű szerkesztő, amit az Emacs meghív. Aki nem szereti az Emacs-ot, annak a rendelkezésére áll a **CoqIDE** szerkesztő program, ami a Coq telepítése után az egyetlen futtatható file abban a könyvtárban.

_Linux_: Ubuntu alatt az alap vagy Synaptic csomagkezelőben elérhető a Coq-ra rákeresve. Akinek nem Ubuntuja van, az meg úgy is olyan okos, hogy annak magától is menni fog. CoqIDE szintén megtalálható, amennyiben az Emacs nem szimpi.

## Érintett témák

<!--
1. óra leírása: [itt](eloadas/1_bevezetes/) és a [.v file](eloadas/1_bevezetes/bizcoq_1.v). (Tanult parancsok és taktikák: Definition, Show Proof, Check, Print, SerachAbout, "match ... with |", reflexivity, unfold ..., apply ..., exact, assumption.)

2. óra leírása: [itt](eloadas/2_bonyolultabb/) és a [.v file](eloadas/2_bonyolultabb/bizcoq_2.v). (Tanult parancsok és taktikák: Structure, "induction x, y; auto; right; discriminate.")

3. óra leírása: [itt](eloadas/3_fák_listák/) és a [.v file](eloadas/3_fák_listák/bizcoq_3.v). (Tanult parancsok és taktikák: Require Import Omega (meg minden), Fixpoint (azaz rekurzív definíció), induction x, simpl, congruence, rewrite IHx.) 
-->

Lásd  [előadás](eloadas) mappa.

1. bool és Prop adattípusok és érvelés velük
2. nat, tree, list és minden: az induktív adattípusok, primitív rekurzív függvények
3. monadizáció, side effectek kezelése
4. Curry--Howard-izomorfizmus, lambda kalkulus és funkcionális programozás
5. matematikai elméletek beprogramozása és bizonyítások
6. egyszerű, polimorf és függő típusok

## Követelmények
Aktív órai jelenlét, minden második alkalomra házik készítése, két beadandó feladatcsomag a 7. és 13. héten. 

## Egyebek

Hivatalos cuccok: https://math.bme.hu/~mozow/biz_coq.html.

LaTeX konverter md file-hoz: https://jsfiddle.net/8ndx694g/.

Github markup puska: https://github.com/adam-p/markdown-here/wiki/Markdown-Cheatsheet.

Természetes számok kezelése: Adam Chlipala spéci taktikái ([v](forrasok/CpdtTactics.v)) a nat típusban való számolások kezelésére (pl. "crush" taktika) (leírás: [net](http://adam.chlipala.net/cpdt/)). Hasonlóképpen kiválóan kezeli a matematikai témákat a [Mathematical Components](https://math-comp.github.io/). 

Leveztésfa készítő csomagok LaTeX-ben ([pdf](latex_sablon/levezetesfa.pdf), [tex](latex_sablon/levezetesfa.tex)).

Coq jelölés, taktika és definíció Cheat Sheet: [pdf](https://www.inf.ed.ac.uk/teaching/courses/tspl/cheatsheet.pdf).

**Egy tényleg automatikus prover:**

http://zenon-prover.org/

**Online Coq, amelyik képes proof tree-ket is készíteni:**

http://carol.dimap.ufrn.br/proofweb/

**Hivatalos online Coq (Firefox)**

https://coq.vercel.app/scratchpad.html

**Online Lean 3** (Lean 4 a legújabb!)

https://leanprover-community.github.io/lean-web-editor/

https://leanprover.github.io/theorem_proving_in_lean/index.html

