# Extraktok

A datatypes.html-t és a társait érdemes letölteni egy könyvtárba és onnan egy böngészőben megnyitni a .html-t. Majd "További eszközök / Fejlesztői eszközök" és ezen belül nyitni egy "konzolt". Ha ez megvan, a definiált függvényekkel lehet használni, a .js-t módosítva új adatokat definiálni...

Lényeges, hogy ha a .ts-t akarjuk módosítani, ahhoz kell node és node-typscript lásd: [https://github.com/mozow01/InfoMC/tree/main/orak/8_ora#typescript] Ha ez megvan, a fájlokat tartalmazó könyvtáron belül a  ````tsc file.ts```` terminál parancs legyártja a .js-t, és frissítve a html-t lehet újra konzol parancsokat kiadni.

## Bináris fák levélhossza

Coq kód:

````coq
Inductive tree : Set :=
  | leaf : tree
  | node : tree -> tree -> tree.

Fixpoint treeLength (t : tree) {struct t} : nat :=
  match t with 
    | leaf => 1
    | node t1 t2 => (treeLength t1) + (treeLength t2)
  end.
````

TypeScript kód:

````typescript

// Címke nélküli bináris fák típusa, "levélhossz" függvény
//
// TS-ben nincs induktív típus, de van olyan, hogy 
// hasonló objektumok típusa. Ilyet csinálunk:
type Tree =
  | { tag: 'leaf' }
  | { tag: 'node'; left: Tree; right: Tree };

// A treeLength függvény összeszámolja a leveleket
function treeLength(tree: Tree): number {
  if (tree.tag === 'leaf') {
    return 1; 
  } else {
    return treeLength(tree.left) + treeLength(tree.right);
  }
}

// tree1: leaf
//
// tree2: leaf leaf
//           \/
//          root
//
// tree3: leaf leaf
//           \/
//          node  leaf  
//              \/
//             root
const tree1: Tree = { tag: 'leaf' };
const tree2: Tree = { tag: 'node', left: tree1, right: tree1 };
const tree3: Tree = { tag: 'node', left: tree2, right: tree1 };

// kilog :)
const l2 = treeLength(tree2);
console.log(l2); 
````



