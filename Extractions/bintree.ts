
// Címke nélküli bináris fák típusa, "levélhossz" függvény
//
// TS-ben nincs induktív típus, de van olyan, hogy 
// hasonló objektumok típusa. Ilyet csinálunk:
type Tree =
  | { tag: 'leaf' }
  | { tag: 'node'; left: Tree; right: Tree };

// A treeLength függvény összeszámolja a leveleket
function treeLength(tree: Tree): number {
  switch (tree.tag) {
    case 'leaf':
      return 1; 
    case 'node':
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

