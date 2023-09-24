// A treeLength függvény összeszámolja a leveleket
function treeLength(tree) {
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
var tree1 = { tag: 'leaf' };
var tree2 = { tag: 'node', left: tree1, right: tree1 };
var tree3 = { tag: 'node', left: tree2, right: tree1 };
// kilog :)
var l2 = treeLength(tree2);
console.log(l2);
