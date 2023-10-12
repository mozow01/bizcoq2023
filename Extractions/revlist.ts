// Hát, ő így csinál listát
type List<T> = { constructor: "nil" } | { constructor: "cons"; head: T; tail: List<T> };

function reverse<T>(l: List<T>): List<T> {
  switch (l.constructor) {
    case "nil":
      return { constructor: "nil" };
    case "cons":
      // itt van egy újabb szép pattern matching! 
      const h = l.head;
      const t = l.tail;
      return app(reverse(t), { constructor: "cons", head : h, tail: { constructor: "nil" } });
  }
}

// Nincs neki app-ja, ezért csinálunk
function app<T>(l: List<T>, m: List<T>): List<T> {
  switch (l.constructor) {
    case "nil":
      return m;
    case "cons":
        const h = l.head;
        const t = l.tail;
      return { constructor: "cons", head : h, tail: app(t, m) };
  }
}

// ez a Correctness silány utánzata
function reverseCorrect<T>(l: List<T>): boolean {
  return JSON.stringify(reverse(reverse(l))) === JSON.stringify(l);
}

// tesztek
const list1: List<number> = { constructor: "cons", head: 1, tail: { constructor: "cons", head: 2, tail: { constructor: "cons", head: 3, tail: { constructor: "nil" } } } };
const reversedList1 = reverse(list1);

console.log(reversedList1);
console.log(reverseCorrect(list1));
