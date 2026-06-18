# Zippy: An algebra for Path Sets

## Abstract

Zippy is a small language for programming with finite sets of structured paths. A value such as `parent.Tom.Bob`, `edge.x.y`, or `Cell.2.1` is a word in a free monoid; a space is a finite set of such words. With only union, intersection, subtraction, path product, prefix restriction, wrapping, unwrapping, first-symbol iteration, and recursion, Zippy expresses relational queries, Datalog-style fixed points, graph algorithms, Game of Life, and trie-indexed fuzzy search.

The set of paths is simultaneously a relation, a trie, a tagged database, and a finite language. This makes several familiar algebras available at once. The finite spaces form a ring of sets under union and relative complement; adding path concatenation gives an idempotent semiring of finite languages. On top of that core, prefix restriction, tails, wrapping, unwrapping, and iteration provide the database operations: selection, projection, nesting, unnesting, grouping, and limited universal queries. The result is a compact calculus in which high-level relational programs are written as algebraic expressions and later lowered by equational laws.

The paper develops the calculus, relates it to idempotent semirings, Kleene algebras, complex-object query languages, and trie automata, then works through five examples: family queries, strongly connected components, Conway's Game of Life, semi-naive Datalog evaluation, and interval-based fuzzy temperature search.

## 1. The core

A path is a sequence of items printed with dots:

```text
parent.Tom.Bob
child.Bob.Tom
female.Ann
edge.x.y
Cell.1.2
0.1.1.1.0.C
```

A space is a finite set of paths. That single choice collapses several common data models into one representation. A binary relation is a set of two-item paths. A tagged union is a set of paths whose first item is the tag. A trie is a set of leaves sharing prefixes. A sparse table is a set of coordinate paths carrying values at the tail. A graph is a set such as `edge.a.b`, `edge.b.c`, and so on.

The payoff is that many operations that normally require separate APIs become variations on path algebra. Selection is prefix restriction. Projection is taking tails. A join is first-symbol iteration plus unwrapping. A derived relation is wrapping under a new tag. A fixed point is a recursive routine over a growing space.

Zippy's core types can be presented without much machinery:

```scala
enum PathItem:
  case Symbol(n: String)
  case Variable(n: String)
  case Arity(k: Int)

case class PathValue(items: List[PathItem]):
  def show: String = items.map(_.show).mkString(".")

case class SpaceValue(paths: Set[PathValue])
```

A path expression is either a variable, a constant, a concatenation, or a grounded host-language computation:

```scala
enum Path:
  case Deref(pr: PathRef)
  case Constant(pi: PathValue)
  case Concat(l: Path, r: Path)
  case GroundedPP(p: Path, f: PathValue => PathValue)
  case GroundedSP(p: Space, f: SpaceValue => PathValue)
```

The space language is similarly small. This is the useful subset used throughout the examples:

```scala
enum Space:
  case Empty
  case Call(r: RoutinePtr, refs: Vector[Path], mentions: Vector[Space])
  case Mention(variable: SpaceMention)
  case Singleton(p: Path)
  case Literal(p: SpaceValue)
  case Union(x: Space, y: Space)
  case Intersection(x: Space, y: Space)
  case Subtraction(x: Space, y: Space)
  case Restriction(x: Space, y: Space)
  case Composition(x: Space, y: Space)
  case Iteration(src: Space, symbol: PathRef, rest: SpaceMention, templates: Space)
  case Wrap(src: Space, p: Path)
  case Unwrap(src: Space, p: Path)
  case TailsUnion(src: Space)
  case TailsIntersection(src: Space)
  case GroundedPS(p: Path, f: PathValue => SpaceValue)
  case GroundedSS(p: Space, f: SpaceValue => SpaceValue)
  case Limit(i: Int, x: Space)
```

The implementation gives these constructors a compact surface syntax. In the rest of the paper, `S"family"` is a named space, `P"x"` is a path variable, `"Aunt" x s` wraps a space under a path prefix, `s("child")` unwraps the prefix `child`, `\/` is union, `/\` is intersection, `\` is subtraction, and `<|` is restriction by prefix.

## 2. Spaces as a ring of sets over words

Let `Σ*` be the free monoid of paths: the set of all finite words over path items, with concatenation as multiplication and the empty path as identity. A Zippy `SpaceValue` is a finite subset of `Σ*`.

Under union and relative complement, finite spaces behave as a ring of sets. In the measure-theoretic sense, a ring of sets is a nonempty family of sets closed under union and relative complement; closure under intersection follows because `A ∩ B = A \ (A \ B)`. The order-theoretic variant instead asks for closure under union and intersection. Zippy has union, intersection, and subtraction directly, so it is comfortably inside both finite readings. See the standard terminology at [Ring of sets](https://en.wikipedia.org/wiki/Ring_of_sets).

Path composition adds another operation:

```text
A · B = { a.b | a ∈ A, b ∈ B }
```

This is language multiplication. If we extended from finite spaces to all subsets of `Σ*`, then union as join and language multiplication would form the usual powerset quantale of a monoid. Zippy intentionally lives in the finite fragment, but the analogy remains useful:

```text
A · (B ∪ C) = (A · B) ∪ (A · C)
(A ∪ B) · C = (A · C) ∪ (B · C)
∅ · A = ∅ = A · ∅
```

That is enough algebra to explain most of the language. The ring-of-sets operations handle filtering and exclusion. The word product handles structure. Prefix restriction and tail operations exploit the fact that the words are not opaque elements but trie paths.


## 3. Algebraic links

Zippy is best understood as a small intersection point between three older stories: idempotent semirings for path problems, relational and complex-object algebra for databases, and language/trie theory for finite automata. Each story explains a different part of the design.

### 3.1 Idempotent semirings and Kleene algebras

Ignore, for a moment, restriction, iteration, and tails. Keep only spaces, union, the empty space, composition, and the singleton empty path. Then spaces form the finite-language instance of an idempotent semiring:

```text
addition       A + B   = A ∪ B
zero           0       = ∅
multiplication A · B   = { a.b | a ∈ A, b ∈ B }
one            1       = { ε }
```

Union is associative, commutative, and idempotent; `A ∪ A = A`. Composition is associative because path concatenation is associative. Composition distributes over union on both sides, and the empty space annihilates composition:

```text
A · (B ∪ C) = (A · B) ∪ (A · C)
(A ∪ B) · C = (A · C) ∪ (B · C)
∅ · A = ∅ = A · ∅
```

The idempotent addition induces the natural order:

```text
A ≤ B  iff  A ∪ B = B  iff  A ⊆ B
```

This is the same algebraic shape that appears in regular languages, relation algebra, and graph path problems. A graph edge relation is a language of length-two words; composing relations is multiplying path languages; union is choice. A reachability computation is the least solution of a closure equation.

Kleene algebra adds a star operation, usually written `A*`, for finite iteration:

```text
A* = 1 ∪ A ∪ A² ∪ A³ ∪ ...
```

Zippy does not expose a general `star` constructor. Instead, recursive routines compute least fixed points over finite spaces. The Datalog transitive-closure example is precisely a Kleene-style closure specialized to a tagged binary relation:

```scala
val r = fixpoint(last =>
  MQT(last, List("edge.$x.$y"), "path.$x.$y") \/
  MQT(last, List("path.$x.$y", "path.$y.$z"), "path.$x.$z"))
```

The semiring view explains why the graph examples feel natural: they are path problems over an idempotent choice-and-composition algebra. It also explains the semi-naive evaluator. The naive program repeatedly multiplies the whole known relation by itself; the semi-naive program computes the finite difference of that multiplication, keeping only summands in which at least one input is new.

The extra Zippy operators live above the semiring core. `TailsUnion` is not semiring multiplication; it is projection:

```text
TailsUnion(X) = { r | ∃a. a.r ∈ X }
```

`Iteration` is not a semiring law; it is grouped elimination over the first letter:

```text
X = ⋃_{a ∈ heads(X)} a · X_a
where X_a = { r | a.r ∈ X }
```

The semiring gives choice and composition. `TailsUnion` and `Iteration` add the relational machinery needed to inspect and regroup structured words.

### 3.2 Relational algebra and complex-object algebras

A flat tuple can be encoded as a path. A binary relation `R(x,y)` is a space of paths `x.y`. A tagged relation `edge(x,y)` is a space of paths `edge.x.y`. Once tuples are words, much of relational algebra appears as path algebra:

```text
union          R ∪ S
intersection   R ∩ S
difference     R \ S
selection      R <| prefixes
projection     TailsUnion(R)
renaming       Wrap / Unwrap under tags
join           Iteration plus Unwrap or prefix restriction
```

The family examples are ordinary joins written without a separate join operator. For instance, a mother query joins `child(person,parent)` with `female(parent)` by unwrapping the child relation at the current person and intersecting the resulting parent set with `female`:

```scala
val mothers =
  "Mother" x S"people".iter("person", "_",
    P"person" x
      (S"family"("child" x P"person") /\ S"family"("female"))
  )
```

This is a relational query, but the join key is a path prefix rather than a named column. `iter` supplies the bound variable; `unwrap` performs an indexed selection; intersection enforces equality with the second predicate.

The same representation also resembles complex-object and nested-relational algebras. In those algebras, data may be structured: sets inside records, records inside sets, and so on. Zippy flattens such structure into paths, but preserves enough shape to rebuild it operationally. A first item is a field name or tag. A suffix is the nested value below that field. `Wrap` nests by adding a field or constructor, and `Unwrap` unnests by removing it.

For example, the path set:

```text
book.title.Foundation
book.author.Serge
book.author.Rick
article.title.Querying
article.cites.book1
```

can be read either as a flattened document tree or as several tagged relations. The expression `S"db"("book")` unnests the `book` object; `"result" x ...` nests the answer under `result`; `iter` groups all tails by the next field:

```scala
S"db"("book").iter("field", "values",
  P"field" x S"values")
```

That grouping operation is the bridge from flat paths back to nested objects. It is similar in spirit to the nesting/unnesting operators of complex-object query languages, but it is intentionally first-order and trie-shaped: grouping is always by the next path item.

`TailsIntersection` adds a small but useful universal quantifier. If we restrict a key-value space to selected keys and then intersect the tails under those keys, we compute values common to every selected key:

```scala
test("intersection all") {
  val keys =
    (s("foo", "bar") x ss"e0") \/
    (s("foo", "cux", "baz") x ss"e1") \/
    (s("cux") x ss"e2")

  assert(eval(/\(keys <| s("foo", "bar"))).prettyLines == "e0")
}
```

After restriction, the relevant rows are:

```text
foo.e0
foo.e1
bar.e0
```

`TailsIntersection` returns the tail present under every selected head, namely `e0`. In logical notation, it computes:

```text
{ v | ∀k ∈ selectedKeys. k.v ∈ keys }
```

That is not a full higher-order quantifier over arbitrary formulas, but it is exactly the universal query that arises in trie-shaped key/value data: common tags, common capabilities, common neighbors, common attributes.

### 3.3 Tries, automata, quotients, and derivatives

A space is a finite language over the alphabet of path items. The trie of that language is not an implementation detail; it is the data structure suggested by the semantics.

For a prefix set `P`, restriction is language intersection with a finite union of prefix cylinders:

```text
X <| P = X ∩ (P · Σ*)
```

Here `Σ*` is the set of all suffixes, and `P · Σ*` means “all words whose prefix is in `P`.” In the current evaluator this is written as a scan:

```scala
case Space.Restriction(x, prefixes) =>
  val ps = recs(prefixes)
  recs(x).filter(w => ps.exists(p => w.items.startsWith(p.items)))
```

A trie-native evaluator would instead descend to each prefix in `P` and enumerate the subtree below it. That changes the practical cost from “scan all of `X`” to “walk the selected prefixes and emit the result.” Ignoring prefix lookup cost and sharing details, the work becomes proportional to the size of the answer rather than the size of the database.

The tail operations are language quotients. For a letter `a`, the left quotient of `X` by `a` is:

```text
a⁻¹X = { r | a.r ∈ X }
```

The children of a trie node are exactly the nonempty single-letter quotients. `Iteration` enumerates those quotients:

```text
for each a with a⁻¹X ≠ ∅:
  symbol = a
  rest   = a⁻¹X
  evaluate template
```

That is what the evaluator does by grouping on the first path item:

```scala
case Space.Iteration(src, symbol, rest, template) =>
  Set.from(for
    (h, tails) <- recs(src).groupMap(w => PathValue(w.items.head :: Nil))(w => PathValue(w.items.tail))
    out <- eval(template)(using pc.grown(Map(symbol -> h)),
                                  sc.grown(Map(rest -> SpaceValue(Set.from(tails)))),
                                  rc).paths
  yield out)
```

This connects Zippy to the derivative view of automata. In regular-language theory, a derivative or quotient describes what remains to be matched after consuming a symbol. Zippy's `rest` is exactly that remainder language for one consumed path item. `TailsUnion` is the union of all nonempty one-letter quotients:

```text
TailsUnion(X) = ⋃_{a ∈ heads(X)} a⁻¹X
```

`TailsIntersection` is the corresponding meet:

```text
TailsIntersection(X) = ⋂_{a ∈ heads(X)} a⁻¹X
```

This is why the same operator can be read as projection in relational algebra and as a quotient in automata theory. The path representation makes those views coincide.

The implementation consequence is important. A trie stores a finite language as a map from head symbols to subtries. Then:

```text
Restriction by prefix   = descend to the prefix node, then enumerate
Iteration               = iterate over the child map
TailsUnion              = union child subtries
TailsIntersection       = intersect child subtries
Unwrap                  = descend to one prefix
Wrap                    = add a prefix node above a trie
```

This would make restriction and iteration output-sensitive for the common cases. The current prototype expresses the semantics directly with sets and scans, but the algebra is already trie-native. The notation records enough structure for a backend to avoid treating paths as opaque strings.

## 4. The operations

The direct evaluator is almost the denotational semantics. The important cases fit on one page:

```scala
def eval(s: Space)(using pc: PathContext, sc: SpaceContext, rc: PartialFunction[RoutinePtr, Routine]): SpaceValue =
  def recp(x: Path): List[PathItem] = x match
    case Path.Deref(pr)       => pc.resolve(pr).items
    case Path.Constant(pi)    => pi.items
    case Path.Concat(l, r)    => recp(l) ++ recp(r)
    case Path.GroundedPP(p,f) => f(PathValue(recp(p))).items
    case Path.GroundedSP(s,f) => f(SpaceValue(recs(s))).items

  def recs(x: Space): Set[PathValue] = x match
    case Space.Empty          => Set()
    case Space.Mention(p)     => sc.resolve(p).paths
    case Space.Singleton(p)   => Set(PathValue(recp(p)))
    case Space.Literal(v)     => v.paths

    case Space.Union(x, y)        => recs(x) union recs(y)
    case Space.Intersection(x, y) => recs(x) intersect recs(y)
    case Space.Subtraction(x, y)  => recs(x) removedAll recs(y)

    case Space.Restriction(x, prefixes) =>
      val ps = recs(prefixes)
      recs(x).filter(w => ps.exists(p => w.items.startsWith(p.items)))

    case Space.Composition(x, y) =>
      val ys = recs(y)
      for a <- recs(x); b <- ys yield PathValue(a.items ++ b.items)

    case Space.Wrap(src, p) =>
      val prefix = recp(p)
      recs(src).map(w => PathValue(prefix ++ w.items))

    case Space.Unwrap(src, p) =>
      val prefix = recp(p)
      recs(src).collect { case w if w.items.startsWith(prefix) =>
        PathValue(w.items.drop(prefix.length))
      }

    case Space.TailsUnion(src) =>
      recs(src).collect { case PathValue(_ :: tail) => PathValue(tail) }

    case Space.TailsIntersection(src) =>
      recs(src)
        .groupMapReduce { case PathValue(h :: _) => h } { case PathValue(_ :: t) => Set(PathValue(t)) }(_ union _)
        .values
        .reduce(_ intersect _)

    case Space.Iteration(src, symbol, rest, template) =>
      Set.from(for
        (h, tails) <- recs(src).groupMap(w => PathValue(w.items.head :: Nil))(w => PathValue(w.items.tail))
        out <- eval(template)(using pc.grown(Map(symbol -> h)),
                                      sc.grown(Map(rest -> SpaceValue(Set.from(tails)))),
                                      rc).paths
      yield out)

    case Space.GroundedPS(p, f) => f(PathValue(recp(p))).paths
    case Space.GroundedSS(s, f) => f(SpaceValue(recs(s))).paths
    case Space.Limit(i, x)      => recs(x).take(i)

  SpaceValue(recs(s))
```

The following subsections give the programming meaning of those cases.

### 4.1 Constants, variables, and set operations

`Empty`, `Singleton`, `Literal`, and `Mention` are the constants and variables of the language. `Union`, `Intersection`, and `Subtraction` are exactly the corresponding operations from the ring of sets. They are also the main guard mechanism. A predicate such as “the count is two” appears as an intersection with the singleton space `{"2"}`. A negative condition appears as subtraction.

### 4.2 Composition, wrap, and unwrap

Composition is lifted path concatenation:

```text
{"Foo"} · {"bar", "baz"} = {"Foo.bar", "Foo.baz"}
{"x", "y"} · {"a", "b"} = {"x.a", "x.b", "y.a", "y.b"}
```

`Wrap(src, p)` is composition by a singleton prefix. It tags a relation or places a result under a namespace:

```scala
"Parent" x S"family"("child")
```

`Unwrap(src, p)` removes a known prefix and discards paths that do not have it. If `family` contains `child.Bob.Tom`, then `S"family"("child")` contains `Bob.Tom`.

Together these operators give a compact encoding of records and tagged relations. A tag is just the first item of a path; selecting a tag is unwrapping; creating a tag is wrapping.

### 4.3 Restriction as prefix cylinders

`x <| prefixes` keeps the paths of `x` that start with at least one selected prefix. If `family` contains:

```text
female.Ann
female.Liz
male.Bob
parent.Bob.Ann
child.Bob.Tom
```

then:

```scala
S"family" <| s("male", "female")
```

returns the gender facts, while:

```scala
S"family" <| s("parent.Bob", "child.Bob")
```

returns the facts about Bob as either parent or child.

A prefix denotes a cylinder in the path trie: all paths below that prefix. Restriction is intersection with a finite union of such cylinders. In a trie implementation, this can be a guided descent rather than a scan; this is the practical reason to keep prefixes explicit in the surface language.

### 4.4 TailsUnion and TailsIntersection

`TailsUnion` removes one head item and unions the tails:

```text
TailsUnion({ Bob.Tom, Bob.Pam, Liz.Tom }) = { Tom, Pam }
```

Equivalently:

```text
TailsUnion(X) = { r | ∃a. a.r ∈ X }
```

This is existential projection over the first column of a path relation. It is used to ask “which children appear under these parents?”, “which graph nodes are reachable by one edge?”, and “which candidates are adjacent to the current frontier?”.

`TailsIntersection` performs the universal sibling query:

```text
TailsIntersection(X) = { r | ∀a ∈ heads(X). a.r ∈ X }
```

The test is a small commonality query:

```scala
test("intersection all") {
  val keys =
    (s("foo", "bar") x ss"e0") \/
    (s("foo", "cux", "baz") x ss"e1") \/
    (s("cux") x ss"e2")

  assert(eval(/\(keys <| s("foo", "bar"))).prettyLines == "e0")
}
```

The constructed space is:

```text
foo.e0   bar.e0
foo.e1   cux.e1   baz.e1
cux.e2
```

After restriction to the selected keys `foo` and `bar`, the remaining rows are:

```text
foo.e0
foo.e1
bar.e0
```

The tail set under `foo` is `{e0, e1}`. The tail set under `bar` is `{e0}`. Their intersection is `{e0}`. Thus `/\(keys <| selectedKeys)` means “what values are common to every selected key?”.

A production implementation should decide the empty-input identity for `TailsIntersection`. The prototype version assumes a nonempty input containing nonempty paths.

### 4.5 Iteration

`Iteration(src, symbol, rest, template)` is the structural eliminator for path spaces. It groups by first item, binds that item as a path variable, binds the set of tails as a space variable, and evaluates a template for each group.

If the source is:

```text
Tom.Bob
Tom.Liz
Bob.Ann
Bob.Pat
```

then:

```scala
S"source".iter("p", "children", template)
```

visits two groups:

```text
p = Tom, children = { Bob, Liz }
p = Bob, children = { Ann, Pat }
```

This is the operation that turns a flat path set into a trie traversal. Joins, projections, adjacency expansion, inverse indexes, and aggregations are all written by combining `iter`, `Wrap`, `Unwrap`, and the ring-of-sets operations.

### 4.6 Grounded functions

Some examples need scalar computation. Zippy isolates that need in grounded functions:

```scala
case Path.GroundedSP(space, f: SpaceValue => PathValue)
case Space.GroundedSS(space, f: SpaceValue => SpaceValue)
```

The Game of Life example uses grounded addition and cardinality. The graph example uses grounded sampling for deterministic pivot selection in one version of SCC. The important design point is that the data movement remains in the path algebra, while scalar decisions are isolated at explicit boundaries.

### 4.7 Routines and fixed points

A routine has path parameters, space parameters, and a space body:

```scala
case class Routine(name: RoutinePtr,
                   refs: Vector[PathRef],
                   mentions: Vector[SpaceMention],
                   body: Space)
```

Recursive routines express least fixed points. A helper used in the Datalog examples is:

```scala
def fixpoint(f: Space => Space) =
  routine(s"step${f.hashCode()}", Vector(), Vector("last"),
    S"last" \/ R"step${f.hashCode()}"(Vector(), Vector(S"last" \/ f(S"last")))
  )
```

Each recursive call receives the previous state plus whatever `f` can derive from it. When the derivation adds nothing new, the finite set has stabilized.

## 5. Laws as a compiler story

Zippy's equational laws are not merely pretty identities. They are a lowering strategy. They explain how to replace derived operations with smaller primitives, unroll constants, fold constant paths, and hoist loop-invariant work out of iterations.

### 5.1 TailsUnion lowers to iteration

`TailsUnion` can be defined using `Iteration`: group by head, ignore the head, and emit the rest space.

```scala
val TailsUnion_Iteration = subs(_: Space)(PartialFunction.empty, {
  case Space.TailsUnion(src) =>
    val name = SpaceMention("s" + src.hashCode().toHexString)
    Space.Iteration(src, PathRef("_"), name, Space.Mention(name))
})
```

This gives `TailsUnion` two lives. It is a convenient primitive for readers, but it can be lowered into the one-step trie iterator for a smaller backend.

### 5.2 Literals lower to singleton unions

A literal finite set is just a union of singleton paths:

```scala
val Literal_ConstantsUnion = subs(_: Space)(PartialFunction.empty, {
  case Space.Literal(SpaceValue(paths)) =>
    paths.map(p => Space.Singleton(Path.Constant(p))).reduce(Space.Union(_, _))
})
```

This is useful for a backend that wants all data introduced through the same constructor, or for proofs by structural induction over syntax.

### 5.3 Iteration over literals unrolls

If the source of an iteration is a known finite literal, the loop can be replaced by a union of instantiated templates:

```scala
val IterateLiteral_Union = subs(_: Space)(PartialFunction.empty, {
  case Space.Iteration(Space.Literal(SpaceValue(paths)), symbol, rest, template) =>
    paths.map(p =>
      subs(template)(
        spre = { case Space.Mention(`rest`) =>
          Space.Singleton(Path.Constant(PathValue(p.items.tail)))
        },
        ppre = { case Path.Deref(`symbol`) =>
          Path.Constant(PathValue(p.items.head :: Nil))
        }
      )
    ).reduce(Space.Union(_, _))
})
```

This is ordinary partial evaluation. It turns a data-known loop into a static expression.

### 5.4 Constant path concatenation folds

When both sides of a path concatenation are constants, concatenate them at compile time:

```scala
val Concat_Path = subs(_: Space)(ppost = {
  case Path.Concat(Path.Constant(PathValue(xs)), Path.Constant(PathValue(ys))) =>
    Path.Constant(PathValue(xs ++ ys))
})
```

This law is small but pervasive. Most surface syntax creates many little concatenations; folding them keeps the operation graph compact.

### 5.5 Loop-invariant union branches move out

If one side of a union inside an iteration mentions neither the bound head nor the rest space, it is loop-invariant and can be pulled out:

```scala
val IterUnion_Indep = subs(_: Space)(PartialFunction.empty, {
  case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if independent(lhs, symbol, rest) =>
    Space.Union(Space.Iteration(src, symbol, rest, rhs), lhs)

  case Space.Iteration(src, symbol, rest, Space.Union(lhs, rhs)) if independent(rhs, symbol, rest) =>
    Space.Union(Space.Iteration(src, symbol, rest, lhs), rhs)
})
```

The side condition is essential. A branch may move only when it does not read the iteration variables. This is classic loop-invariant code motion, expressed as a source-to-source law.

### 5.6 Prefixes move outside iterations

If an iterated template wraps every result with a prefix independent of the iteration variables, wrap after the iteration rather than inside it:

```scala
val Wrap_Iter = subs(_: Space)(PartialFunction.empty, {
  case Space.Iteration(src, symbol, rest, Space.Wrap(s, p)) if independent(Space.Singleton(p), symbol, rest) =>
    Space.Wrap(Space.Iteration(src, symbol, rest, s), p)
})
```

The singleton-concat form is the same optimization seen one level lower:

```scala
val ConcatSingleton_Iter = subs(_: Space)(PartialFunction.empty, {
  case Space.Iteration(src, symbol, rest, Space.Singleton(Path.Concat(p, q))) if independent(Space.Singleton(p), symbol, rest) =>
    Space.Wrap(Space.Iteration(src, symbol, rest, Space.Singleton(q)), p)
})
```

A backend that hoists common prefixes can allocate less and share more.

### 5.7 The identity iterator disappears

The canonical identity loop groups by head and immediately reconstructs the same paths from the bound head and tail space:

```scala
val Iter_Ident = subs(_: Space)(PartialFunction.empty, {
  case Space.Iteration(src, symbol, rest,
       Space.Wrap(Space.Mention(sm), Path.Deref(pr)))
       if symbol == pr && sm == rest => src
})
```

This law is a sanity check on `iter`: taking a trie apart and putting it back together should be the identity.

## 6. Case study: family queries

The family example demonstrates the relational fragment in its smallest form.

### 6.1 Data and indexing

The tree is:

```text
Tom × Pam
 |    \
Liz   Bob
      / \
   Ann   Pat
           |
          Jim
```

The initial database contains parent and gender facts:

```text
parent.Tom.Bob
parent.Pam.Bob
parent.Tom.Liz
parent.Bob.Ann
parent.Bob.Pat
parent.Pat.Jim
female.Pam
female.Liz
female.Pat
female.Ann
male.Tom
male.Bob
male.Jim
```

The indexed database adds child facts and person facts:

```scala
val indexed =
  S"ifamily" \/
  ("child" x S"ifamily"("parent").iter("x", "r",
    S"r".iter("y", "_", Singleton(P"y" x P"x")))) \/
  ("person" x S"ifamily"("female")) \/
  ("person" x S"ifamily"("male"))
```

The child index says: unwrap `parent`, group by parent `x`, group each rest by child `y`, and emit `child.y.x`. That is relation inversion using only unwrapping, iteration, and wrapping.

### 6.2 Selection and retagging

A parent relation is just the child relation under a new tag:

```scala
val parents = "Parent" x (S"family"("child") <| S"people")
```

The result contains paths such as:

```text
Parent.Bob.Tom
Parent.Pat.Bob
Parent.Bob.Pam
Parent.Liz.Tom
Parent.Ann.Bob
Parent.Jim.Pat
```

The prefix `Parent` is not special; it is simply a namespace for the answer.

### 6.3 Mothers

The mother query is a join between `child.person.parent` and `female.parent`:

```scala
val mothers =
  "Mother" x S"people".iter("person", "_",
    P"person" x
      (S"family"("child" x P"person") /\ S"family"("female"))
  )
```

For each person, unwrap the children relation at `child.person`. That yields the person's parents. Intersect those parents with the female set. Rewrap under `Mother.person`.

The result is:

```text
Mother.Jim.Pat
Mother.Bob.Pam
```

### 6.4 Sisters

The sister query finds people who share a parent with the current person, filters to females, and removes the person herself:

```scala
val sisters =
  "Sister" x S"people".iter("person", "_",
    P"person" x
      ((TailsUnion(S"family"("parent") <| S"family"("child" x P"person")) /\
        S"family"("female")) \
        Singleton(P"person"))
  )
```

`S"family"("child" x P"person")` gives the current person's parents. Restricting the `parent` relation by those parent names keeps all children of those parents. `TailsUnion` projects away the parent key, leaving the siblings. Intersection with `female` keeps sisters; subtraction removes the original person.

The result is:

```text
Sister.Ann.Pat
Sister.Pat.Ann
Sister.Bob.Liz
```

### 6.5 Aunts

The aunt query composes the same idea one level higher: find the person's parents, find the parents' siblings, remove direct parents, and filter to females.

```scala
val aunts =
  "Aunt" x S"people".iter("person", "_",
    P"person" x
      ((TailsUnion(
          S"family"("parent") <|
            TailsUnion(S"family"("child") <| S"family"("child" x P"person"))) \
        S"family"("child" x P"person")) /\
        S"family"("female"))
  )
```

The inner `TailsUnion` projects from the current person to the person's parents. The outer restriction looks up all children of those grandparents, giving the parent's siblings and the parent. Subtraction removes the direct parent. Intersection with `female` keeps the aunts.

The answer is:

```text
Aunt.Ann.Liz
Aunt.Jim.Ann
Aunt.Pat.Liz
```

The whole query is a path-space version of a relational join pipeline, but there is no separate join operator. The join emerges from prefix lookup and one-step tail projection.

## 7. Case study: strongly connected components

Graphs are a natural fit for path spaces. A directed graph is a set of `edge.source.target` paths.

```scala
val g3 = SpaceValue(
  "edge.a.b", "edge.a.d", "edge.d.c",
  "edge.x.y", "edge.y.x", "edge.x.z", "edge.z.y",
  "edge.s.t", "edge.t.u", "edge.u.v", "edge.v.w", "edge.w.s"
)
```

The graph above has a chain-like component around `a,b,c,d`, a cycle among `x,y,z`, and a cycle among `s,t,u,v,w`.

### 7.1 Transpose and node set

The forward edge relation is obtained by unwrapping `edge`:

```scala
val fwd = Literal(g3)("edge")
```

The transpose is a path-space inverse:

```scala
val bwd =
  fwd.iter("x", "r",
    S"r".iter("y", "_",
      Singleton(P"y" x P"x")))
```

For each source `x`, iterate through its targets `y`, and emit `y.x`. The node set is the union of sources and targets:

```scala
val nodes =
  fwd.iter("x", "_", Singleton(P"x")) \/
  bwd.iter("x", "_", Singleton(P"x"))
```

### 7.2 Reachability

Reachability is a fixed point over a frontier-like set `reach`:

```scala
val reachable_routine = routine("reachable", Vector(), Vector("edges", "nodemask", "reach"),
  S"reach" \/
  R"reachable"(Vector(), Vector(
    S"edges",
    S"nodemask",
    S"reach" \/
      (TailsUnion(S"edges" <| (S"reach" /\ S"nodemask")) /\ S"nodemask")
  ))
)
```

The step expression is the important part:

```scala
TailsUnion(S"edges" <| (S"reach" /\ S"nodemask")) /\ S"nodemask"
```

Read it as follows.

1. `S"reach" /\ S"nodemask"` keeps reached nodes that are still allowed.
2. `S"edges" <| ...` restricts the edge relation to edges whose source is in the current reached set.
3. `TailsUnion(...)` projects those edges to their targets.
4. `/\ S"nodemask"` keeps only allowed targets.

The recursive routine unions those newly reached targets into `reach` until no new nodes appear.

Examples:

```scala
R"reachable"(Vector(), Vector(fwd, nodes, Singleton("t")))
// { t, u, v, w }

R"reachable"(Vector(), Vector(fwd, nodes \ Singleton("v"), Singleton("s")))
// { s, t, u }

R"reachable"(Vector(), Vector(bwd, nodes, Singleton("c")))
// { c, d, a }
```

The second query masks out `v`, so reachability from `s` stops before crossing the removed node.

### 7.3 Divide-and-conquer SCC

The SCC routine chooses a pivot `v`, computes the forward and backward reachable sets from `v`, emits the component `forward ∩ backward`, then recurses on the three remaining regions:

```scala
val seedless_scc_routine = routine("seedless_scc", Vector(), Vector("fwd", "bwd", "nodes"),
  Limit(1, S"nodes").iter("v", "_", {
    val forward: Space = R"reachable"(Vector(), Vector(S"fwd", S"nodes", Singleton(P"v")))
    val backward: Space = R"reachable"(Vector(), Vector(S"bwd", S"nodes", Singleton(P"v")))

    (P"v" x ((forward /\ backward) \ Singleton(P"v"))) \/
      R"scc"(Vector(), Vector(S"fwd", S"bwd", forward \ backward)) \/
      R"scc"(Vector(), Vector(S"fwd", S"bwd", backward \ forward)) \/
      R"scc"(Vector(), Vector(S"fwd", S"bwd", (S"nodes" \ forward) \ backward))
  })
)
```

The component containing the pivot is `forward ∩ backward`: nodes reachable from the pivot and able to reach the pivot. The emitted paths have the pivot as a representative:

```scala
P"v" x ((forward /\ backward) \ Singleton(P"v"))
```

The pivot itself is removed from the tail to avoid a self-pair. The recursive calls cover the three disjoint regions outside the component:

```text
forward \ backward          reachable from pivot but unable to return
backward \ forward          able to reach pivot but not reachable from it
nodes \ forward \ backward  neither side
```

On the graph `g3`, a representative run produces paths such as:

```text
w.s
w.t
w.u
w.v
z.x
z.y
```

That is, `w` represents the five-node cycle `{s,t,u,v,w}` except itself, and `z` represents the three-node cycle `{x,y,z}` except itself. The acyclic `a,b,c,d` region contributes no nontrivial strongly connected pairs.

The algorithm is a good stress test for Zippy because it combines nearly every core idea: prefix restriction for adjacency lookup, `TailsUnion` for projection, intersection for mutual reachability, subtraction for partitioning, recursion for fixed points, and a small amount of choice for picking a pivot.

## 8. Case study: Conway's Game of Life

Game of Life is often presented as a grid update with nested loops and neighbor counts. In Zippy the grid is a sparse set of `Cell.x.y` paths, and the update is a space expression that generates only the local neighborhoods it needs.

The test starts with four living cells:

```scala
given SpaceContext = SpaceContextMap(Map(
  SpaceMention("Living") -> SpaceValue(
    "Cell.0.2",
    "Cell.1.1",
    "Cell.2.2",
    "Cell.3.3"),
  SpaceMention("Boundary") -> SpaceValue("0", "1", "2", "3", "4")
))
```

The comment draws them as:

```text
   0  1  2  3  4
0
1     x
2  x     x
3           x
4
```

After two steps this pattern evolves into the stable square:

```text
Cell.1.1
Cell.1.2
Cell.2.1
Cell.2.2
```

### 8.1 Grounded arithmetic and cardinality

Coordinates are path items, so arithmetic is implemented as a grounded space computation. The pure space expression first constructs symbolic paths headed by `+` or `+₂`; the grounded function interprets those requests.

```scala
extension (p: Path) def + (s: Space): Space =
  ("+" x p x s).arithmetic

extension (p: Path) def `+₂` (s: Space): Space =
  ("+₂" x p x s).arithmetic

extension (s: Space) def arithmetic: Space = Space.GroundedSS(s, s => SpaceValue(
  (for
    case PathValue(PathItem.Symbol("+") :: PathItem.Symbol(x) :: PathItem.Symbol(y) :: Nil) <- s.paths
  yield PathValue(PathItem.Symbol((x.toInt + y.toInt).toString) :: Nil)) union

  (for
    case PathValue(
      PathItem.Symbol("+₂") ::
      PathItem.Symbol(x0) :: PathItem.Symbol(x1) ::
      PathItem.Symbol(y0) :: PathItem.Symbol(y1) :: Nil
    ) <- s.paths
  yield PathValue(
    PathItem.Symbol((x0.toInt + y0.toInt).toString) ::
    PathItem.Symbol((x1.toInt + y1.toInt).toString) :: Nil))
))
```

Cardinality evaluates a space and returns the size as a one-item path:

```scala
def card(space: Space): Path =
  Path.GroundedSP(space, sv =>
    PathValue(List(PathItem.Symbol(sv.paths.size.toString))))
```

This lets a count guard remain a space expression. For example, `Singleton(card(xs)) /\ ss"2"` is nonempty exactly when `xs` has size two.

### 8.2 Neighbors

The neighbor routine creates the eight Moore neighbors of a coordinate:

```scala
case RoutinePtr("neigh") => R"neigh"(P"coord") := {
  val offsets = s("-1", "0", "1")
  (P"coord" `+₂` (offsets x offsets)) \ sP"coord"
}
```

`offsets x offsets` creates the nine delta pairs:

```text
-1.-1  -1.0  -1.1
 0.-1   0.0   0.1
 1.-1   1.0   1.1
```

Adding those pairs to the coordinate translates the square to the coordinate's neighborhood. Subtracting the singleton coordinate removes the center.

### 8.3 The step routine

The step routine is a direct expression of the two Life clauses:

```scala
case RoutinePtr("nextStep") => R"nextStep"(S"field") := "Cell" x ((

  // Survival with exactly two neighbors.
  S"field"("Cell").iter(P"x", S"ys",
    S"ys".iter(P"y", S"_",
      \/((Singleton(card(R"neigh"(P"x" x P"y") /\ S"field"("Cell"))) /\ ss"2") x
         Singleton(P"x" x P"y"))))

  \/

  // Births, and survival with exactly three neighbors.
  S"field"("Cell").iter(P"x", S"ys",
    S"ys".iter(P"y", S"_",
      R"neigh"(P"x" x P"y")))
    .iter(P"x", S"ys",
      S"ys".iter(P"y", S"_",
        \/((Singleton(card(R"neigh"(P"x" x P"y") /\ S"field"("Cell"))) /\ ss"3") x
           Singleton(P"x" x P"y"))))

): Space)
```

The outer `"Cell" x (...)` retags the resulting bare coordinates.

The first branch iterates over currently living cells. For each live coordinate `(x,y)`, it computes:

```scala
R"neigh"(P"x" x P"y") /\ S"field"("Cell")
```

That is the set of living neighbors of the current cell. If the cardinality is `2`, the branch emits the original coordinate.

The second branch first expands every living cell to its neighbors:

```scala
S"field"("Cell").iter(P"x", S"ys",
  S"ys".iter(P"y", S"_",
    R"neigh"(P"x" x P"y")))
```

This is the candidate set for births. It may also include currently living cells adjacent to another living cell. The following iteration checks each candidate and emits it if it has exactly three living neighbors. That covers births and also live cells that survive with three neighbors.

In set notation, the routine computes:

```text
Cell × (
  { c ∈ Living | |neigh(c) ∩ Living| = 2 }
  ∪
  { c ∈ neigh[Living] | |neigh(c) ∩ Living| = 3 }
)
```

The `Boundary` space is present in the context but not used by this particular routine. As written, the step is sparse and locally generated on an unbounded grid. A bounded version would restrict generated coordinates by `S"Boundary" x S"Boundary"`.

### 8.4 The two steps

The initial live cells have these live-neighbor counts:

```text
0.2 -> 1  dies
1.1 -> 2  survives
2.2 -> 2  survives
3.3 -> 1  dies
```

The dead coordinate `1.2` has exactly three live neighbors: `0.2`, `1.1`, and `2.2`. Therefore the first step is:

```text
Cell.1.1
Cell.1.2
Cell.2.2
```

The second step births `2.1`; the other three cells have the right counts to survive. The assertion is:

```scala
assert(eval(R"nextStep"(R"nextStep"(S"Living"))).prettyLines ==
  "Cell.1.1\nCell.1.2\nCell.2.1\nCell.2.2")
```

Game of Life also shows where the algebraic boundary lies. Union, intersection, subtraction, product, unwrapping, wrapping, and iteration handle all data movement. Addition and cardinality are grounded scalar observations. Since Life is not monotone—adding a live cell can kill another cell—those scalar observations are not an accident; they are the precise place where the program leaves pure set growth.

## 9. Case study: Datalog and semi-naive evaluation

Zippy can express Datalog-style joins by compiling atom patterns into nested unifications over path spaces. The helper used in the tests is `MQT`, a multi-pattern query that emits a template when all patterns match with a consistent set of variable bindings:

```scala
def MQT(src: Space,
        ps: List[PathValue],
        t: PathValue,
        r: Option[Space] = None,
        bound: Map[String, PathRef] = Map.empty): Space = ps match
  case p :: ps =>
    U(src, p, (s, b) => MQT(src, ps, t, Some(s), b), bound)
  case Nil =>
    W(r.get, t, bound)
```

A transitive-closure program is two Datalog rules:

```text
path(x, y) :- edge(x, y)
path(x, z) :- path(x, y), path(y, z)
```

The naive fixed point is almost literal:

```scala
test("trans naive") {
  val r = fixpoint(last =>
    MQT(last, List("edge.$x.$y"), "path.$x.$y") \/
    MQT(last, List("path.$x.$y", "path.$y.$z"), "path.$x.$z"))

  val data = SpaceValue("edge.a.b", "edge.b.c", "edge.c.d", "edge.d.e")

  assert(eval(r.name(Literal(data))("path"))(using rc = { case r.name => r }) ==
    SpaceValue("a.b", "a.c", "a.d", "a.e", "b.c", "b.d", "b.e", "c.d", "c.e", "d.e"))
}
```

The result is the strict reachability relation over the chain. The problem is repeated work: every round reconsiders joins among old path facts.

Semi-naive evaluation splits the state into accumulated facts and the most recent frontier:

```text
complete.edge.x.y      base edge facts
complete.path.x.y      path facts already absorbed
delta.path.x.y         path facts discovered last round
```

The semi-naive routine is:

```scala
test("trans semi-naive") {
  val r = fixpoint(last =>
    ("complete" x (last("complete") \/ last("delta"))) \/
    ("delta.path" x (
      (MQT(last, List("complete.edge.$x.$y"), "$x.$y") \/
       MQT(last, List("complete.path.$x.$y", "delta.path.$y.$z"), "$x.$z") \/
       MQT(last, List("delta.path.$x.$y", "complete.path.$y.$z"), "$x.$z") \/
       MQT(last, List("delta.path.$x.$y", "delta.path.$y.$z"), "$x.$z"))
        \ (last("complete.path") \/ last("delta.path")))))

  val data = s("edge.a.b", "edge.b.c", "edge.c.d", "edge.d.e")

  val initial =
    ("delta" x (
      MQT(data, List("edge.$x.$y"), "path.$x.$y") \/
      MQT(data, List("path.$x.$y", "path.$y.$z"), "path.$x.$z"))) \/
    ("complete" x data)

  assert(eval(r.name(initial)("complete.path"))(using rc = { case r.name => r }) ==
    SpaceValue("a.b", "a.c", "a.d", "a.e", "b.c", "b.d", "b.e", "c.d", "c.e", "d.e"))
}
```

The first branch promotes the old frontier into the accumulated set:

```scala
"complete" x (last("complete") \/ last("delta"))
```

The second branch computes only the next frontier. Expanding the recursive rule over `path = complete.path ∪ delta.path` gives four joins:

```text
complete ⋈ complete
complete ⋈ delta
delta    ⋈ complete
delta    ⋈ delta
```

The old-old join can be skipped because it was available in a previous round. The other three joins are exactly the three recursive terms in the code. The final subtraction:

```scala
\ (last("complete.path") \/ last("delta.path"))
```

keeps `delta` as a true frontier rather than a duplicate of the whole closure.

On the chain graph, the frontier evolves by path length: length-one paths, then length-two paths, then length-three paths, then length-four paths, then empty. The accumulated `complete.path` space is the final closure.

## 10. Case study: fuzzy temperature search with restriction

The temperature example shows that prefix restriction is not only relational selection; it is also a trie-indexed range search.

The database is a sparse world slice. A five-bit binary prefix encodes a temperature bucket from `0` to `31`, and the last item is the qualitative value `H`, `M`, or `C`.

```scala
val temperature = SpaceContextMap(Map(SpaceMention("world_slice") -> SpaceValue(
  "0.0.0.1.1.H",
  "0.0.1.0.0.M",
  "0.0.1.1.0.M",
  "0.1.0.0.0.M",
  "0.1.0.0.1.M",
  "0.1.0.1.0.C",
  "0.1.1.1.0.C",
  "0.1.1.1.1.M",
  "1.0.0.1.0.H",
  "1.0.1.0.0.M",
  "1.0.1.1.0.M",
  "1.0.1.1.1.H",
  "1.1.0.1.1.H",
  "1.1.1.0.0.M",
  "1.1.1.0.1.C",
  "1.1.1.1.1.H"
)))
```

The interval encoder returns a minimal set of trie prefixes covering an integer interval:

```scala
def about(point: Int, surrounding: Int): SpaceValue =
  interval(point - surrounding, point + surrounding)

def interval(start: Int, end: Int, height: Int = 5, trail: Vector[Boolean] = Vector()): SpaceValue =
  val lowest = trail.padTo(height, false).reverseIterator.zipWithIndex.foldLeft(0) {
    case (k, (b, i)) => if b then k + (1 << i) else k
  }
  val middle = trail.appended(true).padTo(height, false).reverseIterator.zipWithIndex.foldLeft(0) {
    case (k, (b, i)) => if b then k + (1 << i) else k
  }
  val highest = trail.padTo(height, true).reverseIterator.zipWithIndex.foldLeft(0) {
    case (k, (b, i)) => if b then k + (1 << i) else k
  }

  if start == lowest && end == highest then
    SpaceValue(trail.map(if _ then "1" else "0").mkString("."))
  else if start < middle && end >= middle then
    SpaceValue(interval(start, middle - 1, height, trail.appended(false)).paths union
               interval(middle, end, height, trail.appended(true)).paths)
  else if end < middle then
    interval(start, end, height, trail.appended(false))
  else
    interval(start, end, height, trail.appended(true))
```

The query itself is simply restriction:

```scala
S"world_slice" <| Space.Literal(interval(18, 21))
```

The tests exercise several ranges:

```scala
assert(eval(S"world_slice" <| Space.Literal(about(1, 1))) ==
  SpaceValue())

assert(eval(S"world_slice" <| Space.Literal(interval(3, 4))) ==
  SpaceValue("0.0.0.1.1.H", "0.0.1.0.0.M"))

assert(eval(S"world_slice" <| Space.Literal(about(12, 3))) ==
  SpaceValue("0.1.0.0.1.M", "0.1.0.1.0.C", "0.1.1.1.0.C", "0.1.1.1.1.M"))

assert(eval(S"world_slice" <| Space.Literal(interval(18, 21))) ==
  SpaceValue("1.0.0.1.0.H", "1.0.1.0.0.M"))

assert(eval(S"world_slice" <| Space.Literal(interval(16, 31))) ==
  SpaceValue(
    "1.0.0.1.0.H", "1.0.1.0.0.M", "1.0.1.1.0.M", "1.0.1.1.1.H",
    "1.1.0.1.1.H", "1.1.1.0.0.M", "1.1.1.0.1.C", "1.1.1.1.1.H"))
```

The important point is that the interval function returns prefixes, not final records. Restriction then interprets those prefixes as cylinders. This is the same operation used for family selection and graph adjacency lookup, but here it acts like a fuzzy range query over a binary trie.

## 11. What the examples show

Across the examples, a small set of patterns repeats.

**Tags are prefixes.** `Cell`, `edge`, `child`, `female`, `complete`, and `delta` are all ordinary path items. Namespaces are data.

**Selection is prefix restriction.** The same `<|` operator selects gender facts, follows graph edges from a reached set, searches an interval cover, and filters the database to a key set.

**Projection is tails.** `TailsUnion` is existential projection over the first path item. `TailsIntersection` is universal projection over selected heads.

**Joins are structured iteration.** `iter` turns a flat path set into head groups. Nested iterations produce the same effect as joining on columns, but the columns are positions in a path.

**Fixed points are finite growth.** Reachability, SCC, and Datalog closure all work by recursive unioning into a finite space until no new paths appear.

**Grounded code is explicit.** Arithmetic, cardinality, and sampling are outside the pure ring-of-path-sets fragment, but they are visible at the boundary rather than hidden inside the evaluator.

## 12. Conclusion

Zippy's core is small enough to explain as a functional pearl: represent structured data as finite sets of paths, then program with the ring of sets and path concatenation. This representation makes relations, records, tries, sparse arrays, graphs, and tagged databases look the same. The consequence is a surprisingly expressive algebra: prefix restriction selects, unwrapping indexes, tails project, iteration groups, wrapping retags, and recursion computes fixed points.

The quantale analogy is useful but should be kept honest. The implemented spaces are finite, and the language relies on Boolean set operations and explicit grounded computations. The better concrete picture is a ring of finite path sets equipped with idempotent-semiring multiplication and trie-aware modalities. The semiring part explains graph paths and fixed points; the database part explains joins, nesting, and universal commonality queries; the automata part explains restriction and iteration as prefix-cylinder intersection and single-letter quotients. That picture is strong enough to organize both the semantics and the optimizer laws, while remaining close to executable Scala.

The examples suggest a practical direction. A production Zippy backend would store spaces as tries, compile restriction to guided traversal, lower `TailsUnion` to iteration when convenient, hoist invariant prefixes, unroll literals, and choose incremental frontiers for recursive rules. The surface language would remain a small algebra of path spaces; the implementation would exploit the structure that the notation already reveals.

## References

- Serge Abiteboul and Catriel Beeri, “[The Power of Languages for the Manipulation of Complex Values](https://doi.org/10.1007/BF01354881),” *VLDB Journal*, 1995.
- Serge Abiteboul, Richard Hull, and Victor Vianu, [*Foundations of Databases*](https://webdam.inria.fr/Alice/), Addison-Wesley, 1995.
- Janusz Brzozowski, “[Derivatives of Regular Expressions](https://doi.org/10.1145/321239.321249),” *Journal of the ACM*, 1964.
- Dexter Kozen, “[On Kleene Algebras and Closed Semirings](https://www.cs.cornell.edu/~kozen/Papers/kacs.pdf),” 1990.
- Mehryar Mohri, “[Semiring Frameworks and Algorithms for Shortest-Distance Problems](https://cs.nyu.edu/~mohri/pub/jalc.pdf),” *Journal of Automata, Languages and Combinatorics*, 2002.
- “[Ring of sets](https://en.wikipedia.org/wiki/Ring_of_sets),” Wikipedia.
