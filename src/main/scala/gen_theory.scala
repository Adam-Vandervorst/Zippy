package gen

trait EM[A]
trait Path[A]

trait A[V]:
  type X
  type E[_]
  type G
  enum AL:
    case Grounded(g: G)
    case Rec(x: X)
    case Value(v: V)
    case Red(x: X, ev: E[V], a: AL)
    case Green(x: X, ev: E[V], a: AL)
    case Pair(l: AL, r: AL)

enum Base[T]:
  case Empty()
  case Store(em: EM[T])
  case GBool(b: Boolean)
  case GInt(i: Int)
  case GString(i: String)

trait RZAM[V] extends A[V]:
  type X = Path[EM[RZAM[V]]]
  type E[v] = RZAM[v]
  type G = Base[RZAM[V]]
