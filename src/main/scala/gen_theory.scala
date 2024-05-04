package gen

trait EM[A]
type Path[A] = A

trait A[X, E[_], V, G]:
  case class Grounded(g: G)
  case class Rec(x: X)
  case class Value(v: V)
  case class Red(x: X, ev: E[V], a: A[X,E,V,G])
  case class Green(x: X, ev: E[V], a: A[X,E,V,G])
  case class Pair(l: A[X,E,V,G], r: A[X,E,V,G])

trait Base[T]:
  case class Empty()
  case class Store(em: EM[T])
  case class GBool(b: Boolean)
  case class GInt(i: Int)
  case class GString(i: String)

trait ZAM[T, V] extends A[
  Path[EM[T]],
  [v] =>> ZAM[T, v], // is this a good fix?
  V,
  Base[T]]

trait RZAM[V] extends A[
  Path[EM[RZAM[V]]],
  RZAM,
  V,
  Base[RZAM[V]]]
