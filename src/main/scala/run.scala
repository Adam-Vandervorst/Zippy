import scala.annotation.targetName
import compiletime.ops.int


sealed trait Poly
sealed trait -->[X <: Poly, Y <: Poly] extends Poly
sealed trait +[X <: Poly, Y <: Poly] extends Poly
sealed trait *[X <: Poly, Y <: Poly] extends Poly
sealed trait Const[I <: Int & Singleton] extends Poly
sealed trait Var[X] extends Poly

// In comparison, + and * should me commutative, slows down proof search of course
//given [X <: Poly, Y <: Poly, Z](using Z =:= (X + Y)): (Z =:= (Y + X)) = <:<.asInstanceOf
//given [X <: Poly, Y <: Poly, Z](using Z =:= (X * Y)): (Z =:= (Y * X)) = <:<.asInstanceOf


type Hinze[X <: Poly] <: Poly = X match
  case (k1 + k2) --> v => Hinze[(k1 --> v)] * Hinze[(k2 --> v)]
  case (k1 * k2) --> v => k1 --> Hinze[(k2 --> v)]
  // not sure how hinze generalizes to these other cases, defining them as the identity for now
  case x --> y => x --> y
  case x + y => x + y
  case x * y => x * y
  case Const[x] => Const[x]
  case Var[x] => Var[x]

@targetName("PartialDerivative")
type ∂[V, X <: Poly] <: Poly = X match
  case Var[V] => Const[1]
  case Var[_] => Const[0]
  case Const[_] => Const[0]
  case x + y => ∂[V, x] + ∂[V, y]
  case x * y => x * ∂[V, y] + y * ∂[V, x]

// Simplifying polynomial expression, nothing rigorous here
type SimplifyStep[X <: Poly] <: Poly = X match
  case Const[x] + Const[y] => Const[int.+[x, y]]
  case Const[x] * Const[y] => Const[int.*[x, y]]
  case Const[1] * y => y
  case x * Const[1] => x
  case Const[0] * _ => Const[0]
  case _ * Const[0] => Const[0]
  case Const[0] + y => y
  case x + Const[0] => x
  case x + y => SimplifyStep[x] + SimplifyStep[y]
  case x * y => SimplifyStep[x] * SimplifyStep[y]
  case x --> y => SimplifyStep[x] --> SimplifyStep[y]
  case _ => X


// Applying a type-level function N times
type FN[F[_], N <: Int & Singleton] = [X] =>> FNinner[F, N, X]

type FNinner[F[_], N <: Int & Singleton, R] = N match
  case 0 => R
  case int.S[n] => FNinner[F, n, F[R]]

type Simplify[X <: Poly] = FN[[V] =>> SimplifyStep[V & Poly], 10][X]

// Two step encoding of Lambda, first providing the var, than the recursive type
trait Lambda[V <: Poly]:
  type Abs[X <: Poly] = V * X
  type App[X <: Poly] = X * X
  type L[X <: Poly] = V + Abs[X] + App[X]

// The value type of the ExprMap, for Unit this is a set, for Int this is a multiset
type Value = Var[Unit]
// Type of variable in a theory like Lambda, may  as well be Int
type Name = Var[String]

trait Fix[F[_]]:
  type unfix = F[Fix[F]]

object Proofs:
  summon[Hinze[(Name + Name) --> Value] =:=
    ((Name --> Value) * (Name --> Value))]
  type ltheory = Fix[[x] =>> Lambda[Name]#L[Var[x]]]
  summon[Hinze[ltheory#unfix --> Value] =:=
    (Name --> Value) * (Name --> (Var[ltheory] --> Value)) * (Var[ltheory] --> (Var[ltheory] --> Value))]

  summon[∂["X", Var["X"]] =:= Const[1]]
  summon[∂["Y", Var["X"]] =:= Const[0]]
  type p1 = Var["X"] * (Const[5] + Var["Y"])
  summon[Simplify[∂["X", p1]] =:= (Const[5] + Var["Y"])]
  summon[Simplify[∂["Y", p1]] =:= Var["X"]]
