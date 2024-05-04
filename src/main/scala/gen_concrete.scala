package genc

trait EM[V]
trait Path[A]

trait A[V]:
  type X
  type E
  type G
  enum Term:
    case Grounded(g: G)
    case Rec(x: X)
    case Value(v: V)
    case Apply(x: X, ev: E, a: Term)
    case Pair(l: Term, r: Term)

trait Base:
  type T
  type EMT <: EM[T]
  enum BaseTerm:
    case Empty()
    case Store(em: EMT)
    case GBool(b: Boolean)
    case GInt(i: Int)
    case GString(i: String)

trait RZAM[V] extends A[V], Base:
  type X <: Path[EMT]
  type E = Term
  type T <: Term
  type G = BaseTerm


object Example:
  opaque type AccessCount = Int

  object ACZRAM extends RZAM[AccessCount]:
    case class CEMR(m: Map[ACZRAM.Term, ACZRAM.Term]) extends EM[ACZRAM.Term]
    enum EMPathWord:
      case G, R, V, A, P // TODO
    case class EMPath(p: List[EMPathWord]) extends Path[CEMR]

    override type T = ACZRAM.Term
    type EMT = CEMR
    type X = EMPath

  import ACZRAM.Term.*
  import ACZRAM.BaseTerm.*
  import ACZRAM.EMPath
  import ACZRAM.EMPathWord.*

  val g42 = Grounded(GInt(42))
  val v = Value(1)
  val app = Apply(EMPath(G::Nil), g42, v)
