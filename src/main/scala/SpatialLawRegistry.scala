package morkl

enum SpatialLawVerdict:
  case Proved, Refuted

case class SpatialLawCertificate(
  law: String,
  artifact: String,
  verdict: SpatialLawVerdict,
  counterexample: Option[String] = None,
)

/** Auditable law -> certificate -> status index. Positive entries point to
  * unbounded FOL obligations; negative entries carry committed finite
  * witnesses and matching CounterSatisfiable obligations. */
object SpatialLawRegistry:
  val certificates: Vector[SpatialLawCertificate] = Vector(
    SpatialLawCertificate("abstract join is least upper bound",
      "proofs/vampire/generated/spatial_join_least_fo.p", SpatialLawVerdict.Proved),
    SpatialLawCertificate("abstract meet is greatest lower bound",
      "proofs/vampire/generated/spatial_meet_interval_greatest_fo.p", SpatialLawVerdict.Proved),
    SpatialLawCertificate("reduced product preserves gamma",
      "proofs/vampire/generated/spatial_reduction_gamma_idempotent_fo.p", SpatialLawVerdict.Proved),
    SpatialLawCertificate("difference distributes over union in its right argument",
      "proofs/generated/bad_diff_right_union_distribution_generated_negative_control.smt2", SpatialLawVerdict.Refuted,
      Some("A={a}, B={a}, C={} gives {} != {a}")),
    SpatialLawCertificate("restriction is commutative",
      "proofs/generated/bad_restriction_commutative_generated_negative_control.smt2", SpatialLawVerdict.Refuted,
      Some("A={a.b}, B={a} gives A <| B={a.b}, B <| A={}")),
  )

  def apply(law: String): Option[SpatialLawCertificate] = certificates.find(_.law == law)
