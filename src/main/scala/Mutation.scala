package morkl

/** ==============================================================================================
 *  MUTATION SWITCHES: weaken one property of the analysis on purpose, so a gate can be
 *  shown to FAIL exactly when that property is weakened.
 *
 *  A gate that only ever passes proves nothing about what it guards.  Each switch below removes one
 *  thing the resource analysis is supposed to do; `MutationGates` turns each on, runs the assertion
 *  that is supposed to catch it, and requires the assertion to fail — and to pass again with the switch
 *  off.  The switches are consulted at exactly one site each (named beside them) and are never set
 *  outside a test; `active` is a plain volatile set so a suite can flip them without any plumbing.
 *
 *   drop-alias            the input's object identity is forgotten (`Alias.Fresh`): same-object facts,
 *                         pointer-preserving results and the reference `same` case are lost
 *                         — site: CostSem's `Mention` rule
 *   reverse-range         `Range(x, lo, hi)` is priced and abstracted with its window reversed
 *                         — site: CostSem's `Range` rule
 *   erase-calls           every `Call` is answered by ⊤ (no summary, no stationary recursion)
 *                         — site: CostSem's `call`
 *   optimistic-lower      every reported lower bound is raised to its upper bound
 *                         — site: `CostSem.analyze` / `analyzeGraph`, on the final report
 *   no-widening-record    a widening happens but is not written to the certificate
 *                         — site: `Domain.record`
 *  ============================================================================================== */
object Mutation:
  @volatile private var flags: Set[String] = Set.empty
  val all: Vector[String] = Vector("drop-alias", "reverse-range", "erase-calls", "optimistic-lower", "no-widening-record")
  def active(name: String): Boolean = flags.nonEmpty && flags(name)
  def activeNames: Set[String] = flags
  /** run `body` with `name` switched on; always switched off afterwards */
  def withActive[A](name: String)(body: => A): A =
    require(all.contains(name), s"unknown mutation $name")
    flags += name
    try body finally flags -= name

  /** the reported bounds under `optimistic-lower`: every lower endpoint raised to the upper one */
  def bounds(b: EventBounds): EventBounds =
    if !active("optimistic-lower") then b else EventBounds(b.m.view.mapValues(i => Ivl(i.hi, i.hi)).toMap)
