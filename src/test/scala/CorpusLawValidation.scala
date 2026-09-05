package morkl

import munit.FunSuite

/** THE LAW-PIPELINE CORPUS GATE: apply the FULL optimiser law set (SC.reduce — every certified
 *  source law, including the semijoin, push/merge, hoisting, raffination/restriction and keyed
 *  iteration-merge families) to every fuzzed corpus program, and validate the reduced program
 *  against `eval` of the original on many random input environments.  This is the
 *  programs × inputs gate for NEW LAWS: a law that is wrong for any corpus shape fails here.
 *  Tunables: -Dlawvalid.m (envs per program, default 100), -Dlawvalid.progs (default all). */
class CorpusLawValidation extends FunSuite:
  import Space.*
  override val munitTimeout = scala.concurrent.duration.Duration(30, "min")

  val maxS = 3; val maxP = 3
  val sNames = (0 until maxS).map(i => SpaceMention("s" + i)).toVector
  val pNames = (0 until maxP).map(j => PathRef("p" + j)).toVector
  val A = SpaceFuzzer.alphabet

  def randPath(rng: java.util.Random): PathValue = PathValue(List.fill(1 + rng.nextInt(2))(A(rng.nextInt(A.length))))
  def smallTrie(rng: java.util.Random): SpaceValue = SpaceValue((0 until (1 + rng.nextInt(6))).map(_ => randPath(rng)).toSet)

  test("law pipeline over the corpus: SC.reduce(prog) == prog on random inputs".tag(SlowTag.Slow)) {
    val M = sys.props.get("lawvalid.m").map(_.toInt).getOrElse(100)
    val progLimit = sys.props.get("lawvalid.progs").map(_.toInt).getOrElse(Int.MaxValue)
    val recs = Corpus.load(progLimit)

    val rng = new java.util.Random(133742)
    final case class Env(sv: Array[SpaceValue], pv: Array[PathValue])
    val envs: Array[Env] = Array.fill(M)(Env(Array.fill(maxS)(smallTrie(rng)), Array.fill(maxP)(randPath(rng))))
    val noRc: PartialFunction[RoutinePtr, Routine] = PartialFunction.empty

    var checks = 0L; var changed = 0; var reduceMs = 0.0
    val t0 = System.nanoTime()
    for r <- recs do
      val c0 = System.nanoTime()
      val red = SC.reduce(r.prog)
      reduceMs += (System.nanoTime() - c0) / 1e6
      if red != r.prog then changed += 1
      var k = 0
      while k < M do
        val e = envs(k)
        val pc: PathContext = PathContextMap((0 until r.nPath).map(j => pNames(j) -> e.pv(j)).toMap)
        val sc = SpaceContextMap((0 until r.nSpace).map(i => sNames(i) -> e.sv(i)).toMap)
        val ref = eval(r.prog)(using pc, sc, noRc)
        val got = eval(red)(using pc, sc, noRc)
        assertEquals(got, ref, s"LAW BUG: reduced program disagrees\nprog: ${r.prog.show}\nred:  ${red.show}")
        checks += 1
        k += 1
    val secs = (System.nanoTime() - t0) / 1e9
    println(f"CORPUS-LAW: ${recs.size} programs x $M envs = $checks%d checks, all agree; " +
      f"laws changed $changed/${recs.size} programs; reduce total ${reduceMs / 1000}%.1fs; wall $secs%.1fs")
  }
end CorpusLawValidation
