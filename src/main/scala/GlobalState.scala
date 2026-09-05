package morkl

/** ==================================================================================================
 *  EVERY PIECE OF PROCESS-WIDE MUTABLE STATE, IN ONE PLACE, SO A COUNTED COLUMN CAN BE INTERROGATED
 *  INSTEAD OF GUESSED AT.
 *
 *  ==WHAT WENT WRONG==
 *  `sbt test` and `testOnly morkl.SpatialScaleCheck` disagreed on a counted column: the same tree,
 *  the same assertion, PASSING in one invocation and FAILING-AND-UNDIAGNOSED in the other (recorded
 *  in build.log, round 7).  The diagnosis on offer was "interner id drift" — the ladder's alphabet
 *  gets different [[Interner]] ids depending on which suites ran first, and something downstream is
 *  sensitive to the id VALUES rather than only to their distinctness.  That is a plausible story and
 *  it was never checked, because nothing in the process could report the state the story is about.
 *
 *  ==WHAT THIS IS==
 *  A read-only probe over every table in this process whose contents SURVIVE A TEST and are
 *  APPEND-ONLY FOR THE LIFE OF THE JVM.  Two things use it:
 *
 *   1. `CalibrationProbe` (test scope) prints it on entry to and exit from each measuring suite, as a
 *      `CALIBRATION:` line, so it lands in the same output stream as the numbers it might explain;
 *   2. `scripts/check_determinism.sh` runs one gate suite twice and diffs every `CALIBRATION:` line.
 *
 *  ==AND WHY IT IS AN ENUMERATION RATHER THAN TWO FIELDS==
 *  Because the point is FALSIFICATION.  If two runs' probes are IDENTICAL and their counted columns
 *  still differ, the id-drift hypothesis is refuted — but only if the probe covers the whole
 *  hypothesis, i.e. every process-wide table, not just the two that were suspected.  A probe over a
 *  subset can only ever weakly confirm.  So the list below is meant to be TOTAL over the `object`s
 *  of `src/main/scala` and their file-scope `private val` caches, and a new process-wide table is
 *  expected to be added here in the same commit that introduces it.  (Scala nests block comments, so
 *  the grep that enumerates them cannot be quoted here: it is `object` declarations plus
 *  `ConcurrentHashMap` / `mutable.HashMap` / `ArrayBuffer` fields held by one.)
 *
 *  Nothing here mutates anything, and every accessor is O(1) (a `size` on a map or an array-backed
 *  buffer), so a probe is free to print on every suite.
 *  ================================================================================================== */
object GlobalState:

  /** one process-wide table: its probe name, the file that owns it, and its current occupancy */
  final case class Table(name: String, owner: String, read: () => Long):
    def size: Long = read()

  /** THE TOTAL LIST.  Order is fixed so two probes are line-comparable. */
  val tables: Vector[Table] = Vector(
    // The two the plan names, and the two whose ids everything downstream is keyed by.
    Table("Interner.size", "IntTrie.scala", () => Interner.size.toLong),
    // THE CERTIFICATE ARENA  — and it is the one table here that CANNOT change an
    // answer, by construction rather than by argument: `Cert`'s `equals`/`hashCode` are structural
    // and the arena only hands back a canonical instance, so `Cert.reset()` mid-run changes nothing.
    // That is exactly what the `HeadAtoms` id table it replaces could not say, and why the ids had to
    // go: a `Shape` carrying an atom id was meaningless without the table, and shapes outlive their
    // analysis.  It is still probed, because it can change TIMING and this suite set has wall-clock
    // budgets as well as counted ones.
    // `Cert.constructed` AND NOT `Cert.arenaSize`.  The arena is WEAK-keyed, so its occupancy depends
    // on when the collector ran and it is not a determinism signal at all —
    // `scripts/check_determinism.sh` reported it as a differing probe line across two runs of
    // `SpatialEventsCheck` (28 against 41), which is the gate working.  The construction counter is
    // deterministic for a deterministic run and answers what the probe is for: how much certificate
    // work the suite did.
    Table("Cert.constructed", "SpatialCert.scala", () => Cert.constructed),
    // By-ref literal ids.  These appear in EMITTED TEXT (`lit#7`), so unlike a memo they are
    // observable in artifacts, which makes them a candidate for a golden-file diff as well.
    Table("LiteralStore.size", "MORKL.scala", () => LiteralStore.size.toLong),
    // The trie-side decode memos, all three append-only for the life of the JVM.
    Table("iLiteralCache.size", "IntTrie.scala", () => iCacheSizes._1.toLong),
    Table("iLiteralStrCache.size", "IntTrie.scala", () => iCacheSizes._2.toLong),
    Table("iConstStrCache.size", "IntTrie.scala", () => iCacheSizes._3.toLong),
  )

  /** THE TWO ARMED FLAGS, reported separately because they are not tables: they are booleans that a
   *  leaked counting region would leave `true`, which would make every subsequent hook in the
   *  process record events into nothing (`armed` true, `active` null) — a real cost, and a real
   *  candidate for "the same code counted differently". */
  def flags: Vector[(String, Boolean)] = Vector(
    "EffortSink.armed" -> EffortSink.armed,
    "ZipperDemandSink.armed" -> ZipperDemandSink.armed,
  )

  /** One line, stable field order, `k=v` pairs — diffable by `scripts/check_determinism.sh`. */
  def probe: String =
    (tables.map(t => s"${t.name}=${t.size}") ++ flags.map((n, b) => s"$n=$b")).mkString(" ")

  /** The probe, labelled, as a `CALIBRATION:` line so it shares the stream with the numbers it
   *  exists to explain.  `phase` is ENTRY or EXIT. */
  def calibrationLine(suite: String, phase: String): String =
    s"CALIBRATION: PROBE $phase $suite $probe"
end GlobalState
