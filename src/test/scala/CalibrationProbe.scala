package morkl

/** ==================================================================================================
 *  THE PROBE THAT MAKES A MEASURING SUITE'S JVM STATE VISIBLE.
 *
 *  Mixed into every suite that COUNTS or TIMES anything and is therefore sensitive to the state of
 *  the process it runs in.  It prints [[GlobalState.probe]] as a `CALIBRATION:` line on entry and at
 *  JVM exit, which does two things:
 *
 *   - `scripts/check_determinism.sh` runs one gate suite twice and diffs every `CALIBRATION:` line,
 *     so ENTRY tells it whether the two runs started from the same JVM state at all.  With
 *     `Test / testGrouping` (build.sbt) an ENTRY probe reads all zeros and both `armed` flags false,
 *     because the suite owns its JVM; a non-zero ENTRY probe means the grouping regressed and the
 *     counted columns are order-dependent again.
 *   - the ENTRY/EXIT pair says how much of the process-wide state THIS suite minted, which is the
 *     number a future "the counts moved" investigation needs and which nothing recorded before.
 *
 *  ==WHY EXIT IS A SHUTDOWN HOOK AND NOT `afterAll`==
 *  MEASURED: an `override def afterAll()` prints under `sbt test` and NOT under
 *  `org.junit.runner.JUnitCore`, which is what `target/test-runtime/run-suite.sh` and therefore every
 *  gate run uses.  `MUnitRunner.run` drives `runAfterAll` through a `Future`, and `JUnitCore.main`
 *  calls `System.exit` on the result — so the EXIT line was dropped in exactly the harness the
 *  determinism gate runs in.  A probe line that appears in one harness and silently vanishes in the
 *  other is worse than no probe line at all: the gate would be diffing a field that is sometimes
 *  absent.  A shutdown hook fires on normal exit AND on `System.exit`, in both harnesses, exactly
 *  once per suite JVM.
 *
 *  ==IT IS DELIBERATELY NOT AN ASSERTION==
 *  build.log's diagnosis of the order-dependent counted column was "interner id drift", never
 *  checked.  A probe that FAILED on a non-empty interner would encode that unchecked diagnosis as a
 *  requirement; a probe that PRINTS lets the determinism gate decide, and lets an identical probe
 *  beside differing counts refute the hypothesis outright — which is the outcome the plan asks to be
 *  recorded rather than "fixed". */
trait CalibrationProbe extends munit.Suite:

  /** the name the probe lines are labelled with; the simple class name is what a `diff` reads best */
  private def probeSuiteName: String = getClass.getSimpleName.stripSuffix("$")

  override def beforeAll(): Unit =
    super.beforeAll()
    println(GlobalState.calibrationLine(probeSuiteName, "ENTRY"))
    val name = probeSuiteName
    Runtime.getRuntime.addShutdownHook(new Thread(() => {
      println(GlobalState.calibrationLine(name, "EXIT"))
      System.out.flush()
    }, s"calibration-probe-exit-$name"))
end CalibrationProbe
