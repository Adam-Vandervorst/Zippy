package morkl

import munit.FunSuite

/** ==================================================================================================
 *  THE TWO THINGS `ArtifactSink` REFUSES, AND THE ONE IT MUST NOT PASS SILENTLY (plan.md 0.3).
 *
 *  The sink's value is entirely in its failure modes: in VERIFY mode it writes to a scratch twin and
 *  compares, so the only way it can be WRONG is by reporting agreement where there is none.  Three
 *  such paths, each checked here rather than argued for in the header:
 *
 *   1. A BENCHMARK OUTPUT MUST BE REFUSED.  `corpus_runtimes.csv`, `expressivity.csv`,
 *      `prog_matrix.tsv` and `docs/BENCHMARKS.md` belong to `PublishManifest`, which exists so that
 *      one publication carries one commit identity and one environment record.  Routing one through
 *      this sink instead would put a measured number behind a plain environment variable.  The two
 *      gates cover disjoint sets by construction, and this is the check that they do.
 *   2. AN ARTIFACT WITH NO COMMITTED TWIN IS A FINDING, NOT A PASS.  A run that produces a NEW
 *      artifact has changed what the tree claims just as much as one that changes an existing file;
 *      an emitter that started writing a cell nobody declared would otherwise be invisible.
 *   3. THE SECOND WRITE TO ONE PATH REPLACES THE FIRST FINDING.  `EquivPipelineTest`'s egglog rounds
 *      ladder writes one artifact once per rung, and only the rung it settles on is the artifact —
 *      so a stale finding from rung 8 must not survive a green rung 12.
 *  ================================================================================================== */
class SinkGuardCheck extends FunSuite:

  test("1. a BENCHMARK output is refused, and the message says which gate owns it") {
    for rel <- Vector("corpus_runtimes.csv", "expressivity.csv", "prog_matrix.tsv",
                      "docs/BENCHMARKS.md") do
      val f = new java.io.File(RunEnvironment.repoRoot, rel)
      val e = intercept[IllegalStateException](ArtifactSink.write(f, "x"))
      assert(e.getMessage.contains("belongs to PublishManifest"),
        s"`$rel` was not refused with the right reason: ${e.getMessage}")
      // and the same on the binary path, which is a separate entry point
      val e2 = intercept[IllegalStateException](ArtifactSink.writeBytes(f, Array[Byte](1)))
      assert(e2.getMessage.contains("belongs to PublishManifest"), e2.getMessage)
  }

  test("2. an artifact with NO committed twin is reported ABSENT, not passed") {
    assume(!ArtifactSink.regenerating, "REGENERATE mode has nothing to compare against")
    val g = new java.io.File(RunEnvironment.repoRoot, "proofs/__sinkguard_absent.smt2")
    assert(!g.exists(), s"${g.getPath} exists in the tree; this probe needs a path that does not")
    ArtifactSink.write(g, "; a cell nobody declared\n")
    val f = ArtifactSink.findings.find(_.rel == "proofs/__sinkguard_absent.smt2")
    assert(f.isDefined, s"no finding for an absent committed twin: ${ArtifactSink.findings.map(_.show)}")
    assert(f.get.show.startsWith("ABSENT"), s"wrong finding kind: ${f.get.show}")
    // and it is NOT written into the tree
    assert(!g.exists(), "VERIFY mode wrote the artifact into the tree")
  }

  test("3. a second write to one path REPLACES the first finding (the rounds-ladder case)") {
    assume(!ArtifactSink.regenerating, "REGENERATE mode records no findings")
    // an artifact that DOES exist, written first wrong and then right
    val committed = new java.io.File(RunEnvironment.repoRoot, "datalog-morkl.txt")
    val real = new String(java.nio.file.Files.readAllBytes(committed.toPath),
                          java.nio.charset.StandardCharsets.UTF_8)
    ArtifactSink.write(committed, real + "// rung 8, rejected\n")
    assert(ArtifactSink.findings.exists(_.rel == "datalog-morkl.txt"),
           "the differing write produced no finding")
    ArtifactSink.write(committed, real)
    assert(!ArtifactSink.findings.exists(_.rel == "datalog-morkl.txt"),
      "a matching write did not clear the earlier finding — the rounds ladder would report every " +
      "artifact as stale on the strength of a rung it discarded")
  }
end SinkGuardCheck
