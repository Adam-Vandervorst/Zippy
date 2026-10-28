package morkl

import morkl.Syntax.{*, given}
import munit.FunSuite

class GeneratedArtifactDeterminismTest extends FunSuite:
  test("iterk binder names depend on syntax rather than lambda identity") {
    def build(): Space =
      S"rows".iterk(3, S"tail", path => Space.Singleton(path) \/ S"tail")

    val first = build()
    val second = build()
    assertEquals(first, second)
    assertEquals(first.show, second.show)
    assert(!first.show.contains("__iterk_probe_"), first.show)
  }

  test("different iterk bodies do not share a generated binder identity") {
    val singleton = S"rows".iterk(2, S"tail", path => Space.Singleton(path))
    val wrapped = S"rows".iterk(2, S"tail", path => "tag" x Space.Singleton(path))
    assertNotEquals(singleton.show, wrapped.show)
  }

  test("zero-arity iterk binds the tail name to its source exactly once") {
    var invocations = 0
    val result = S"rows".iterk(0, S"tail", _ => {
      invocations += 1
      S"tail"
    })
    assertEquals(result, S"rows")
    assertEquals(invocations, 1)
  }

  test("deterministic nested iterk binders remain closed and executable") {
    val (first, firstContext) = NQueensExample.program(4)
    val (second, _) = NQueensExample.program(4)
    assertEquals(first.body, second.body)
    assertEquals(first.body.show, second.body.show)
    assertEquals(Matching.freeMentions(first.body), Set.empty)
    assertEquals(Matching.freeRefs(first.body), Set.empty)
    val result = eval(first.body)(using PathContext.emptyMap, SpaceContextMap(Map.empty), firstContext)
    assertEquals(result.paths.size, 2)
  }
