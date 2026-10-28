package morkl

import morkl.Syntax.{*, given}

/** The paper's seedless divide-and-conquer SCC program.
  *
  * A pivot is selected from the remaining nodes, forward and backward
  * reachability are intersected to emit one representative/member row for
  * the pivot's component, and the routine recurses over the three disjoint
  * residual partitions. Singleton components deliberately emit no row. */
object SccCornerstone:
  val edges: SpaceValue = SpaceValue(
    "a.b", "b.a", "b.c", "c.d", "d.c", "e.f",
  )

  val reachableRoutine: Routine = Routines.reachable_routine
  val sccRoutine: Routine = Routines.seedless_scc_routine
  val defs: Vector[Routine] = Vector(reachableRoutine, sccRoutine)
  val rc: PartialFunction[RoutinePtr, Routine] = mod(defs*)

  def transpose(source: Space): Space =
    val from = PathRef("scc_from").known(1)
    val neighbors = SpaceMention("scc_neighbors")
    val to = PathRef("scc_to").known(1)
    val remainder = SpaceMention("scc_remainder")
    Space.Iteration(
      source,
      from,
      neighbors,
      Space.Iteration(
        Space.Mention(neighbors),
        to,
        remainder,
        Space.Singleton(Path.Concat(Path.Deref(to), Path.Deref(from))),
      ),
    )

  def expression(source: Space): Space =
    val backward = transpose(source)
    val forwardNode = PathRef("scc_forward_node").known(1)
    val backwardNode = PathRef("scc_backward_node").known(1)
    val nodes = Space.Union(
      Space.Iteration(source, forwardNode, SpaceMention("scc_forward_tail"),
        Space.Singleton(Path.Deref(forwardNode))),
      Space.Iteration(backward, backwardNode, SpaceMention("scc_backward_tail"),
        Space.Singleton(Path.Deref(backwardNode))),
    )
    sccRoutine.name(source, backward, nodes)

  val body: Space = expression(Space.Literal(edges))
  val expected: SpaceValue = SpaceValue("a.b", "c.d")
