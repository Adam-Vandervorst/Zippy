# Generated Cornerstone Spatial Summary

This deterministic table is generated from the production `SpatialTypeAnalysis` entry point. The analysis does not execute or materialize any concrete cornerstone output.

Regenerate it with `scala-cli run src/main/scala src/test/scala --test --server=false --scala 3.8.1 --source 3.3 --dependency org.scalameta::munit:1.2.1 --dependency org.scala-lang.modules::scala-collection-contrib:0.3.0 --main-class morkl.cornerstoneSpatialTypeReport --`.

| Program | Cardinality interval | Path-length interval | Strata |
| --- | --- | --- | ---: |
| `aunt` | `⌊result⌋=0, ⌈result⌉=(people * min(parentEdges, childEdges, femalePeople))` | `minPathLen≥3, maxPathLen≤3` | 1 |
| `semi-naive-datalog-fixpoint` | `⌊result⌋=edges, ⌈result⌉=(edges * edges)` | `minPathLen≥2, maxPathLen≤2` | 2 |
| `game-of-life` | `⌊result⌋=0, ⌈result⌉=(liveCells * 9)` | `minPathLen≥3, maxPathLen≤3` | 8 |
| `eight-puzzle-all-states` | `⌊result⌋=181440, ⌈result⌉=181440` | `minPathLen≥9, maxPathLen≤9` | 2 |
| `temperature` | `⌊result⌋=0, ⌈result⌉=worldCells` | `minPathLen≥4, maxPathLen≤4` | 1 |
| `nqueens` | `⌊result⌋=2, ⌈result⌉=2` | `minPathLen≥4, maxPathLen≤4` | 1 |
| `scc-representative-pairs` | `⌊result⌋=0, ⌈result⌉=(2 * sccEdges)` | `minPathLen≥2, maxPathLen≤2` | 3 |
