# Cornerstone Backend Parity Report

Status: PASS

This report records executable Scala differential checks. It is not a solver proof: generation fails unless reference, trie, optimized source, zipper, and operation-graph results agree. Counterexample-sensitive symbolic SMT and axiomatized structural-FOL schema checks live under `proofs/open/`; the latter assume backend/source agreement per constructor and are not independent implementation-equivalence proofs.

| Example | Result paths | Result digest | Checked relations |
| --- | ---: | --- | --- |
| `aunt` | `3` | `a49b8dddcc87b1e175732592` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
| `semi-naive-datalog` | `21` | `8bf48c060741eeca763ad5f1` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
| `gol` | `4` | `f052ec939c6bc8b1f8659a33` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
| `15-puzzle` | `2` | `5f7f76bc432e2f7a13fc479d` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
| `temperature` | `1` | `cdc9e2ccc913556de492214b` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
| `nqueens` | `2` | `0d3b049b52c0e9f10bfdb489` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
| `scc` | `2` | `7e0719960d48003007075b49` | trie_vs_reference, space_optimized, zipper_vs_space, graph_execT_vs_space |
