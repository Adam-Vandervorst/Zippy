# Trie-layer asymptotic audit

This report records the focused response to the trie/cursor/range/closure audit.
The lasting evidence is structural counters and denotation tests; wall-clock
timings are secondary and distribution-specific.

| Area | Implemented law | Permanent evidence |
| --- | --- | --- |
| Boolean algebra parent wrapping | Patricia constructors register exact path/node/child aggregates; `nodeFromChildren` is O(1) after the algebra traversal. | 8,192-wide root-disjoint union: one semantic node, one Patricia node, one parent allocation. |
| Incremental binary union / fixpoint | Operation-local summaries for persistent Patricia branches are promoted weakly across operations; a small delta touches one Patricia spine rather than rescanning the wide accumulator. | At K=512/2,048/8,192/32,768, folded singleton union performs exactly K trie visits, K−1 parent allocations, and 7,907/35,811/159,715/704,483 distribution-specific Patricia visits. Timings were 1.05/4.80/16.06/77.00 ms versus the review's 6.75/92.83/2,567.28/27,887.09 ms. At widths 256/1,024/4,096/16,384, a wide-accumulator one-delta fixpoint stays below eight semantic visits and a constant multiple of the fixed 32-bit Patricia depth, with constant allocations and exactly two rounds. |
| Distribution-sensitive algebra | Work is the touched Patricia structure, not W. Leaf pairs are fused without lookup/update retraversal. | Identity `0`, root-disjoint `1`, quarter-interwoven `W/2+1`, fully interwoven `2W-1` Patricia visits. |
| `joinAll` / `tailsUnion` | Identity deduplication plus balanced `union`; shared/disjoint map branches remain shared. | 4,096 equal references: zero node visits/allocations; distinct singleton reduction has exactly K−1 semantic joins. |
| Composition | Transform the left child map with unchanged topology, share right subtries, wrap once. | Asymmetric cost-counter families: growth only with the left operand; prefix-free allocation equals rebuilt internal left nodes. |
| Suffix/tails closure | A single path becomes a minimal acyclic suffix automaton; zipper closure retains one full frontier summary. | Depths 256/1,024/4,096 for repeated and alternating labels are linear; explicit suffix denotation checks. |
| Read cursor | Store current focus and ancestors. | Depth-256 descent performs one initial semantic-node lookup, then no root replay. |
| Concrete zipper rebuild | Frames retain original parent and use child aggregate deltas. | Depth-256 edit: zero scans, exactly 256 parent allocations. |
| Sibling movement | Cache ordered sibling array and frame index. | Walking 4,096 siblings in both cursor implementations performs one ordering, not per-step sorting. |
| Range / last / drop-last | Cached order plus cumulative rank frontiers and binary key/rank lookup. | Existing eager/lazy range tests ensure unrelated and selected children are not sized prematurely. |
| Virtual patch | One-key overlay; concrete patches use `IntMap` deltas. | Zipper denotation oracle plus focused rebuild counter. |
| Path concat | Iterative factor flattening. | 12,000-factor left-associated path evaluates without quadratic copying/stack growth. |
| Construction / insertion | Bulk paths freeze once; incremental insertion saves/rebuilds frames iteratively. | Wide/deep bulk counters allocate only final semantic nodes; 12,000-item insertion is stack-safe. |
| Specialized iteration | Build head-dependent union, then wrap a static prefix once. | 512 heads with a 64-item prefix has allocation bounded by O(H+P), not O(HP). |
| Lexical contexts | Persistent-map updates rather than mutable copy and `toMap`. | Exercised by trie/zipper evaluator suites. |
| AST dependency / intersections | Identity-keyed dependency caches; iterative intersection flatten. | 4,096 left-associated intersections evaluate without quadratic vector copying. |
| Dead suffix helper | Removed unused quadratic `postfixes`. | Compile/oracle suites. |

The distribution benchmark uses exactly the same prebuilt operand at each
repetition and checks the result before timing. On the focused run its exact
counter rows were:

| W | identity | root-disjoint | quarter-interwoven | fully interwoven |
| ---: | ---: | ---: | ---: | ---: |
| 256 | 0 | 1 | 129 | 511 |
| 1,024 | 0 | 1 | 513 | 2,047 |
| 4,096 | 0 | 1 | 2,049 | 8,191 |
| 16,384 | 0 | 1 | 8,193 | 32,767 |

These are exact Patricia-visit counts for the benchmark's fixed encoded-key
distributions, not upper approximations. They are not claimed for every
process-global path-label interning order: relabeling keys can change Patricia
topology while preserving the structural bounds. The raw local timing CSV is
intentionally not checked in; `build.log` contains only its one-line run summary.
