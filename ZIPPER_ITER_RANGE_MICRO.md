# Iter Range-Tail Zipper Microbenchmark

This isolates `SpaceZipper.Iteration(..., RangeTail(0, -1))`, the path used by range-tail iteration over child zippers. The old model first collected all output keys, then recomputed each key by scanning every source head again. The current implementation accumulates per-key children in the first branch traversal and joins them once.

| source heads | tail fanout | result paths | old emulation ms | current ms | old / current |
|---:|---:|---:|---:|---:|---:|
| 32 | 12 | 352 | 13.753 | 8.297 | 1.66 x |
| 96 | 16 | 1,440 | 107.182 | 104.017 | 1.03 x |
| 192 | 16 | 2,880 | 414.336 | 419.373 | 0.99 x |
