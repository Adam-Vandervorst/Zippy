# Review

Resolve all of the following:

1. README is "PASS_WITH_PROOF_DEBT" is out-of-sync with PROOF_REPORT.md's "PARTIAL PASS"
2. `datalog-morkl.txt` and `terminating/datalog_a.txt` are duplicates
3. ALGEBRA.md should be updated to reflect the removed `PathItem.Symbol`
4. The proof runner defaults Vampire to the machine-specific `/Applications/Vampire`
5. Support functions in Zipper evaluator (which allows it to be used for semi-naive datalog)
6. Support demand-driven fixpoint traversal in the Zipper instead of just materializing
7. Incomplete dependent relation fibers, graph/degree inference, parameterized puzzle/queens arithmetic, and restriction lower coverage
8. Size upper bounds still explode on correlated nested iteration/product cases; lower bounds often collapse toward zero
9. Recursive cost recurrences needs to be supported
10. The `proofs/examples/smt2/*.smt2` are tautological
11. The spatial analysis is not automatic, and the README overstates it
12. The validate_*_acceptance functions seem superficial/redundant
13. laws.diff can be removed
14. Z3ResultSpaceSize.scala has a silent failure on not finding z3, this should crash. Also, the 1s timeout should be reported on firing rather than just reporting a bad bound in analysis
15. `proofs/open/smt2/*_full_open_*.smt2` should likely be regenerated, not commited?
16. The strongly connected components example should be treated like the other cornerstone examples (not ignored in tests, be in every benchmark table, have certificates, and a spatial report)
17. The operational manifest resting on alphabet `{a,b}` at max path length 3 should be extended as budget allows for it, e.g. given a "long" option (and probably executed in parallel)
18. `semi-naive-datalog-full-open` and `sliding-puzzle-2x2-full-open` are the most interesting examples, this should be part of the obligation
19. Add alpha-invariant loop-sharing in the graph representation
20. Size-only merges are linear in the operand the algorithm never descends in; this should be fixed more generically
21. Summing local worst cases is the wrong semantics for a lazy cursor -- the outer consumer decides which prefixes are forced — so `(A \/ B) /\ C` is charged the full inner union although it stays proportional to a fixed `C`
22. The set-interval domain proofs need to be bridged to the code with additional theorems

Produce resolution.md which points to precisely how each of the 22 bullet points was concretely resolved (and go back to development when this is not the case).
Append to build.log each change or experiment (which can be multiple entries for the tasks with larger scope).


