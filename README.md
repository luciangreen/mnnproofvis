# Prolog MNN Proof Visualiser

Annotates Prolog algorithms with insights about possible optimisations and unneeded computation. Each insight is backed by a named law that is proved in `proofs.pl`.

The insights cover: `append([X],L,R)` → `R=[X|L]`, constant folding, duplicate pure goals, `length(L,N), N>0` → `L=[_|_]`, needless `true`, dead results, double `reverse`, `findall` + `length` → `aggregate_all(count)`, `member` + `!` → `memberchk`, and sum recursion → accumulator.

`optimise/2` applies the rewrites, and `equivalent/5` checks that the optimised program gives the same outputs in a meta-interpreter.

```
?- example(P), visualise(P).
?- example(P), optimise(P, P2), portray_clauses(P2).
```

Proved properties: every law (append singleton, reverse involution, length positive, count of solutions, member/memberchk, evaluation determinism, idempotence, unused results, conjunction identity, sum accumulator), optimisation preserves meaning, and the implementation equals the spec.

## Tests and proofs

```
swipl run_tests.pl        # runs the 200 saved I/O pairs and checks every proof
swipl tests/gen_io.pl     # regenerates tests/io_pairs.pl from spec.pl
```

- `tests/io_pairs.pl` has 200 saved `io(Id, Predicate, Input, ExpectedOutput)` facts.
- The expected outputs come from `spec.pl`, an independent specification written in a different style from the implementation. Because the implementation is checked against a separate oracle, a pass is real evidence and not the program checking itself.
- `proofs.pl` has machine-checked `proof(Name, Goal)` theorems. Each one is checked exhaustively on a bounded domain or over sample inputs, and its comment gives the general (usually inductive) argument.

All files are plain, portable SWI-Prolog, with no packs needed.
