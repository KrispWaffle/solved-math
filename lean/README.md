# Lean proofs

SolvedMath imports each verified result. ProofAudit checks the axiom dependencies of both separator declarations. The pinned toolchain and the empty dependency manifest allow the project to build with the Lean core library alone.

From this directory, run

```sh
lake build
lake env leanchecker --fresh --verbose SolvedMath
```

[Theorem index and verification scope](../docs/lean-status.md)
