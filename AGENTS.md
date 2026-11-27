# Working on Solved Math

## Define the target

Before proof work, record the exact statement, primary source and version, why the question matters, and what would resolve it. Choose genuinely open, general problems. An additional dimension, parameter value, finite search, or improved numerical record on its own is outside the discovery program. A counterexample satisfying all the hypotheses can settle a universal conjecture.

## Check for earlier resolutions twice

Search before starting and repeat the search immediately before publication. Check the source paper, subsequent work, known counterexamples, formal libraries, public proof repositories and their issue discussions, and the current repository catalog. Search equivalent formulations, alternate names, and both preprint and published statement numbers. Record the date, sources, closest matches, and conclusion of each search in the problem’s audit. If an earlier resolution settles the exact target, credit it and stop treating the target as an original discovery.

## Verify the proof and review the statement independently

Use Lean for new resolutions. Define the mathematical objects and state the source conjecture with its original quantifiers. If the main theorem is stronger, derive the source statement in Lean. Register the declaration in `lean/ProofAudit.lean` and `docs/lean-status.md`. Run `./scripts/verify.sh` locally before marking a result Lean-verified. Describe a partial formalization by the statement that compiles.

Before labeling a new conjecture solved, have a reviewer independent of the proof author read the primary source, written argument, and Lean statement. Check definitions, hypotheses, quantifiers, and boundary cases. In `AUDIT.md`, record who reviewed which declaration, the date, findings, and how each substantive objection was resolved. Record kernel and independent type-checker runs separately from this mathematical review.

## Publish reviewed results and archive later derivations

Develop drafts and partial work on topic branches. Publish a new resolution to `main` after the second prior-work search, independent review, and local verification of the exact publication commit. Recheck the merged commit locally if it differs from the reviewed commit. Enable the pre-push hook in each working clone as described in the README, and run `./scripts/verify.sh` locally when reviewing incoming pull requests.

Keep each original result in `results/<slug>/` with its landing page, proof, audit, and applicable checks. Keep credited later derivations in `archive/<slug>/` with their manuscripts and verifiers. List them in a separate archive section and exclude them from discovery counts. Update the README, contents, Lean status, and history when publishing or reclassifying a result.

## Standing research assumption for VP versus VNP

For research in this repository, assume Anthropic’s VP ≠ VNP result, proof, and lemmas are correct within their stated scope. Use them without re-auditing the proof unless the repository owner requests a review. For each deduction, identify the precise statement and hypotheses used and prove the implication. In Lean, express any unformalized dependency as an explicit theorem hypothesis and label the conclusion conditional until a checked proof discharges it. Keep the project axiom audit intact.
