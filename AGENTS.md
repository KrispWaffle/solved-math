# Working on Solved Math

For a new conjecture, find its original statement and check current papers, public proof repositories, and their issue discussions for an earlier resolution. Record the search and the exact claim in the result’s audit.

Use Lean for new resolutions. State the source conjecture with its original quantifiers, define the mathematical objects, and connect any stronger theorem to the source statement in Lean. Track the declaration in `lean/ProofAudit.lean` and `docs/lean-status.md`. Mark partial formalizations by the statement that actually compiles.

Keep each result in `results/<slug>/` with a README, a written proof, and an audit. Link the result from the root catalog and history. Run `./scripts/verify.sh` before marking a result Lean-verified.
