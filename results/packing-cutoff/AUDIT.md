# Packing-cutoff proof audit

Section 7, item 8 asks about an absolute cutoff and also raises length-dependent bounds. The two constructions give a negative answer for an absolute cutoff and a lower bound along their respective pattern families. The November 26 proof by Cinna Davis predates this manuscript. [Original question](https://arxiv.org/html/2610.29846v1#S7) · [Earlier proof](https://github.com/1337isnot1337/solved-conjectures/blob/2e54a945aa14bb6965f88f9fc21c63e1d9183921/results/blitvic-kammoun-steingrimsson-packing-cutoff/PROOF.md)

The exact checker counts linear extensions from the actual window inequalities for $2\le k\le9$ through the first differing term. The manuscript proves the general formula using Catalan paths. This result currently has manuscript and Python coverage. [Checker](verify.py) · [Derivation and corrected search record](../../docs/research-log.md)
