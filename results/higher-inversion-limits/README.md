# Higher inversion limits for 1324-avoiding permutations

Claesson, Linusson, Ulfarsson and Verkama observed two different stabilization patterns when counting permutations that avoid 1324 and a second classical pattern of length four. Problem 8.4 asks for an explanation of the entire split. [Original question and prior case](https://arxiv.org/html/2604.01143v2#S8)

Let $a(n,k)$ count the avoiders of length $n$ with $k$ inversions. Fix an integer $d$. The difference $a(n+1,n+d)-a(n,n+d)$ is eventually an affine function $s_d n+t_d$. This holds for **every finite set of additional forbidden patterns**. On each diagonal, taking one further difference therefore gives the constant $s_d$. The proof identifies at most two independently variable increasing intervals in every family that can affect the count. [General affinity theorem](PROOF.md)

For a single additional pattern of length four, the classification is as follows, up to inverse and reverse-complement.

| Additional pattern | What happens on the diagonals |
|---|---|
| 1243, 1342, 1432, 2341, 3421, 4321 | The first difference itself stabilizes on every diagonal. |
| 2143, 2413, 2431, 3412, 4231 | One further difference stabilizes on every diagonal. In each of these five classes the first difference grows or decreases linearly on at least one diagonal. |
| 1234 | The counts themselves eventually vanish on each diagonal. |

For example, with partner 2143 the first difference eventually decreases by exactly two at each step on $k=n-1$. With partner 2413 it increases by three on that same diagonal. The proof gives a coefficient formula for all of these slopes. The explicit secondary sequence for 1342 was already known. [Classification and slope formula](CLASSIFICATION.md) · [Prior formula, Theorem 7.14 in the PDF](https://arxiv.org/pdf/2604.01143v2#page=35)

The five tertiary series also have explicit formulas. For 4231, the slope at degree $k$ is twice the number of ordered pairs of distinct-part partitions of total weight $k-2$. For 2143, every tertiary coefficient after the initial $-2$ is zero. [All five formulas, including the predicted identities](TERTIARY-SERIES.md)

The written proofs received independent mathematical review. Lean checks the end-component excess bound, the count of two free interval lengths, the six pattern certificates, the fifteen displayed slope coefficients and the all-degree convolution for each tertiary partner. The passage from an arbitrary source permutation to the finite interval families uses the written proof and Linusson and Verkama’s structural theorem. [Lean declarations and scope](../../docs/lean-status.md) · [Audit](AUDIT.md) · [Independent structural input](https://arxiv.org/abs/2408.15075)

Run `python3 results/higher-inversion-limits/verify.py` from the repository root to replay the occurrence and slope checks, or `./scripts/verify.sh` for the full local suite. [Coefficient checker](verify.py)
