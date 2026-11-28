# The distribution and variance of the number of patterns

For independent Poisson random variables $N_{d,e}$ of mean two, indexed by positive horizontal and vertical distances, define

```math
Y=\prod_{d,e\ge1}(1-2^{-d-e})^{N_{d,e}}.
```

Then $X_n/2^n$ converges in distribution and in every positive integer moment to $Y$. In particular,

```math
\mathbb E Y=e^{-2},\qquad
\frac{\operatorname{Var}(X_n)}{4^n}\longrightarrow
e^{-4}(e^{2/9}-1).
```

Thus the fluctuations are of the same order as the mean. This answers the asymptotic variance and limiting-distribution questions in §4. [Source](https://arxiv.org/html/2601.13194v1#S4) · [Embedding class theorem](PROOF.md)

## Localizing the replacements

Fix the permutation plot $\{(j,\pi(j))\}$ and choose a subset $S$ by coloring each label red independently with probability $1/2$. The exact identity $X_n/2^n=\mathbb E_S[1/K(S)\mid\pi]$ follows by summing over embedding classes. The embedding class theorem and binomial concentration of $|S|$ imply
```math
\mathbb E\,\left|X_n/2^n-\mathbb E_S[2^{-W}\mid\pi]\right|\longrightarrow0.
```
Here each local replacement fixes all the red labels outside its moving pair.

Let $W_D$ count only interchangeable pairs whose horizontal and vertical distances $d,e$ are both at most $D$. For each $d,e$, the expected number of unordered plot pairs at these exact distances equals $2(n-d)(n-e)/(n(n-1))$ when $d,e<n$. It is at most two. Given the two partners, the probability that exactly one is red and that all points between their coordinates are white is at most $2^{-\max(d,e)}$: there are at least $\max(d,e)-1$ distinct intervening labels. Hence $\mathbb E(W-W_D)\le 2\sum_{\max(d,e)>D}2^{-\max(d,e)}\to0$ uniformly in $n$. This also bounds the error in replacing $2^{-W}$ by $2^{-W_D}$.

## Short pairs in a uniform permutation

For fixed $D$ the counts $N^{(n)}_{d,e}$ of plot pairs at distances $1\le d,e\le D$ converge jointly to independent Poisson variables of mean two. Blackburn, Homberger and Winkler’s Theorem 5 proves a Poisson limit for the aggregate count of pairs up to a prescribed Manhattan distance. We give the displacement calculation for the joint law used here. [Blackburn, Homberger and Winkler](https://arxiv.org/abs/1706.01557)

In a mixed factorial moment of fixed total order $h$, first take configurations in which the $h$ edges have disjoint endpoints. For any ordered sequence of displacement types there are $n^h(1+O(1/n))$ choices of the left horizontal endpoints and $2^h n^h(1+O(1/n))$ choices of the lower vertical coordinates and orientations, after excluding endpoint collisions and boundary violations. The $2h$ prescribed values occur with probability $1/(n)_{\underline{2h}}$. This gives $2^h$. For configurations with a shared endpoint, consider the graph on the $v$ prescribed plot points. If it has $c$ components, the bounded displacement along every edge gives $O(n^c)$ horizontal assignments and $O(n^c)$ vertical assignments. Distinct vertices cost $1/(n)_{\underline v}$, and at least one component has three vertices, so $2c-v<0$. The factorial moments thus converge to those of independent Poisson variables.

The following additional separation properties hold with probability tending to one for fixed $D$. Within a close pair's horizontal and vertical open strips there is no point belonging to both strips. For a prescribed pair and such an extra point there are $O(n)$ horizontal and $O(n)$ vertical assignments for three vertices. Between two different close pairs, their closed horizontal intervals are disjoint and so are their closed vertical intervals. Indeed a common endpoint costs $O(1/n)$ by the graph calculation. For four different endpoints a horizontal overlap gives $O(n)$ choices horizontally, $O(n^2)$ vertically and probability $O(n^{-4})$ for each complete assignment. Vertical overlap has the same bound. Finally, no label lies in the horizontal strip of one pair and the vertical strip of another. An extra point with this property permits $O(n^2)$ assignments on each axis for five vertices and hence has total probability $O(1/n)$. An endpoint in those strips would already violate the disjoint-interval condition. The constants in these estimates may depend on $D$.

On this event the sets of labels determining whether each close pair is interchangeable are disjoint. A pair of type $(d,e)$ needs exactly one of its endpoints red and all $d+e-2$ intervening labels white. Its probability given the plot is $2^{1-d-e}$. Averaging its contribution $2^{-\mathbf 1_{\mathrm{replacement}}}$ gives $1-2^{-d-e}$. Independence of the colors now gives

```math
\mathbb E_S[2^{-W_D}\mid\pi]
=\prod_{1\le d,e\le D}(1-2^{-d-e})^{N^{(n)}_{d,e}}.
```

The finite product converges in distribution by the joint Poisson law. The limiting infinite product exists and is positive almost surely because the expected sum of the absolute logarithms is finite. Letting $D\to\infty$ with the uniform error above proves convergence in distribution, for example by testing bounded Lipschitz functions. Since $0\le X_n/2^n,Y\le1$, every positive integer moment converges. Independence gives $\mathbb E Y^a=\exp(2\sum_{d,e}[(1-2^{-d-e})^a-1])$. For $a=1,2$ use $\sum_{d,e}2^{-d-e}=1$ and $\sum_{d,e}4^{-d-e}=1/9$ to obtain the stated variance.
