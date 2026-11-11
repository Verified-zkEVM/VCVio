# 6. Instability: a classical quantity for quantum proofs

Covers: The classical instability calculus and its role in quantum proofs. See
[conventions](../reference/conventions.md). Read first: tutorial
[chapter 6](../tutorial/6-quantum-queries.md); builds on [guide 2](2-vectors-and-hybrid-bound.md),
[guide 5](5-qrom.md).

Quantum security proofs in the QROM often use Zhandry's **compressed oracle**: the random function
is replaced by a quantum register holding a superposition of partial tables (*databases*), to which
each query adds, changes or removes an entry. A property $P$ of databases, such as "contains a
collision", gives a projector $\Pi_P$, and the adversary wins only if the final database has $P$.
The question is how fast one query can move amplitude into $P$.

The **instability** $I(P, t)$ answers it with a classical quantity: the worst-case probability that
extending a database with fewer than $t$ entries at one fresh input, by a uniformly random answer,
changes whether it has $P$ (`QueryCache.instability`).

**Example: collisions.** Let $D$ have fewer than $t$ entries and no collision. A fresh answer drawn
uniformly from $n$ values creates a collision only if it equals one of the at most $t - 1$ stored
answers, so with probability at most $(t-1)/n$; and an extension never removes a collision. Hence
$I(P_{\mathrm{col}}, t) \le (t-1)/n$ (`instability_cacheHasCollision_le`).

**How it is used.** Classically, an algorithm making $t$ queries wins with probability at most
$t \cdot I$, here the birthday bound $t^2/n$. Chiesa, Manohar and Spooner show that one quantum
query moves amplitude across the boundary of $P$ by at most $\sqrt{6 I(P, t)}$
($\|\Pi_P\,\mathsf{cO}\,\Pi_{\bar P}\|^2 \le 6\,I(P,t)$), so after $t$ queries the amplitude in $P$
is at most $t\sqrt{6I}$ and the winning probability at most $6t^2 I$, here $6t^3/n$. The classical
bound becomes a quantum bound at the cost of one more factor of $t$.

VCVio proves the classical side: the definitions, the rules for combining instabilities of
different properties (`instability_union_le`, `partitionInstability_eq_iSup_flip_compl`), and the
collision and Merkle-extraction bounds. The quantum lemma that turns instability into the amplitude
bound is not part of these files.

## Checks

**They compute the right numbers.** The tests work small examples to exact values: the collision
bound $(t-1)/n$ attained for $t = 2$, $n = 4$.
