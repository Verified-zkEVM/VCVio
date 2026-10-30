# Conventions

These conventions specify the basis, matrix, tensor, state and oracle notation used throughout the
[guides](../guide/README.md).

| Item | Convention |
|---|---|
| System | A basis type `A`; state space $\mathbb{C}^A$; operators `Matrix A A ℂ`. `Unit` is one-dimensional. |
| Operators | `K : Matrix B A ℂ` maps $\mathbb{C}^A \to \mathbb{C}^B$: output index first, vectors are columns. |
| Adjoint | `Kᴴ` is the conjugate transpose $K^\dagger$. |
| Composition | `L * K` applies `K` first. Kraus maps compose as `conj L ∘ conj K = conj (L * K)`. |
| Kraus map | `conj K` is $\rho \mapsto K\rho K^\dagger$, not entrywise conjugation. |
| Inner product | Conjugate-linear in the first argument, as $\langle\phi|\psi\rangle$. |
| Tensor order | `A × R` is $\mathbb{C}^A \otimes \mathbb{C}^R$; `(X ⊗ₖ Y) (a, r) (b, s) = X a b * Y r s`. |
| Reference system | On the right: `amplify Φ R` is $\Phi \otimes \mathrm{id}_R$; `frame R p` is $p \otimes \mathrm{id}_R$. |
| Complete positivity | `IsCP` quantifies over `Fin k`; `IsCP.amplify_posSemidef` gives every finite reference. |
| States | `SubState`: PSD, trace at most one. The deficit is the probability of failure so far. |
| Post-states | Unnormalized: `post p ρ a = p.branch a ρ`, whose trace is the probability of `a`. |
| Chain rule | Continuations run on unnormalized post-states; no extra factor for the first outcome. |
| Failure | Missing trace; there is no failure outcome. |
| Partial trace | `traceRight A R` discards the right factor: $(\operatorname{tr}_R\rho)_{aa'} = \sum_r \rho_{(a,r),(a',r)}$, not normalized. |
| Choi matrix | Output first, unnormalized: $C_\Phi = \sum_{a,a'}\Phi(E_{aa'}) \otimes E_{aa'}$ (Watrous's $J(\Phi)$). |
| Stinespring | Environment on the right: $S\psi = \sum_i (K_i\psi) \otimes |i\rangle$. |
| Runtime registers | (program register) $\times$ (private register). |
| Oracle unitary | $U_H|x, y\rangle = |x, y + H(x)\rangle$ on `X × Y`; XOR for bitstrings; inverse $U_{-H}$. |
| Outcomes | Any type; only countably many outcomes have nonzero weight. |
