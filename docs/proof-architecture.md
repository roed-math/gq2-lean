# Proof architecture of the $G_{\mathbf Q_2}$ presentation paper

A map of the paper's proof, its dependency DAG (from the body + Appendix D
"Proof dependency certificate"), and a **formalizability grade** for each node.
This is the plan-of-record for what to attempt in Lean and in what order.

Grades:
- **F** — formalizable now against Mathlib (finite/abstract group theory).
- **F′** — formalizable now but needs modest new infrastructure (a few hundred lines).
- **P** — needs a missing *foundation* (profinite presentations, $\widehat{\mathbf Z}$, …) first.
- **H** — hard: needs a large absent theory (Demushkin, local CFT, Tate duality, cup products).

## Top-level spine (how Theorem 1.2 is assembled)

```
Theorem 1.2  (G_Q2 ≅ ⟨σ,τ,x0,x1 | τ^σ=τ², h0 u1⁻¹ x1^σ c0 =1, ⟨⟨x0,x1⟩⟩ pro-2⟩)
  ▲
  │  Lemma 2.5 (one-sided profinite reconstruction)        [F′]
  │      + eq. (154):  ∀ finite G,  |Sur(Γ_A,G)| = |Sur(G_Q2,G)|
  │
  ├── Γ_A := candidate profinite group = lim of "admissible" finite quotients   [P: needs free profinite grp]
  │      Prop 2.3: Sur(Γ_A,G) ↔ admissible marked generating quadruples in G     [F, once Γ_A exists]
  │
  └── eq. (154) is proved by:
        Prop 3.2  common tame quotient  Γ_A/W_A ≅ T_tame ≅ G_Q2/W_F              [F′ tame side / H local side]
        Prop 1.1  marked dyadic Demushkin normalization of G_Q2(2)              [H]
        Thm 4.2   boundary-framed exact-image theorem  (the technical heart)     [H]
        Lemma 10.1 exhaustion by tame boundary frames  ⇒ (154)                   [F′ combinatorial glue]
```

## The technical heart: Theorem 4.2 (proved in §9 by strong induction on $|L_Y|$)

The claim: for every "boundary-framed marked target", the exact-image lift counts
from the two sources ($\Gamma_A$ via a finite Fox–Heisenberg word complex, and $G_{\mathbf Q_2}$
via continuous local Galois cohomology) agree. Induction on the marked 2-kernel $|L_Y|$;
Lemma 9.4 guarantees every recursive call strictly decreases it.

Three lifting regimes (§9.1–9.3), each reducing to strictly smaller targets:
- **9.1 terminal** (only trivial module factors): Schur–Zassenhaus split
  $Y \cong H \times_{H_2} Q$, $Q$ a finite 2-group (Lemma 9.2).            **[F′]**
- **9.2 elementary quotient $M$**: $H^2_{\Gamma,\rho}(M)=0$ and
  $|Z^1_{\Gamma,\rho}(M)| = 2^{2\dim M}$ match; strict decrease (145).      **[H: needs H¹/H² + local duality]**
- **9.3 Frattini layer $R$ + scalar central pushouts**: the $R$-valued
  obstruction dual $D_R=(R^\vee)^C$; Fourier inversion over characters
  $\lambda\in D_R$; the affine central formula (151) via a constrained
  Fourier–Gauss sum $G(Q^0)$.                                              **[H: cup products, Gauss sums, Evens]**

Feeding Theorem 4.2:

| paper node | statement (abbrev.) | grade |
|---|---|---|
| Lemma 5.7 / Prop 5.8 | finite-word Stokes identities ⇒ Fox–Heisenberg chain map (5.10) | H |
| Lemmas 5.11, 5.13 | exact-cone dévissage; duality for elementary modules (5.15) | H |
| Lemma 6.13 | universal two-point $D_8$ class ⇒ half-orbit Evens normalization | H |
| Lemma 6.15 | normalized Shapiro–corestriction ⇒ base form vanishes on deep half (6.17) | H |
| Lemma 6.8 | ramified Hermitian + fixed-space ⇒ candidate ramified Gauss sign (6.9) | H |
| Lemma 6.16 | deep-unit Hilbert-symbol ledger ⇒ local ramified hyperbolicity (6.18) | H |
| Lemma 6.21 | qualified determinant transgression ⇒ $B/T\cong V\rtimes C$ split | H |
| Lemma 8.6 | radical-edge variation ⇒ exact half-torsor count | H |
| Prop 8.9 | closed recursion (136)–(142) ⇒ Theorem 4.2 | H (glue over H nodes) |

## Nodes that are genuinely formalizable now (the target list for this repo)

These are self-contained (finite/abstract) and do **not** touch the missing analytic/arithmetic tower:

| node | statement | file | grade |
|---|---|---|---|
| **Lemma 2.5** | topologically f.g. profinite $P$, any profinite $Q$; $\forall$ finite $H$, $|\mathrm{Sur}(P,H)|=|\mathrm{Sur}(Q,H)|$ ⇒ $P\cong Q$ | `Reconstruction.lean` | F′ |
| **Lemma 2.1** | finite subdirect closure of admissible quotients is admissible | `FiniteGroupLemmas.lean` | F |
| **Prop 2.3** | $\mathrm{Sur}(\Gamma_A,G)$ ↔ admissible marked generating quadruples | `Statement.lean` | F (given $\Gamma_A$) |
| **Lemma 3.1** | finite quotient with $t^s=t^2$: $t$ has odd order, group is $C_e\rtimes C_n$, normal 2-subgroups central+unramified | `Tame.lean` | F |
| **Lemma 9.1** | coprime-kernel subdirect product is the full fibre product | `FiniteGroupLemmas.lean` | F |
| **Lemma 9.2** | trivial-module-factor target splits as $H\times_{H_2}Q$ (Schur–Zassenhaus) | `FiniteGroupLemmas.lean` | F′ |
| **Words / App. A–B** | auxiliary words (1)–(3) and admissibility predicate, $\omega_2 \to$ integer via CRT | `Words.lean` | F |

**Strategy.** Prove the F/F′ nodes for real. State the H nodes as `sorry`-backed
Lean theorems with paper cross-references, so the missing foundations are visible as an
explicit gap map. Assemble the spine so that *if* every `sorry` were filled, Lean would
accept Theorem 1.2 — i.e. the top-level logical wiring is checked even while the leaves are open.

## Independence from the computational verification

The paper (Remark 1.3, §11) stresses the displayed relator word is *separately*
computer-verified but that verification is **not** an input to the proof. App. B gives the
machine-readable word with $\omega_2 \equiv 40491355905 \pmod{85667662080}$. This is a good
**cross-check target**: `Words.lean` can evaluate the relator in concrete finite groups and
confirm it matches the paper's ledger (App. A eqs. 155–160), independently of the main proof.
