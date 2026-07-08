# P-16d6e4aA A-4 prep: the paper reread — watch-item RESOLVED (Fable, 2026-07-08 session 4b)

Reread of the paper's §6.1–6.3 (pp. 25–29, Props 6.5/6.9, Lemmas 6.6–6.8, (82)–(92)),
Prop 6.18 + Cor 6.19 (p. 34), and the §8 consumption (pp. 39–41, (124)–(132)).  This
freezes the un/ram form identification for A-4 and records what the paper itself proves,
so A-3/A-4 formalize the *right* statements.  ⚠-watch-item of the e4/c1c rows: **resolved**.

## 1. The paper's candidate value chain (what A-3/A-4 mirror)

**Prop 6.5 (Complete base second-order word expansion), (82)/(83)** — the paper *already
does Route W's A-3*: normalizing the cohomology representative so that only `x₀` varies
(by `c`), the relator evaluation of the base class `κ⁰_q` on the candidate source is the
base contribution ledger (p. 26 table: factors `h₀, u₁⁻¹, x₁^σ, d₀ = (x₀τ)₂^ω x₀⁻¹,
z₀ = x₀^{σ₂²}, [d₀,z₀]` with `V`-coordinates `0,0,0,(P+1)c, U⁻¹c, 0`), summing to

    Q⁰_A(c) = q(c) + B((P+1)c, U⁻¹c)                                  (82)

with the **frozen dichotomy** (83):

| regime | condition | form |
|---|---|---|
| unramified | `T = 1` (tame operator trivial on `V`) | `Q⁰_A = q` — the invariant form itself, NO twist (`U = 1` too, per 6.9's proof) |
| ramified | `V^T = 0` | `Q⁰_A(c) = q(c) + B(c, U⁻¹c)` — the Wall double `q_U`, `U = S^{ω₂}` |

The repo's `hunram : ∀ v, c tameTau • v = v` is exactly `T = 1` ✓.  Key structural
points from the proof: only `d₀` and `z₀` carry `V`-coordinates; the commutator
`[d₀, z₀]` contributes exactly the polar term; `u₁⁻¹`/`x₁^σ` have zero `V`-coordinate on
the normalized representative and hence no quadratic contribution; the `m_c`-terms occur
only as central coordinates of `d₀`/`z₀` and do not affect the commutator.

**Affine classes are NOT in the base Gauss sum**: (85) `Q_{A,κ,ρ}(c) = Q⁰_A(c) +
⟨c, ρ*γ_κ⟩ + ι_A(ρ*δ_κ)` for general `κ = κ⁰_q + Γ_{γκ} + inf δκ` — and §6.3 (p. 29)
states explicitly "the affine terms are not folded into the base Gauss sum" (handled by
the phase-cover argument, i.e. the repo's `phaseChi` lane).  The repo's `QZero` at
`dat = kappa0` is the base class ✓ — A-3/A-4 need only (83), never (85).

**Arf pins** — Lemma 6.6 (Wall doubling): `Arf(q_U) = Arf(q) + rank(1+U) (mod 2)`;
Lemma 6.7 (hermitian lines): unramified invariant forms are trace forms
`Tr_{D₀/𝔽₂}(axx*)`, each of Arf 1; Lemma 6.8: ramified `Arf(q) ≡ s`,
`rank(1+U) = rs(2^a−1) ≡ s`, so **`Arf(Q⁰_A) = 0` ramified**; unramified
**`Arf(Q⁰_A) = Arf(q) = 1`**.

**Prop 6.9 (Candidate base determinant zero count), (91)**:

    #(Q⁰_A)⁻¹(0) = 2^{d−1} − 2^{d/2−1}   (V unramified)
                 = 2^{d−1} + 2^{d/2−1}   (V ramified)

— **identical numbers to the local Prop 6.18/(115)**, so the same Gauss sums
`G0 = −2^m` (unram) / `+2^m` (ram); Prop 6.18's remark makes the source-independence
explicit ("The candidate base form `Q⁰_A` has the same Gauss sum by proposition 6.9").
This is the twin-duality shape the `prop_8_9` ledger's shared `G0` encodes ✓.

## 2. Repo cross-check (formalization status of the pins)

| paper | repo | status |
|---|---|---|
| Lemma 6.6 `q_U` | `QuadraticFp2.qDouble q U x := q x + polar q x (U x)` | ✓ banked |
| Lemma 6.8 (incl. `Arf(Q⁰_A) = 0` ram) | `SectionSix.lemma_6_8` (cl. 4) | ✓ landed |
| Prop 6.9 unram count | `SectionSix.prop_6_9_unramified` | ✓ landed |
| unram Arf pin | `PhaseGaussLIndep.arf_qbar_eq_one_of_unramified` | ✓ landed |
| Arf ⟹ Gauss | `PhaseGaussLIndep.gaussSum_eq_of_arf_eq` | ✓ landed |
| Prop 6.5 ledger (82)/(83) | **A-3's deliverable** (via A-2's `QZero_eq_obs`) | in flight |
| zero-count → residue assembly | **A-4** (mirror `GaussZFinal`) | open |

**Orientation note (2-line reconciliation for A-4)**: the paper's ramified `B`-term is
`B(c, U⁻¹c)`; the repo's `qDouble` uses `polar q x (U x)`.  Pointwise equal:
`B(x, U⁻¹x) = B(Ux, x) = B(x, Ux)` (substitute `y = U⁻¹x` + polar symmetry) — so the
identification is orientation-free; A-4 should still expect a one-lemma
`polar q x (U⁻¹ x) = polar q x (U x)` bridge if A-3's ledger output lands in the paper's
spelling.

**`hfaith` caution**: the landed pins `arf_qbar_eq_one_of_unramified` /
`sum_sign_Q0loc_*` thread `hfaith` — over `Γ_A` prefer routing the `V^{C₀} = 0` input
through `GaussZCoordGammaA.hfix_of_simple_nt` (`hnt`-only); where a *pin* itself demands
`hfaith` (frame-level, about the block's faithful image — not the source), it is
per-`(l,h)` frame data supplied at the ThmFourTwo consumer alongside the `hpack`, same
as the local discharge.

## 3. Consequences for the A-3/A-4 seam

* A-3's target statement should be (83) verbatim in the A-1 coordinates: for
  `x : Z¹⧸B¹`, `Q̄⁰(x) = q̄(v)` (unram, under `hunram`) / `= qDouble q̄ U (v)` (ram, under
  `V^T = 0`), where `v` is the `x₀`-generator coordinate of the gauge-normalized
  representative (`h1CoordGammaA`), and the normalization freedom is absorbed exactly as
  in the paper's proof ("only `x₀` varies").
* A-4 then = Prop 6.9's two counts (unram: the trace-form count — check whether
  `prop_6_9_unramified`'s statement already covers the *candidate* spelling or needs a
  transport; ram: `lemma_6_8` cl. 4 + the standard even-dimensional zero-count) + the
  `gaussZ_reduction`/`h1CoordGammaA` finsum transport, mirroring `GaussZFinal`'s spine
  with the `GaussZCoordGammaA` pack.
* The (140)-side consumption ((126)–(132), pp. 39–41) is fully banked plumbing
  (`lemma_8_5`-shape Gauss transform; `phase140_from_residues`); nothing further from
  the paper is needed there.
