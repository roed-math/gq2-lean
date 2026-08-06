# χ-free clearing note (lane SQ, P2′ adjudication) — 2026-08-05

Companion to `GQ2/Dyadic/SqCore/ChiFreeClearing.lean` and
`GQ2/Dyadic/Instances/GammaLSylowPreimageRealizationBypass.lean` (both compile clean at HEAD
36e75fb0 against the 09761b6a cache; core prints std-3).  Successor to
`eichler-reduction-note.md`: the search target has **changed** from `SqEichlerSeed` to
`SqNuSeed`.

## The adjudication (routes 0 / A / 3, settled)

**Route 0 (pure bypass).**  Half true, and the true half is decisive.

* The downstream consumer of the L-row certificate is `MarkedCoreRealization (DSq h) (lNu h)`
  (`LabuteInterface.lean`), a two-field structure: the equivalence and the pointwise
  `ν`-matching `ι(lNu x) = ν_B(e x)`.  Its four exported theorems are exactly the
  `KExactSupplyRN` pro-2 block (`KAnalytic.lean`), which feeds `CertificateSupplyRN.ofL` and
  `GammaLCorrectedArithmeticInput` — the slot is pinned to `(DSq h, lNu h)` there.  **No
  χ-clause appears anywhere on this path**; the certificate's `orientation` and
  `correction_chi` fields have no remaining consumer (checked: `ofCertificateSq` had *no*
  call sites — its `hnuP` slot was never instantiated before `ztwoIota_lNu`; the
  `SelectedBranchRealization`/`BranchData.CoreCertificate` layer has no external consumers).
* But `nu_equiv` evaluated at a handle letter *is* the handle normalization
  `ν_B(e(u_j)) = 0`, so "never normalize handle rows" is impossible; and the proven τ-moves
  alone cannot do it: they act by `SL₂(ℤ₂)` per handle plane, preserving the ideal
  `(ν'(u_j), ν'(v_j)) ⊆ ℤ₂`, which never reaches `(0)` from a unit row.

**Route A (CoV transport of the M/N Proposition).**  Refuted, and the refuting reason is not
the χ-row.  The precise letter roles in spike §6.1's mechanism, from the symplectic form of
the Eichler unipotent of the plane pair `(⟨ȳ,z̄⟩, ⟨ū_j,v̄_j⟩)`:

| role | which letter | must satisfy (certificate route) | must satisfy (bypass route) |
|---|---|---|---|
| pivot (class added to `ū_j`) | the letter of `[y,z]` lying **in** `W` | `χ = 1` **and** `ν'` unit | `ν'` unit only |
| compensated partner (absorbs `k·v̄_j`) | the `W`-disjoint letter | nothing (`χ(v_j) = 1`, `ν'(v_j) = 0`) | nothing |

So the earlier naive-Labute refutation ("pivot `b` has `χ = X⁻¹ ≠ 1`") was correct **for the
certificate route only**, and is **moot** under the bypass; the search agent's
recommendation ("standard form with `c` as the W-disjoint letter") aimed at the right letter
assignment but at a wall that isn't the binding one.  The binding wall is word shape:
`eichler-reduction-note.md`'s basis-independent analysis (every letter-degree even in every
basis; the reduced core's syllable counts — 6 σ / 4 x₁ / 2-but-degree-−4 x₀, and 9
x₀-syllables in the `(w,x,t)`-basis — against HM2's exactly-2-with-degrees-±1) blocks the
`W·[y,z]·∏[u,v]` shape in every basis, independently of χ.  A CoV cannot transport the M/N
Proposition; what a CoV *would* buy is exactly what the widened seed search below buys
directly.

**Route 3 (corrected interface).**  Landed.  `SqNuSeed h j k` = `SqEichlerSeed h c j k` with

* the four χ-fields **deleted** (`chi_beta1/beta0/beta2/rho`) — the composed *realization*
  (not certificate) consumes no χ-clause;
* the three ν-fields' hypothesis **widened** from "`v_j`-row vanishes" to "`v_j`-row
  vanishes **and** `ν'(σ) = 1` **and** `ν'(x₀) = 0`" — legitimate because the clearing recipe
  only ever applies moves to markings carrying the P3-selected rows (which every composed
  stage preserves);
* `nu_rho`'s target changed from `k·ν'(σx₀^{−c})` to the bare `k` — the σ-pivot: at the
  selected rows the old pivot row is `1` for every `c`, so **the exponent parameter `c` has
  dissolved** from the residual interface (with it, the whole `sqPivotExp`-normalisation
  constraint of `HandleMixFixesCore` §3).

`HandleMixFixesCore` §2's refutation does not touch the new target: its witness has
`ν'(σ) = c₀ ≠ 1` (fails the new hypothesis), and its contradiction consumes the χ-clause
essentially (`χ_sq(Ψ⁻¹u₀) = 1` comes from the deleted field).  The mod-2 isometry check also
passes: `ν̄' = σ̄* + Σ(t̄_j ū_j* + s̄_j v̄_j*)` and `ν̄_sq = σ̄*` have the same cup-square
(`q` is linear on `H¹` in char 2; both values `0`) and the same characteristic-vector
pairing, so no `𝔽₂`-level obstruction separates them.

## The χ-free class-2 balance (the widened ansatz; supersedes the pinned table)

Same sites as `eichler-reduction-note.md` (they depend on the word, not the ansatz).  The
ν-fields now force only the σ̄- and ū-components of the correction classes:

```
β̄₁ = a₁v̄ + p₁x̄₀ + q₁x̄₁ ,   β̄₀ = a₀v̄ + p₀x̄₀ + q₀x̄₁ ,   β̄₂ = 2β̄₀ + λt̄ (forced row) ,
ρ̄  = k σ̄ + a_ρv̄ + p_ρx̄₀ + q_ρx̄₁            (t̄ = x̄₁ − 2x̄₀ ;  no σ̄-, no ū-components else)
```

Balance coordinates (relations available: the relator's quadratic form and `2[t̄, ḡ] ≡ 0`,
multipliers `m` on `2[t̄,v̄]`, `m'` on `2[t̄,σ̄]`, `m''` on `2[t̄,x̄₀]`/`2[t̄,x̄₁]`):

```
[v̄,σ̄]  : −a₀ − k = 0                        (unchanged: the x₀-slot still moves by −k·v̄)
[v̄,x̄₀] : a₁ + 10a₀ − p_ρ + 4m = 0           (p_ρ replaces the old forced −kc)
[v̄,x̄₁] : −8a₀ + a₂ − q_ρ − 2m = 0
[x̄₀,σ̄] : −p₀ − 4m' = 0                      (new coordinate, new freedom)
[x̄₁,σ̄] : −q₀ + 2m' = 0                      (new coordinate)
[x̄₁,x̄₀]: q₁ + 10q₀ + 8p₀ − p₂ + 2m'' + … = 0 (absorbable by p₂)
degree  : −4β̄₀ + 2β̄₂ ∈ ℤ₂·2t̄               (the forced row; not a constraint)
```

The pinned system had a **unique** first-order solution; the widened system is
**underdetermined** with ≥ 8 free first-order parameters (`p₀ = −4m'`, `q₀ = 2m'`, `p₁`,
`q₁`, `λ`, `p_ρ`, `q_ρ`, `a_ρ`, `m`, `m'`, `m''`).  The weight-4 obstruction was a 29-codim
miss (span 146/175) *inside the 0-parameter family*; the re-run should search the widened
family.  Note the qualitative change: `p₀, q₀ ≠ 0` mean the σ- and x₀-slot corrections may
now carry `x̄₀`/`x̄₁`-dressing whose class-2 damage lands in the previously untouchable
`[x̄₀,σ̄]`/`[x̄₁,σ̄]`-coordinates and is paid by the torsion relation `2[t̄,σ̄]` — a mechanism
entirely invisible to the χ-pinned ansatz.

## The residual search (retargeted recommendation)

Target `SqNuSeed 1 0 1` first (unit slice suffices: `sqNuClearHypothesis_of_unit_seeds`).
Harness as in `eichler-reduction-note.md` (`~/claude/general_2adic/dyadic_search`, that repo
otherwise untouched), with these changes:

1. **drop the χ-side filters entirely** (no `chi_*` targets; the t-torsion class with
   `χ(t) = −1` is now *allowed* in every slot);
2. ν-filters: β-slots must have zero σ̄- and ū-coordinates (x̄₀-, x̄₁-, v̄-coordinates free);
   ρ must have σ̄-coordinate exactly `k` and ū-coordinate `0`;
3. impose the widened class-2 solution above as the leading-order gate, with the free
   parameters swept;
4. target identity unchanged (`sqRelWord`-level, mod `⟨⟨R⟩⟩` is enough for the Lean
   interface) plus Nielsen invertibility.

On success, one `SqNuSeed` per `(j, k unit)` closes, via
`sqNuClearHypothesis_of_unit_seeds → markedCoreRealization_of_supply →` the
`KExactSupplyRN` pro-2 block, with no new axiom.  On failure with the widened family, the
obstruction becomes basis-free evidence that `SqNuClearHypothesis` itself needs a
non-substitution device (e.g. a two-handle composite), and the next escalation is a
refutation attempt against `SqNuClearHypothesis 1` directly — which, unlike the χ-pinned
statement, no currently known witness refutes.

## Status ledger

| statement | status |
|---|---|
| `ztwoIota_lNu` (the `hnuP` bridge) | **theorem**, std-3 |
| bypass `supply + SqNuClearHypothesis → MarkedCoreRealization (DSq h) (lNu h)` | **theorem**, std-3 |
| converse `realization → SqNuForwardSupply` (interface exactness) | **theorem**, std-3 |
| `SqNuClearHypothesis 0` | **theorem** (rank-three: no binder at all) |
| `SqNuClearHypothesis h` from any of `fixesCore`/`Eichler`/`SqEichlerSeed`s | **theorems** (pricing; old lane subsumed) |
| `SqNuClearHypothesis h`, `h ≥ 1`, unconditionally | **open** — the retargeted seed search |
