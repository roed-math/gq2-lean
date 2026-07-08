# P-17b3 — the (144) correspondence ⟹ `terminal_count_eq`  (design + status)

> **STATUS: ☑ DONE (Opus 2026-07-06).**  `terminal_count_eq` is fully proved, std-3, sorry-free
> (`GQ2/SectionNine.lean`; library green 8671, gate census 15; `#print axioms terminal_count_eq`
> = `[propext, Classical.choice, Quot.sound]` exactly).  **The final proof took a simpler route
> than the "(B)" plan below** — the KEY lemma `head_factors_through_nuT` and the `Zhat.zpowHat`/φ
> construction were **avoided entirely**.  Instead, source-independence of the H-condition rides
> the **surjectivity of `b`** onto `∂bd` (+ `compat*`, `nuT`/`nuTwo`-surjectivity): given `b`
> surjective, the per-γ condition `λ(g̃(pro2 γ)) = κ(F.α(bγ).1)` is *equivalent* to the source-free
> condition `∀ x∈∂bd, λ(g̃ x.2) = κ(F.α x.1)`, so both sources' Q-counts biject with the same
> `CommonLifts` set on `Π`.  Landed lemmas: **(A)** `boundaryLifts_equiv_qlifts`, **(B)**
> `qlifts_equiv_commonLifts` (via `compPro2Equiv`/`pro2Iso` = `maxProPHomEquiv` transported) +
> `CommonLifts`, and `ker_pro2A` (from `prop_3_10_gammaA` + `topGen_gammaA`).  **B3c/B8 confirmed
> unneeded.**  Two mild deviations: `terminal_count_eq` gained `[CompactSpace AbsGalQ2]
> [TotallyDisconnectedSpace AbsGalQ2]` (codebase convention), and `SectionNine` imports
> `GQ2.SectionThreeMarked`.  The design below is retained for the record.

Companion to the P-17b3 infrastructure in [`GQ2/SectionNine.lean`](../GQ2/SectionNine.lean).
Goal: prove
```
terminal_count_eq : exactImageCount B.bA F T = exactImageCount B.bF F T
```
for a terminal marked target (`hstack : IsScalarStack T.LY`).

## Landed (Opus 2026-07-06, all std-3, sorry-free, in `SectionNine.lean`)

* **`odd_subgroup_le_ker_of_expTwo`** — a hom to an exponent-2 group kills any odd normal
  subgroup.  (This is where `hE2` enters: `θ_Y` descends to `Q`.)
* **`odd_mem_of_pTwo_quotient`** — an odd-order element dies in a 2-group quotient.
* **`cyclic_two_quotient_of_tame`** — `H/M` is **cyclic** when `H = ⟨s,t | s⁻¹ t s = t²⟩` and
  `H/M` is a 2-group (`t` odd ⟹ `t ∈ M` ⟹ `H/M = ⟨s̄⟩`).  *The engine of source-independence.*
* **`L92`** — a bundle of the `lemma_9_2_core` outputs (`piY, L, M, Ñ, …`), with:
  * `L92.lamQ : Q ↠ H/M` (the lower fibre map `λ`), `lamQ_mk`, `lamQ_surjective`;
  * `L92.fibreSub : Subgroup (H × Q)` (`{(h,q) | κ h = λ q}`), `toFibre`, injectivity,
    **`toFibre_surjective`** (via `coprime_fiber_product`);
  * **`L92.fibreMulEquiv : Y ≃* fibreSub`** (Lemma 9.2's `Y ≅ H ×_{H₂} Q`, eq. (143));
  * **`L92.thetaBarQ`** — `θ_Y` descended to `Q →* E`.

Plumbing verified: inside `terminal_count_eq` the bundle `D : L92 H Y` is built directly from
`head_two_nilpotent F` (gives `M = O²H`) + `lemma_9_2_core …` (gives `Ñ` and all fields).

## Remaining — two pieces

Write `Q := D.Q`, `κ := mk' D.M`, `λ := D.lamQ`, `θ̄ := D.thetaBarQ T.thetaY hE2`.  For a source
`Γ` with boundary map `b : Γ → ∂bd`, note `(b γ).1` is the **tame** component and `(b γ).2` the
**pro-2** component, and `F.frameMap (b γ) = (F.alpha (b γ).1, F.psiBar (b γ).2)`.  Define the
source-parametrised **Q-count set**
```
QLifts Γ b := { g : ContSurj Γ Q //
    (∀ γ, λ (g γ) = κ (F.alpha (b γ).1)) ∧ (∀ γ, θ̄ (g γ) = F.psiBar (b γ).2) }.
```

### (A) `Nat.card (BoundaryLifts b F T) = Nat.card (QLifts Γ b)`  — source-generic

An `Equiv BoundaryLifts (QLifts Γ b)`:

* **Forward** `f ↦ (quotientMk Ñ).comp f.1`.  Surjective (comp of surjections).  Conditions
  from `IsBoundaryLift`: `λ(mk (f γ)) = κ(π_Y(f γ)) = κ(F.alpha (b γ).1)` (`lamQ_mk`, boundary
  eqn's H-part); `θ̄(mk (f γ)) = θ_Y(f γ) = F.psiBar (b γ).2` (`thetaBarQ_mk`, θ-part).
* **Backward** `g ↦ f` where `f γ := D.fibreMulEquiv.symm ⟨(F.alpha (b γ).1, g γ), hmem γ⟩`,
  `hmem γ` from condition 1 (`(F.alpha (b γ).1, g γ) ∈ fibreSub ↔ κ(F.alpha (b γ).1) = λ(g γ)`).
  Build `f` as a `ContinuousMonoidHom` = `fibreMulEquiv.symm ∘ ((h-hom).prod g).codRestrict`,
  where `h-hom γ = F.alpha (b γ).1` (continuous: `F.alpha ∘ fst ∘ ∂bd.subtype ∘ b`); continuity
  is otherwise free (`Y, Q, H` finite discrete).
  * **Surjectivity of `f`** = surjectivity of `((h-hom).prod g).codRestrict fibreSub` onto
    `fibreSub` — a **second `coprime_fiber_product`** (same shape as `toFibre_surjective`), whose
    two projection-surjectivities are: `h-hom` onto `H` (needs `(b·).1` onto `Ttame`, from
    `b` onto `∂bd` (`surjA`/`surjF`) + `fst(∂bd) = ⊤` via `nuTwo` surjective, then `F.alpha`
    onto `H`), and `g` onto `Q` (given).
* `left_inv`/`right_inv`: both reduce to `fibreMulEquiv`'s round-trips + `Subtype.ext`.

No source-specific axioms here.

### (B) `Nat.card (QLifts GammaA B.bA) = Nat.card (QLifts AbsGalQ2 B.bF)`  — source-independence

`Q` is a finite 2-group (pro-2).  A `g : ContSurj Γ Q` factors through the **maximal pro-2
quotient** `Γ ↠ Π` (`ker (pro2ₓ) = proPKernel` — for `G_ℚ₂` this is `ker_pro2F`; for `Γ_A` it is
`prop_3_10_gammaA`, i.e. `pro2A = e_A ∘ maxProPMk`).  So `QLifts Γ b ≃ { g̃ : Π ↠ Q // Cᴴ ∧ Cᴱ }`
where the two conditions transport to `Π`:

* **θ-condition** `θ̄ ∘ g̃ = F.psiBar` — **already source-independent** (both `θ̄, F.psiBar` are on
  `Π`/`Q`; and `(b γ).2 = pro2ₓ γ` *literally*, since `bA g = (tameA g, pro2A g)`).
* **H₂-condition** `λ ∘ g̃ = α₂` where `α₂ : Π → H/M` is the factoring of
  `κ ∘ F.alpha ∘ (b·).1` through `pro2ₓ`.  **Source-independence of `α₂`** is the only content:
  `α₂` agrees on the topological generators `piSigma, piX0, piX1` because
  **`κ ∘ F.alpha : Ttame → H/M` factors through `ν_t = nuT`** (KEY LEMMA, below), so on any
  `g` with `pro2ₓ g = π`, `α₂ π = κ(F.alpha (tameₓ g)) = φ(nuT (tameₓ g)) = φ(nuTwo (pro2ₓ g))
  = φ(nuTwo π)` — *manifestly independent of the source* (uses `compatA`/`compatF`:
  `nuT ∘ tameₓ = nuTwo ∘ pro2ₓ`, and `nuTwo`-values `nuTwo piSigma = ztwoOne`,
  `nuTwo piX0 = nuTwo piX1 = 1`).

**KEY LEMMA `head_factors_through_nuT`**: `∃ φ : ContinuousMonoidHom Ztwo (H/M)`,
`(mk' M).comp F.alpha = φ.comp nuT` (equivalently `ker nuT ≤ ker (mk' M ∘ F.alpha)`).
*Proof*: `H/M` is cyclic (`cyclic_two_quotient_of_tame`, generators `s = α σ, t = α τ`), so
`c := mk' M (F.alpha tameSigma)` generates it.  Build `φ` via the `Zhat` universal property
(`GQ2.Zhat.zpowHat`, `map_zpowHat`): `ψ : Zhat → H/M`, `ofInt 1 ↦ c`, then factor through
`maxProPMk` (`H/M` pro-2, `proPKernel_le_ker`) to get `φ : Ztwo = maxProPQuotient 2 Zhat → H/M`
with `φ ztwoOne = c`.  Check `φ ∘ nuT = mk' M ∘ F.alpha` on the topological generators `σ, τ` of
`Ttame` (`topGen_ttame`): `σ ↦ φ(nuT tameSigma) = φ ztwoOne = c = mk' M (F.alpha tameSigma)` (✓);
`τ ↦ φ(nuT tameTau) = φ 1 = 1 = mk' M (F.alpha tameTau)` (✓, `tameTau` odd ⟹
`odd_mem_of_pTwo_quotient`).  Agreement on generators + T2 target ⟹ equal.  *This is the only
remaining nontrivial construction; it needs the `ProfiniteGrp`/`zpowHat` API but no marked iso.*

The `Nat.card`-equality then follows from the composite equivalences to the **common** set
`{ g̃ : Π ↠ Q // λ ∘ g̃ = α₂ ∧ θ̄ ∘ g̃ = F.psiBar }` (source-independent), via `Nat.card_congr`.

## Axiom note

**B3c/B8 are likely NOT needed** (the ticket's Ax column overestimates): source-independence
routes through `nuT` + `compatA`/`compatF` (BoundaryMaps fields, axiom-free) + `prop_3_10_gammaA`
(P-09; check its `#print axioms`) — **not** `prop_3_10_local_marked` (the B3c/B8 carrier).  Confirm
by `#print axioms terminal_count_eq` once closed; downgrade the Ax column if clean.

## Effort estimate

(A) ≈ 120–160 lines (2× `coprime_fiber_product`, continuity plumbing, the `Equiv`).
(B) key lemma ≈ 60–90 lines (`zpowHat`/`ProfiniteGrp` plumbing) + ≈ 60 lines assembly.
