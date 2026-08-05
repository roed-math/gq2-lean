/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.LabuteInterface
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldCore

/-!
# P3 — the pivot `ν`-row of the `L_sq` certificate: joint `(χ, ν)` selection

`marked_matching_certificate_KTwoSq` (`GQ2/Dyadic/LabuteInterface.lean`) needs, beyond an
oriented equivalence `f : D_sq(h) ≃ₜ* G_K(2)`, the **pivot row**
`ν(f w) = 1`, `w = σ·x₀^{−c}`; in the one-binder (`fixesCore`) variant it needs the pair
`ν(f σ) = 1`, `ν(f x₀) = 0`.  The forward-generator table
(`SqCyclotomicForwardGeneratorData`) pins `χ`-values only.  This file settles which of the two
possible routes is the true one and proves the arithmetic of the surviving route.

## Design verdict: the row must be **selected**, not derived

* **Route (b) — "`d = ν(f w) = 1` is forced invariantly" — is FALSE.**  §5 exhibits a marking
  `ν_tw` of the very same core `D_sq(h)`, with the very same `χ_sq`, which satisfies *every*
  clause the marked-reciprocity bundle supplies about `ν` — it is surjective, its restriction to
  `ker χ` is already onto `ℤ₂` (the level-zero clause `nu_ker_chi_ge` at `r = 0`), and it has the
  *same kernel* as `ν_sq`, so every kernel-shaped clause (`ki_unramified`) reads identically —
  and whose pivot row is `−1`.  Indeed `ν_tw = ν_sq⁻¹`, i.e. `ν_tw` differs from the standard
  marking by an automorphism of the target `Multiplicative ℤ₂`.  Since the abstract marked-pair
  interface `(χ, ν, r)` is stable under such automorphisms, **no** theorem of the shape
  "oriented equivalence + marked interface ⟹ `ν(f w) = 1`" can exist.  The exact row `= 1` (as
  opposed to `IsUnit`) is a *normalization* condition: the only clause in `MarkedRecip` that
  normalizes the scale of `ν` is `nu_ur_recip_uniformizer` (`ν(recip π) = −1`), which is a
  statement about a *chosen* element, not an invariant of the equivalence.
* **Route (a) — `ν`-refine the generator selection — is the true one**, and §1–§4 prove its
  arithmetic:
  1. **Joint realization** (§1, `exists_chiCycKTwo_eq_and_nuUrKTwo_eq`): for odd-degree `K` at
     level `r = 0` the pair `(χ, ν) : G_K(2) → ℤ₂ˣ × ℤ₂` is **jointly surjective**.  So the
     `(χ, ν)`-values needed by the improved table are unobstructed: every joint value occurs,
     and in particular `(S, 1)`, `(X, 0)`, `(Y, 0)` are simultaneously realizable (§3).
  2. **Frattini-coset `ν`-adjustment** (§2, `exists_squareShift_nuUrKTwo_eq`): a generator may be
     replaced by `q·g²` with `χ g = 1`, which fixes the `χ`-value on the nose, keeps the
     Frattini class (a square lies in `Q²`), and shifts the `ν`-value by an *arbitrary* element
     of `2ℤ₂`.  Hence the **exact** rows `ν(σ) = 1`, `ν(x₀) = 0` reduce to their **mod-2**
     shadows, which is the form the Frattini frame can see: `ν mod 2` is a coordinate of
     `H¹(G_K(2), 𝔽₂)`, so the two mod-2 rows say exactly that the unramified class `ν̄` pairs as
     `ν̄(σ̄) = 1`, `ν̄(x̄₀) = 0` against the frame's dual basis.
  3. **The adapter** (§4): a table-matched oriented equivalence yields the certificate, and —
     the sharp part — the two `ν`-rows are **necessary** as well as sufficient
     (`sqMarkedForwardSupply_of_certificate`): every `MarkedCoreCertificateKTwoSq` produces an
     oriented equivalence carrying them.  So `SqMarkedForwardSupply` is *exactly* the residual
     obligation of the adapter package; there is no cleverer interface that avoids it.

## What is *not* proved here (the residual, and why it is frame-level)

The frame construction (`GammaLSylowPreimageFieldLabuteFrattiniFrame.lean` §4–§6) chooses the
generators as the dual family of a Witt-adapted basis of `H¹(G_K(2), 𝔽₂)` for the cup form, with
the `⟨1⟩` slot at `κ = [−1]` and the first hyperbolic plane `(ε₀, ε₁)` split so that
`ε₀ + ε₁ = τ = [2]`, and only then lifts each representative to the exact `ℤ₂ˣ`-value inside its
Frattini coset.  It never looks at `ν`.  Item 2 above says the *exact* `ν`-rows cost nothing once
the *mod-2* rows hold, and the mod-2 rows are exactly a constraint on where `ν̄ = [u]` (`u` the
unramified unit) sits in that adapted basis.  Two remarks, recorded for the frame ticket:

* the hyperbolic splitting is free in `w'` (any `w'` with `b τ w' = 1`), which is precisely the
  freedom needed to move `ν̄` into the `ε₀`-slot;
* **the ramified-`i` hypothesis is what makes this possible**: `ν̄ ∈ span{κ, τ}` would mean
  `[u] ∈ {[1], [−1], [2], [−2]}`, i.e. `K(√u) = K(i)` (excluded by ramified-`i`, since `K(√u)/K`
  is unramified) or `K(√u) = K(√±2)` (excluded because `v(2) = e(K/ℚ₂)` is odd in odd degree, so
  `K(√±2)/K` is ramified).  So for an odd-degree ramified-`i` field `ν̄` is a genuinely
  independent direction and the mod-2 rows are not obstructed.

Formalizing that placement means editing the frame, which this package does not own; the
selection is therefore packaged as the `def`-shaped `SqMarkedForwardSupply` (never an axiom),
proved to be exactly equivalent to what the certificate consumes.

## Axioms

Every declaration prints **std-3** plus whatever the odd-degree cyclotomic surjectivity input
carries; the `#print axioms` block at the end of the file is the record.  No `sorry`, no new
axiom, no `native_decide`.
-/

namespace GQ2.Dyadic.LSquare

open GQ2 GQ2.Dyadic SqCore MarkedCore Multiplicative

noncomputable section

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section JointValues

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-! ## §1 Joint `(χ, ν)` values on `G_K(2)`

The two clauses that enter are the level clause `nu_ker_chi_ge` of the marked bundle (at the
type-`L` level `r = 0`) and odd-degree cyclotomic surjectivity.  Together they make the pair
`(χ, ν)` jointly surjective: `χ` alone realizes any unit, and the level clause then corrects the
`ν`-value inside `ker χ` without disturbing it. -/

/-- **The level-zero clause on `G_K(2)`**: at `r = 0` every `2`-adic value of the unramified
character is realized on the cyclotomic kernel of the maximal pro-`2` quotient. -/
theorem exists_chiCycKTwo_eq_one_and_nuUrKTwo_eq (B : MarkedRecip R K) (hr : B.r = 0)
    (y : ℤ_[2]) :
    ∃ q : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) q = 1 ∧ nuUrKTwo B q = ofAdd y := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge y
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  refine ⟨maxProPMk 2 (GalK K) g, ?_, ?_⟩
  · rw [chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK]
    exact hgchi
  · refine Multiplicative.toAdd.injective ?_
    rw [nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul, toAdd_ofAdd]

/-- **Joint realization** — the genuinely arithmetic content of P3.  For an odd-degree field at
the type-`L` level `r = 0` the pair `(χ, ν) : G_K(2) → ℤ₂ˣ × ℤ₂` is jointly surjective: the
cyclotomic row and the unramified row of a generator may be prescribed *independently*.

This is what licenses the `ν`-refinement of the improved constructor table: the possible
`(χ, ν)` joint values on an odd-degree ramified-`i` field are *all* of `ℤ₂ˣ × ℤ₂`. -/
theorem exists_chiCycKTwo_eq_and_nuUrKTwo_eq (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) (u : ℤ_[2]ˣ) (y : ℤ_[2]) :
    ∃ q : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) q = u ∧ nuUrKTwo B q = ofAdd y := by
  obtain ⟨k, hk⟩ := chiCycKTwo_surjective_of_odd_finrank K B hodd u
  obtain ⟨q, hqchi, hqnu⟩ :=
    exists_chiCycKTwo_eq_one_and_nuUrKTwo_eq B hr (y - toAdd (nuUrKTwo B k))
  refine ⟨k * q, ?_, ?_⟩
  · rw [map_mul, hk, hqchi, mul_one]
  · refine Multiplicative.toAdd.injective ?_
    rw [map_mul, hqnu, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
    ring

/-! ## §2 The Frattini-coset `ν`-adjustment

A square `g²` with `χ g = 1` lies in `Q²·[Q, Q] = Φ(Q)` and has `χ`-value `1` on the nose, so
multiplying a generator by it changes neither its `χ`-value nor its Frattini class (hence neither
the exact cyclotomic row nor topological generation).  By §1 its `ν`-value ranges over all of
`2ℤ₂`.  Consequently the **exact** rows `ν(σ) = 1`, `ν(x₀) = 0` cost nothing beyond their
**mod-2** shadows. -/

/-- Squares of `χ`-trivial elements realize every value of `2ℤ₂` on the unramified character,
with `χ`-value `1`. -/
theorem exists_sq_chiCycKTwo_eq_one_and_nuUrKTwo_eq (B : MarkedRecip R K) (hr : B.r = 0)
    (m : ℤ_[2]) :
    ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) (g * g) = 1 ∧ nuUrKTwo B (g * g) = ofAdd (2 * m) := by
  obtain ⟨g, hgchi, hgnu⟩ := exists_chiCycKTwo_eq_one_and_nuUrKTwo_eq B hr m
  refine ⟨g, by rw [map_mul, hgchi, one_mul], ?_⟩
  refine Multiplicative.toAdd.injective ?_
  rw [map_mul, hgnu, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd]
  ring

/-- **The Frattini-coset `ν`-adjustment.**  Replacing `q` by `q·g²` with `χ g = 1` preserves the
exact cyclotomic value and the Frattini class, and shifts the unramified value by any prescribed
element of `2ℤ₂`. -/
theorem exists_squareShift_nuUrKTwo_shift (B : MarkedRecip R K) (hr : B.r = 0)
    (q : maxProPQuotient 2 (GalK K)) (m : ℤ_[2]) :
    ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) (q * (g * g)) = chiCycKTwo (K := K) q ∧
        nuUrKTwo B (q * (g * g)) = nuUrKTwo B q * ofAdd (2 * m) := by
  obtain ⟨g, hgchi, hgnu⟩ := exists_sq_chiCycKTwo_eq_one_and_nuUrKTwo_eq B hr m
  exact ⟨g, by rw [map_mul, hgchi, mul_one], by rw [map_mul, hgnu]⟩

/-- The adjustment in target form: any `ν`-value congruent to the current one modulo `2` is
reachable inside the Frattini coset, at no cost to the cyclotomic row. -/
theorem exists_squareShift_nuUrKTwo_eq (B : MarkedRecip R K) (hr : B.r = 0)
    (q : maxProPQuotient 2 (GalK K)) (y m : ℤ_[2])
    (hm : y = toAdd (nuUrKTwo B q) + 2 * m) :
    ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) (q * (g * g)) = chiCycKTwo (K := K) q ∧
        nuUrKTwo B (q * (g * g)) = ofAdd y := by
  obtain ⟨g, hgchi, hgnu⟩ := exists_squareShift_nuUrKTwo_shift B hr q m
  refine ⟨g, hgchi, ?_⟩
  refine Multiplicative.toAdd.injective ?_
  rw [hgnu, toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, hm]

/-- **Exact `σ`-row from its mod-2 shadow**: a generator whose unramified value is a *unit* can
be moved inside its Frattini coset, without touching its cyclotomic value, to one whose
unramified value is exactly `1`. -/
theorem exists_squareShift_nuUrKTwo_eq_one (B : MarkedRecip R K) (hr : B.r = 0)
    (q : maxProPQuotient 2 (GalK K)) (hq : IsUnit (toAdd (nuUrKTwo B q))) :
    ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) (q * (g * g)) = chiCycKTwo (K := K) q ∧
        nuUrKTwo B (q * (g * g)) = ofAdd (1 : ℤ_[2]) := by
  obtain ⟨v, hv⟩ := hq
  obtain ⟨m, hmv⟩ := two_dvd_val_sub_one v
  refine exists_squareShift_nuUrKTwo_eq B hr q 1 (-m) ?_
  rw [← hv]
  linear_combination -hmv

/-- **Exact `x₀`-row from its mod-2 shadow**: a generator whose unramified value is even can be
moved inside its Frattini coset, without touching its cyclotomic value, to one whose unramified
value is exactly `0`. -/
theorem exists_squareShift_nuUrKTwo_eq_zero (B : MarkedRecip R K) (hr : B.r = 0)
    (q : maxProPQuotient 2 (GalK K)) (m : ℤ_[2]) (hq : toAdd (nuUrKTwo B q) = 2 * m) :
    ∃ g : maxProPQuotient 2 (GalK K),
      chiCycKTwo (K := K) (q * (g * g)) = chiCycKTwo (K := K) q ∧
        nuUrKTwo B (q * (g * g)) = ofAdd (0 : ℤ_[2]) := by
  refine exists_squareShift_nuUrKTwo_eq B hr q 0 (-m) ?_
  rw [hq]
  ring

end JointValues

/-! ## §3 The `ν`-refined constructor table

`OddDegreeGalKSqCyclotomicCoreTable` (`GammaLSylowPreimageFieldCore.lean`) records three elements
of `G_K(2)` carrying the three exceptional cyclotomic rows `(S, X, Y)` of the improved square
presentation.  Joint realization upgrades it to carry the unramified rows `(1, 0, 0)` as well —
the rows the `L_sq` certificate's pivot clause needs.  The `x₁`-row `ν(x₁) = 0` is not an extra
demand: it is the value forced by `ν(x₁) = 2ν(x₀)` on any relator-killing tuple
(`SqCore.toAdd_nu_dsqX1`). -/

section MarkedTable

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The `ν`-refined constructor table**: the improved square presentation's three exceptional
cyclotomic rows *together with* the unramified rows the pivot clause consumes. -/
structure OddDegreeGalKSqMarkedCoreTable (K : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (B : MarkedRecip R K) extends OddDegreeGalKSqCyclotomicCoreTable K where
  /-- The `σ`-row of the marking: `ν(σ) = 1`. -/
  nu_sigma : nuUrKTwo B sigma = ofAdd (1 : ℤ_[2])
  /-- The `x₀`-row of the marking: `ν(x₀) = 0`. -/
  nu_x0 : nuUrKTwo B x0 = ofAdd (0 : ℤ_[2])
  /-- The `x₁`-row of the marking: `ν(x₁) = 0` (forced on any relator-killing tuple). -/
  nu_x1 : nuUrKTwo B x1 = ofAdd (0 : ℤ_[2])

/-- **The `ν`-refined table exists** for every odd-degree field at the type-`L` level `r = 0`:
the joint `(χ, ν)`-values `(S, 1)`, `(X, 0)`, `(Y, 0)` are simultaneously realizable.  This is
the element-level statement that route (a) is unobstructed. -/
def oddDegreeGalKSqMarkedCoreTable (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) :
    OddDegreeGalKSqMarkedCoreTable K B :=
  let hS := exists_chiCycKTwo_eq_and_nuUrKTwo_eq B hodd hr GQ2.Roe.SvalUnit 1
  let hX := exists_chiCycKTwo_eq_and_nuUrKTwo_eq B hodd hr GQ2.Roe.rootXUnit 0
  let hY := exists_chiCycKTwo_eq_and_nuUrKTwo_eq B hodd hr GQ2.Roe.YvalUnit 0
  { sigma := hS.choose
    x0 := hX.choose
    x1 := hY.choose
    sigma_value := hS.choose_spec.1
    x0_value := hX.choose_spec.1
    x1_value := hY.choose_spec.1
    nu_sigma := hS.choose_spec.2
    nu_x0 := hX.choose_spec.2
    nu_x1 := hY.choose_spec.2 }

/-- **From mod-2 rows to the refined table** — the form the frame ticket consumes.  A plain
cyclotomic table whose three unramified rows have the right *parities* (`ν(σ)` a unit, `ν(x₀)`
and `ν(x₁)` even) upgrades to a fully `ν`-refined table by moving each element inside its own
Frattini coset.  Nothing else about the elements changes: the replacement multiplies by a square
of a `χ`-trivial element, so the exact cyclotomic rows are preserved on the nose and the Frattini
classes — hence topological generation — are untouched.

The parities are exactly what the Frattini frame can see: `ν mod 2` is a coordinate functional on
`H¹(G_K(2), 𝔽₂)`, so the three parity clauses say where the unramified class `ν̄` sits against
the frame's dual basis.  Whether the relator survives the replacement is the frame's business,
not this file's. -/
def OddDegreeGalKSqCyclotomicCoreTable.toMarkedOfParities (B : MarkedRecip R K) (hr : B.r = 0)
    (T : OddDegreeGalKSqCyclotomicCoreTable K)
    (hsigma : IsUnit (toAdd (nuUrKTwo B T.sigma)))
    (hx0 : ∃ m : ℤ_[2], toAdd (nuUrKTwo B T.x0) = 2 * m)
    (hx1 : ∃ m : ℤ_[2], toAdd (nuUrKTwo B T.x1) = 2 * m) :
    OddDegreeGalKSqMarkedCoreTable K B :=
  let hS := exists_squareShift_nuUrKTwo_eq_one B hr T.sigma hsigma
  let hX := exists_squareShift_nuUrKTwo_eq_zero B hr T.x0 hx0.choose hx0.choose_spec
  let hY := exists_squareShift_nuUrKTwo_eq_zero B hr T.x1 hx1.choose hx1.choose_spec
  { sigma := T.sigma * (hS.choose * hS.choose)
    x0 := T.x0 * (hX.choose * hX.choose)
    x1 := T.x1 * (hY.choose * hY.choose)
    sigma_value := hS.choose_spec.1.trans T.sigma_value
    x0_value := hX.choose_spec.1.trans T.x0_value
    x1_value := hY.choose_spec.1.trans T.x1_value
    nu_sigma := hS.choose_spec.2
    nu_x0 := hX.choose_spec.2
    nu_x1 := hY.choose_spec.2 }

/-- Regression: the refined table still carries the literal improved cyclotomic rows. -/
theorem oddDegreeGalKSqMarkedCoreTable_chi (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) :
    let T := oddDegreeGalKSqMarkedCoreTable B hodd hr
    chiCycKTwo (K := K) T.sigma = GQ2.Roe.SvalUnit ∧
      chiCycKTwo (K := K) T.x0 = GQ2.Roe.rootXUnit ∧
      chiCycKTwo (K := K) T.x1 = GQ2.Roe.YvalUnit :=
  ⟨(oddDegreeGalKSqMarkedCoreTable B hodd hr).sigma_value,
    (oddDegreeGalKSqMarkedCoreTable B hodd hr).x0_value,
    (oddDegreeGalKSqMarkedCoreTable B hodd hr).x1_value⟩

/-- Regression: the refined table carries the unramified rows `(1, 0, 0)`. -/
theorem oddDegreeGalKSqMarkedCoreTable_nu (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) :
    let T := oddDegreeGalKSqMarkedCoreTable B hodd hr
    nuUrKTwo B T.sigma = ofAdd (1 : ℤ_[2]) ∧
      nuUrKTwo B T.x0 = ofAdd (0 : ℤ_[2]) ∧ nuUrKTwo B T.x1 = ofAdd (0 : ℤ_[2]) :=
  ⟨(oddDegreeGalKSqMarkedCoreTable B hodd hr).nu_sigma,
    (oddDegreeGalKSqMarkedCoreTable B hodd hr).nu_x0,
    (oddDegreeGalKSqMarkedCoreTable B hodd hr).nu_x1⟩

end MarkedTable

/-! ## §4 The adapter: the two `ν`-rows are exactly what the certificate needs -/

section Adapter

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The marking of the `L_sq` core transported through a `K`-side equivalence. -/
def transportedNuUr (B : MarkedRecip R K) {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) where
  toFun := fun x ↦ nuUrKTwo B (f x)
  map_one' := by rw [map_one, map_one]
  map_mul' := fun x y ↦ by rw [map_mul, map_mul]
  continuous_toFun := (nuUrKTwo B).continuous_toFun.comp f.continuous_toFun

@[simp] theorem transportedNuUr_apply (B : MarkedRecip R K) {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (x : (DSq h : Type)) : transportedNuUr B f x = nuUrKTwo B (f x) := rfl

/-- **The pivot row from the two core rows**: `ν(f w) = ν(f σ) − c·ν(f x₀)`, so the marked-data
clause `ν(f w) = 1` of `marked_matching_certificate_KTwoSq` follows from `ν(f σ) = 1` and
`ν(f x₀) = 0`, at *every* exponent `c`. -/
theorem nuUrKTwo_sqMixPivotElem_eq_one (B : MarkedRecip R K) {h : ℕ}
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) (c : ℤ_[2])
    (hsigma : nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])) :
    nuUrKTwo B (f (sqMixPivotElem h c)) = ofAdd (1 : ℤ_[2]) := by
  refine Multiplicative.toAdd.injective ?_
  have hp := toAdd_nu_sqMixPivotElem (transportedNuUr B f) c
  rw [transportedNuUr_apply, transportedNuUr_apply, transportedNuUr_apply, hsigma, hx0,
    toAdd_ofAdd, toAdd_ofAdd, mul_zero, sub_zero] at hp
  rw [hp, toAdd_ofAdd]

/-- **The `L_sq` certificate over the two `ν`-rows** (shear route).  This is
`marked_matching_certificate_KTwoSq` with its arithmetic pivot clause replaced by the pair of
generator rows the refined constructor table supplies. -/
theorem marked_matching_certificate_KTwoSq_of_nuRows (B : MarkedRecip R K) (h : ℕ) (c : ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x)
    (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (hsigma : nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  marked_matching_certificate_KTwoSq B h c f horient hMix hShear
    (nuUrKTwo_sqMixPivotElem_eq_one B f c hsigma hx0)

/-- The same, at a table-matched equivalence: an oriented `f` whose two core generators *are* the
refined table's elements produces the certificate. -/
theorem marked_matching_certificate_KTwoSq_of_markedTable (B : MarkedRecip R K)
    (T : OddDegreeGalKSqMarkedCoreTable K B) (h : ℕ) (c : ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x)
    (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (hfsigma : f (dsqSigma h) = T.sigma) (hfx0 : f (dsqX0 h) = T.x0) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  marked_matching_certificate_KTwoSq_of_nuRows B h c f horient hMix hShear
    (by rw [hfsigma]; exact T.nu_sigma) (by rw [hfx0]; exact T.nu_x0)

/-- The table-matched one-binder route: with the strengthened (core-fixing) handle binder the
shear disappears and the refined table's two rows are the whole marked-data input. -/
theorem marked_matching_certificate_KTwoSq_of_fixesCore_markedTable (B : MarkedRecip R K)
    (T : OddDegreeGalKSqMarkedCoreTable K B) (h : ℕ) (c : ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x)
    (hMix : SqHandleMixFixesCore h c)
    (hfsigma : f (dsqSigma h) = T.sigma) (hfx0 : f (dsqX0 h) = T.x0) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  marked_matching_certificate_KTwoSq_of_fixesCore B h c f horient hMix
    (by rw [hfsigma]; exact T.nu_sigma) (by rw [hfx0]; exact T.nu_x0)

/-- **The residual obligation of the adapter package**, as a `def`-shaped `Prop` (never an
axiom): the forward presentation can be produced with its two core generators carrying the
standard unramified rows.  §5 shows this cannot be weakened to a consequence of orientation
alone, and `sqMarkedForwardSupply_of_certificate` below shows it cannot be weakened at all. -/
def SqMarkedForwardSupply (B : MarkedRecip R K) (h : ℕ) : Prop :=
  ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
    (∀ x, chiCycKTwo (K := K) (f x) = chiSq h x) ∧
      nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
      nuUrKTwo B (f (dsqX0 h)) = ofAdd (0 : ℤ_[2])

/-- **Sufficiency**: the marked supply plus the strengthened handle binder produces the
certificate, with no residual marked-data clause. -/
theorem marked_matching_certificate_KTwoSq_of_supply (B : MarkedRecip R K) (h : ℕ) (c : ℤ_[2])
    (hMix : SqHandleMixFixesCore h c) (H : SqMarkedForwardSupply B h) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) := by
  obtain ⟨f, horient, hsigma, hx0⟩ := H
  exact marked_matching_certificate_KTwoSq_of_fixesCore B h c f horient hMix hsigma hx0

/-- Sufficiency on the two-binder (shear) route. -/
theorem marked_matching_certificate_KTwoSq_of_supply_shear (B : MarkedRecip R K) (h : ℕ)
    (c : ℤ_[2]) (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (H : SqMarkedForwardSupply B h) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) := by
  obtain ⟨f, horient, hsigma, hx0⟩ := H
  exact marked_matching_certificate_KTwoSq_of_nuRows B h c f horient hMix hShear hsigma hx0

/-- **Necessity — the sharp form of the P3 verdict.**  A marked-core certificate *produces* an
oriented equivalence carrying both unramified rows: its corrected equivalence
`abstractEquiv ∘ correction` transports `ν` to `ν_sq`, whose `σ`- and `x₀`-rows are `1` and `0`.

Hence `SqMarkedForwardSupply` is not merely one sufficient interface among many: it is
*equivalent* to the certificate (given the handle binder), so the adapter package cannot dodge
the `ν`-selection by reshaping the certificate. -/
theorem sqMarkedForwardSupply_of_certificate (B : MarkedRecip R K) {h : ℕ}
    (C : MarkedCoreCertificateKTwoSq B h) : SqMarkedForwardSupply B h := by
  refine ⟨C.correction.trans C.abstractEquiv, fun x ↦ ?_, ?_, ?_⟩
  · exact (C.orientation (C.correction x)).trans (C.correction_chi x)
  · exact (C.correction_nu (dsqSigma h)).trans (nuSq_sigma h)
  · exact (C.correction_nu (dsqX0 h)).trans (nuSq_x0 h)

/-- The two directions packaged: under the strengthened handle binder the marked supply and the
certificate are interchangeable. -/
theorem sqMarkedForwardSupply_iff_nonempty_certificate (B : MarkedRecip R K) (h : ℕ) (c : ℤ_[2])
    (hMix : SqHandleMixFixesCore h c) :
    SqMarkedForwardSupply B h ↔ Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  ⟨fun H ↦ marked_matching_certificate_KTwoSq_of_supply B h c hMix H,
    fun ⟨C⟩ ↦ sqMarkedForwardSupply_of_certificate B C⟩

end Adapter

/-! ## §5 Refutation of route (b): the pivot row is not determined by orientation

The twisted marking `ν_tw = ν_sq⁻¹` of the `L_sq` core has the same kernel as `ν_sq`, is
surjective, and satisfies the level-zero clause `ν(ker χ) = ℤ₂` — i.e. every clause the marked
bundle supplies about `ν` — yet its pivot row is `−1`.  Its existence refutes any statement of
the form "an oriented equivalence forces `ν(f w) = 1`". -/

section Refutation

variable {h : ℕ}

/-- **The twisted marking** `ν_tw = ν_sq⁻¹`: the standard marking composed with the inversion
automorphism of `Multiplicative ℤ₂`. -/
def nuSqTwisted (h : ℕ) : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) where
  toFun := fun x ↦ (nuSq h x)⁻¹
  map_one' := by rw [map_one, inv_one]
  map_mul' := fun x y ↦ by rw [map_mul, mul_inv]
  continuous_toFun := continuous_inv.comp (nuSq h).continuous_toFun

@[simp] theorem nuSqTwisted_apply (x : (DSq h : Type)) :
    nuSqTwisted h x = (nuSq h x)⁻¹ := rfl

/-- The twisted marking has the same kernel as the standard one, so every kernel-shaped clause
of the marked bundle (`ki_unramified`) reads identically on it. -/
theorem ker_nuSqTwisted : (nuSqTwisted h).toMonoidHom.ker = (nuSq h).toMonoidHom.ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
  show (nuSq h x)⁻¹ = 1 ↔ nuSq h x = 1
  exact inv_eq_one

/-- The standard marking is surjective (`σ^y` realizes `y`). -/
theorem surjective_nuSq (h : ℕ) : Function.Surjective (nuSq h) := by
  intro z
  refine ⟨zpowZtwo (isProP_DSq h) (dsqSigma h) (toAdd z), Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_map_zpowZtwo (isProP_DSq h) (nuSq h) (dsqSigma h) (toAdd z), nuSq_sigma, toAdd_ofAdd,
    mul_one]

/-- The twisted marking is surjective too. -/
theorem surjective_nuSqTwisted (h : ℕ) : Function.Surjective (nuSqTwisted h) := by
  intro z
  obtain ⟨x, hx⟩ := surjective_nuSq h z⁻¹
  exact ⟨x, by rw [show (nuSqTwisted h) x = (nuSq h x)⁻¹ from rfl, hx, inv_inv]⟩

/-- The standard marking satisfies the level-zero clause on the `L_sq` core: the canonical pivot
`w` lies in `ker χ_sq` with unit row, so its `ℤ₂`-powers realize every value. -/
theorem nuSq_ker_chiSq_ge (h : ℕ) (y : ℤ_[2]) :
    ∃ g : (DSq h : Type), chiSq h g = 1 ∧ toAdd (nuSq h g) = y := by
  refine ⟨zpowZtwo (isProP_DSq h) (sqPivot h) y, ?_, ?_⟩
  · rw [map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h) (sqPivot h) y,
      chiSq_sqPivot, zpowZtwo_one_base]
  · rw [toAdd_map_zpowZtwo (isProP_DSq h) (nuSq h) (sqPivot h) y, nuSq_sqPivot, toAdd_ofAdd,
      mul_one]

/-- The twisted marking satisfies the level-zero clause as well. -/
theorem nuSqTwisted_ker_chiSq_ge (h : ℕ) (y : ℤ_[2]) :
    ∃ g : (DSq h : Type), chiSq h g = 1 ∧ toAdd (nuSqTwisted h g) = y := by
  obtain ⟨g, hgchi, hgnu⟩ := nuSq_ker_chiSq_ge h (-y)
  refine ⟨g, hgchi, ?_⟩
  rw [show (nuSqTwisted h) g = (nuSq h g)⁻¹ from rfl, toAdd_inv, hgnu, neg_neg]

/-- The twisted pivot row is `−1`, at every exponent. -/
theorem nuSqTwisted_sqMixPivotElem (h : ℕ) (c : ℤ_[2]) :
    nuSqTwisted h (sqMixPivotElem h c) = ofAdd (-1 : ℤ_[2]) := by
  rw [show (nuSqTwisted h) (sqMixPivotElem h c) = (nuSq h (sqMixPivotElem h c))⁻¹ from rfl,
    nuSq_sqMixPivotElem]
  rfl

/-- `−1 ≠ 1` in `ℤ₂`. -/
private theorem neg_one_ne_one : (-1 : ℤ_[2]) ≠ 1 := by
  intro hcon
  have h2 : (2 : ℤ_[2]) = 0 := by linear_combination -hcon
  exact (by norm_num : (2 : ℤ_[2]) ≠ 0) h2

/-- **Route (b) is false.**  There is a continuous marking of the `L_sq` core which
* is surjective onto `ℤ₂`,
* satisfies the level-zero clause `ν(ker χ_sq) = ℤ₂`,
* has the *same kernel* as the standard marking `ν_sq`,

and whose pivot row is `−1 ≠ 1`.  Since the underlying oriented equivalence may be taken to be
the identity of `D_sq(h)` (with the canonical `χ_sq` untouched), no theorem can derive the
certificate's pivot clause from an oriented equivalence plus the marked-reciprocity interface:
the row is a *normalization*, and must be selected with the generators.  This is why P3 is
route (a). -/
theorem exists_marking_orientation_pivot_ne_one (h : ℕ) (c : ℤ_[2]) :
    ∃ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      Function.Surjective nu' ∧
        (∀ y : ℤ_[2], ∃ g : (DSq h : Type), chiSq h g = 1 ∧ toAdd (nu' g) = y) ∧
        nu'.toMonoidHom.ker = (nuSq h).toMonoidHom.ker ∧
        (∀ x, chiSq h ((ContinuousMulEquiv.refl (DSq h : Type)) x) = chiSq h x) ∧
        nu' ((ContinuousMulEquiv.refl (DSq h : Type)) (sqMixPivotElem h c)) ≠
          ofAdd (1 : ℤ_[2]) := by
  refine ⟨nuSqTwisted h, surjective_nuSqTwisted h, nuSqTwisted_ker_chiSq_ge h, ker_nuSqTwisted,
    fun _ ↦ rfl, ?_⟩
  show nuSqTwisted h (sqMixPivotElem h c) ≠ ofAdd (1 : ℤ_[2])
  rw [nuSqTwisted_sqMixPivotElem]
  intro hcon
  exact neg_one_ne_one (Multiplicative.ofAdd.injective hcon)

end Refutation

end

#print axioms exists_chiCycKTwo_eq_one_and_nuUrKTwo_eq
#print axioms exists_chiCycKTwo_eq_and_nuUrKTwo_eq
#print axioms exists_squareShift_nuUrKTwo_eq
#print axioms exists_squareShift_nuUrKTwo_eq_one
#print axioms exists_squareShift_nuUrKTwo_eq_zero
#print axioms oddDegreeGalKSqMarkedCoreTable
#print axioms OddDegreeGalKSqCyclotomicCoreTable.toMarkedOfParities
#print axioms nuUrKTwo_sqMixPivotElem_eq_one
#print axioms marked_matching_certificate_KTwoSq_of_nuRows
#print axioms marked_matching_certificate_KTwoSq_of_markedTable
#print axioms marked_matching_certificate_KTwoSq_of_fixesCore_markedTable
#print axioms SqMarkedForwardSupply
#print axioms marked_matching_certificate_KTwoSq_of_supply
#print axioms marked_matching_certificate_KTwoSq_of_supply_shear
#print axioms sqMarkedForwardSupply_of_certificate
#print axioms sqMarkedForwardSupply_iff_nonempty_certificate
#print axioms exists_marking_orientation_pivot_ne_one

end GQ2.Dyadic.LSquare
