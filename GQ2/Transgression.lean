/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import GQ2.QuadraticFp2
public import GQ2.OrbitData

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Transgression splitting for Lemma 6.21

Proof layer for `GQ2.SectionSix.lemma_6_21`: an extension `1 → V → B → C → 1` carrying a
global `𝔽₂`-valued 2-cocycle `ξ` whose fibre diagonal is a **nonsingular** quadratic form `q`
splits.  The paper's mechanism is the transgression formula `d₂(q) = B_q^♭ ∘ η` (eq. (116));
this file fixes a **direct cochain-level design** with no spectral sequences:

## The design

Fix a set-section `σ : C → B` with `σ 1 = 1` (`Function.surjInv` patched at `1`) and its
factor set `f c d := i⁻¹(σ c · σ d · σ (c·d)⁻¹) ∈ V` (values in `i.range = ker p`).  Define
the explicit **mixed cochain**

  `A : C → V → ZMod 2,  A c v := ξ (σ c, i (c⁻¹ • v)) + ξ (i v, σ c)`.

The **key transgression identity** (`key_transgression`, the cochain-level (116)) is

  `polar q (f c d) v = A c v + A d (c⁻¹ • v) + A (c*d) v`  —  i.e. `B_q^♭ ∘ f = δA` in the
  `C`-module `V^∨ = (V → 𝔽₂)` with `(c • φ) v = φ (c⁻¹ • v)`,

proved by expanding `hcocycle` on mixed triples from `{σ c, σ d, i v}` (the grind is
`lemma_6_22`-flavoured: `linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))`
over the cocycle instances, after normalizing arguments with `hconj`/`hσ`).

`A c` is **not additive** in `v` (defect = the conjugation defect of the fibre restriction
`R := ξ∘(i×i)`, `mixedA_defect`), so `B_q^♭⁻¹` cannot be applied to it directly.  The paper's
Lemma 6.21 resolves this obstruction with
its *"fixed equivariant class `κ⁰_q`"* hypothesis: in cochain avatar, a family
`t : C → V → 𝔽₂` with

  (i)  `δ_V(t c) = R(c•, c•) + R`   (each `t c` is a central automorphism datum of `𝔽₂ ×_R V`
       over the `c`-action), and
  (ii) `t (c·d) = t c (d•·) + t d`  (the automorphisms compose coherently, eq. (60)),

which is exactly Lemma 6.1's `IsEquivariantFactorSet` correction family `m`, transported from
`dat.f` to `R` along a primitive `θ` of the symmetric zero-diagonal 2-cocycle `dat.f + R`
(`symm_cocycle_is_coboundary`, `equivariant_lift_of_factorSet`).  Then `Ã c := A c + t c⁻¹` is
**additive** with the same `δ` (by (i) the defects cancel; by (ii) the correction telescopes),
`g := B_q^♭⁻¹ ∘ Ã` satisfies `f = δg` (bijectivity + `C`-equivariance of `B_q^♭`), and
`s c := i (g c)⁻¹ · σ c` is the splitting homomorphism.

## Facts derived, not assumed

* `V` has exponent 2: `polar q (v+v) w = 2·polar q v w = 0` for all `w`, so `hns` forces
  `v + v = 0` (`exponent_two_of_nonsingular`, proved below).
* `ξ` is normalized at `1`: cocycle instances give `ξ(g,1) = ξ(1,k) = ξ(1,1)`, and
  `hξq` at `v = 0` gives `ξ(1,1) = q 0 = 0`.
* `q (c • v) = q v` and `polar q (c•v) (c•w) = polar q v w`: conjugating a 2-cocycle changes
  it by an explicit coboundary `δ(k_b)`; diagonals and antisymmetrizations of coboundaries
  vanish (`δa` is symmetric with zero diagonal), so both are conjugation-invariant.

## Result

The theorem `splitting_of_global_cocycle` implements the complete assembly, and
`SectionSix.lemma_6_21` applies it through
`equivariant_lift_of_factorSet`.  The `κ⁰_q` hypothesis `(t, ht_quad, ht_mul)` restores the
paper's *"relative to the fixed equivariant class"* clause dropped by the consequence-form
extraction — see `docs/orchestration/p15i-transgression-gap.md`.
-/

namespace GQ2

namespace Transgression

open QuadraticFp2

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
variable {B : Type} [Group B] [Finite B]

omit [Finite V] in
/-- Exponent 2 of the fibre is forced by nonsingularity (no `h2` hypothesis needed):
`polar q (v+v) w = 2·polar q v w = 0` for every `w`. -/
theorem exponent_two_of_nonsingular {q : V → ZMod 2} (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (v : V) : v + v = 0 := by
  by_contra hne
  obtain ⟨w, hw⟩ := hns (v + v) hne
  exact hw (by rw [hq.polar_add_left]; exact CharTwo.add_self_eq_zero _)

/-! ## Symmetric zero-diagonal 2-cocycles on an elementary-abelian group are coboundaries

The injectivity half of `H²(V, 𝔽₂) ≅ {quadratic forms}`; used to transport the Lemma 6.1
correction family `m` from the datum's factor set `dat.f` to `ξ`'s own fibre restriction. -/

/-- Carrier of the twisted product `𝔽₂ ×_S V` (the central extension of `V` by `𝔽₂` with factor
set `S`), used in `symm_cocycle_is_coboundary`.  `S` is a phantom parameter so that the
operations below can refer to it. -/
private structure Twisted {V : Type*} (S : V → V → ZMod 2) where
  /-- The central `𝔽₂`-coordinate. -/
  z : ZMod 2
  /-- The base `V`-coordinate. -/
  v : V

namespace Twisted

variable {V' : Type*} [AddCommGroup V'] {S : V' → V' → ZMod 2}

private instance : Zero (Twisted S) := ⟨⟨0, 0⟩⟩
private instance : Add (Twisted S) :=
  ⟨fun p q => ⟨p.z + q.z + S p.v q.v, p.v + q.v⟩⟩
private instance : Neg (Twisted S) := ⟨fun p => p⟩

end Twisted

omit [Finite V] [DistribMulAction C V] in
/-- **Symmetric zero-diagonal 2-cocycles on an elementary-abelian group are coboundaries**:
if `S` satisfies the trivial-coefficient 2-cocycle identity, is symmetric and has zero
diagonal, then `S = δθ` for some `θ` with `θ 0 = 0`.  Proof: the twisted product `𝔽₂ ×_S V` is
an abelian group of exponent 2 (commutativity = symmetry, inverses = zero diagonal), hence an
`𝔽₂`-vector space; the projection to `V` is linear and surjective, so it has a linear section,
whose central coordinate is `θ`. -/
theorem symm_cocycle_is_coboundary
    (h2 : ∀ v : V, v + v = 0) (S : V → V → ZMod 2)
    (hcoc : ∀ v w x, S (v + w) x + S v w = S v (w + x) + S w x)
    (hsymm : ∀ v w, S v w = S w v) (hdiag : ∀ v, S v v = 0) :
    ∃ θ : V → ZMod 2, θ 0 = 0 ∧ ∀ v w, S v w = θ (v + w) + θ v + θ w := by
  have hS0l : ∀ v, S 0 v = 0 := by
    intro v
    have h := hcoc 0 0 v
    rw [add_zero, zero_add] at h
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h + hdiag 0
  letI : AddCommGroup (Twisted S) :=
    { add := (· + ·)
      zero := 0
      neg := Neg.neg
      nsmul := nsmulRec
      zsmul := zsmulRec
      add_assoc := fun p q r => by
        show Twisted.mk (p.z + q.z + S p.v q.v + r.z + S (p.v + q.v) r.v) (p.v + q.v + r.v)
            = Twisted.mk (p.z + (q.z + r.z + S q.v r.v) + S p.v (q.v + r.v)) (p.v + (q.v + r.v))
        congr 1
        · linear_combination hcoc p.v q.v r.v
        · exact add_assoc p.v q.v r.v
      zero_add := fun p => by
        show Twisted.mk (0 + p.z + S 0 p.v) (0 + p.v) = p
        rw [hS0l p.v, add_zero, zero_add, zero_add]
      add_zero := fun p => by
        show Twisted.mk (p.z + 0 + S p.v 0) (p.v + 0) = p
        rw [(hsymm p.v 0).trans (hS0l p.v), add_zero, add_zero, add_zero]
      neg_add_cancel := fun p => by
        show Twisted.mk (p.z + p.z + S p.v p.v) (p.v + p.v) = Twisted.mk 0 0
        rw [hdiag p.v, h2 p.v, add_zero, CharTwo.add_self_eq_zero]
      add_comm := fun p q => by
        show Twisted.mk (p.z + q.z + S p.v q.v) (p.v + q.v)
            = Twisted.mk (q.z + p.z + S q.v p.v) (q.v + p.v)
        rw [hsymm p.v q.v, add_comm p.v, add_comm p.z] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact h2 v)
  letI : Module (ZMod 2) (Twisted S) := AddCommGroup.zmodModule (fun p => by
    rw [two_nsmul]
    show Twisted.mk (p.z + p.z + S p.v p.v) (p.v + p.v) = Twisted.mk 0 0
    rw [hdiag p.v, h2 p.v, add_zero, CharTwo.add_self_eq_zero])
  let π : Twisted S →ₗ[ZMod 2] V :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' Twisted.v (fun p q => rfl))
  have hsurj : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun v => ⟨⟨0, v⟩, rfl⟩
  obtain ⟨s, hs⟩ := π.exists_rightInverse_of_surjective hsurj
  have hsv : ∀ v : V, (s v).v = v := fun v => LinearMap.congr_fun hs v
  refine ⟨fun v => (s v).z, ?_, ?_⟩
  · exact congrArg Twisted.z (map_zero s)
  · intro v w
    have hz' : (s (v + w)).z = (s v).z + (s w).z + S (s v).v (s w).v :=
      congrArg Twisted.z (s.map_add v w)
    rw [hsv v, hsv w] at hz'
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hz'

section Design

variable (p : B →* C) (hp : Function.Surjective p)
  (i : Multiplicative V →* B) (hi : Function.Injective i)
  (hrange : i.range = p.ker)
  (hconj : ∀ (b : B) (v : V), b * i (Multiplicative.ofAdd v) * b⁻¹
    = i (Multiplicative.ofAdd (p b • v)))
  (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
  (ξ : B × B → ZMod 2)
  (hcocycle : ∀ g h k : B, ξ (h, k) + ξ (g, h * k) = ξ (g * h, k) + ξ (g, h))
  (hξq : ∀ v : V, ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd v)) = q v)

include hq hns in
/-- The polar adjoint `B_q^♭ : V → (V → 𝔽₂)` is bijective onto the additive functionals:
for every additive `φ : V → 𝔽₂` there is a unique `v` with `polar q v · = φ`.  The polar of a
nonsingular `q` on the finite elementary abelian `V` is a nondegenerate `𝔽₂`-bilinear form, so
`V ≃ₗ Module.Dual (ZMod 2) V` (`LinearMap.BilinForm.toDual`); additivity ⟹ `𝔽₂`-linearity via
`AddMonoidHom.toZModLinearMap`. -/
theorem bflat_bijective :
    ∀ φ : V → ZMod 2, (∀ x y, φ (x + y) = φ x + φ y) →
      ∃! v : V, ∀ w, polar q v w = φ w := by
  intro φ hφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact exponent_two_of_nonsingular hq hns v)
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  -- The polar form as a genuine `𝔽₂`-bilinear form (biadditivity ⟹ `ZMod 2`-linearity).
  let Bil : LinearMap.BilinForm (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v => AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w')))
        (fun v v' => by
          ext w
          simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.mk'_apply, LinearMap.add_apply]
          exact hq.polar_add_left v v' w))
  have hBilapp : ∀ v w, Bil v w = polar q v w := fun v w => rfl
  have hnd : Bil.Nondegenerate := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · by_contra hvne
      obtain ⟨w, hw⟩ := hns v hvne
      exact hw (by rw [← hBilapp]; exact hv w)
    · by_contra hvne
      obtain ⟨w, hw⟩ := hns v hvne
      exact hw (by rw [polar_comm, ← hBilapp]; exact hv w)
  let e := Bil.toDual hnd
  let φlin : Module.Dual (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' φ hφ)
  have hφlinapp : ∀ w, φlin w = φ w := fun w => rfl
  refine ⟨e.symm φlin, ?_, ?_⟩
  · intro w
    rw [← hBilapp]
    show Bil ((Bil.toDual hnd).symm φlin) w = φ w
    rw [LinearMap.BilinForm.apply_toDual_symm_apply, hφlinapp]
  · intro v' hv'
    have hev' : e v' = φlin := by
      ext w
      show Bil v' w = φlin w
      rw [hBilapp, hv' w, hφlinapp]
    rw [← e.symm_apply_apply v', hev']

omit [Finite V] [Finite B] in
include hcocycle hξq hq hns in
/-- **The fibre antisymmetrization computes the polar**: for `u w : V`,
`polar q u w = ξ(iu, iw) + ξ(iw, iu)`.  Proof: expand `q(u+w) = ξ(iu·iw, iu·iw)` by the
cocycle on the (commuting, involutive) fibre elements `iu, iw`, using normalization
`ξ(1, ·) = 0`. -/
theorem polar_fibre (u w : V) :
    polar q u w = ξ (i (Multiplicative.ofAdd u), i (Multiplicative.ofAdd w))
                + ξ (i (Multiplicative.ofAdd w), i (Multiplicative.ofAdd u)) := by
  -- normalization `ξ(1, ·) = 0`
  have hone : ξ ((1 : B), (1 : B)) = 0 := by
    simpa [hq.map_zero] using hξq 0
  have h1L : ∀ x : B, ξ ((1 : B), x) = 0 := by
    intro x
    have h := hcocycle 1 1 x
    rw [one_mul, one_mul, hone, add_zero, CharTwo.add_self_eq_zero] at h
    exact h.symm
  set a := i (Multiplicative.ofAdd u) with ha
  set b := i (Multiplicative.ofAdd w) with hb
  have hab : a * b = i (Multiplicative.ofAdd (u + w)) := by rw [ha, hb, ← map_mul, ← ofAdd_add]
  have hba : b * a = i (Multiplicative.ofAdd (u + w)) := by
    rw [ha, hb, ← map_mul, ← ofAdd_add, add_comm w u]
  have hcomm : a * b = b * a := by rw [hab, hba]
  have hbb : b * b = 1 := by
    rw [hb, ← map_mul, ← ofAdd_add, exponent_two_of_nonsingular hq hns w, ofAdd_zero, map_one]
  have hqu : q u = ξ (a, a) := (hξq u).symm
  have hqw : q w = ξ (b, b) := (hξq w).symm
  have hquw : q (u + w) = ξ (a * b, a * b) := by rw [hab]; exact (hξq (u + w)).symm
  have hbab : b * (a * b) = a := by rw [← mul_assoc, ← hcomm, mul_assoc, hbb, mul_one]
  have hc1 := hcocycle a b (a * b)
  rw [hbab] at hc1
  have hc2 := hcocycle b b a
  rw [hbb, ← hcomm, h1L] at hc2
  unfold polar
  rw [hquw, hqu, hqw]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc1 + hc2

omit [Finite B] in
include hcocycle in
/-- **Conjugation is a coboundary**: for a trivial-coefficient 2-cocycle `ξ`, conjugation by a
fixed `s` changes `ξ` by the coboundary of the 1-cochain `β_s(z) = ξ(s, z) + ξ(szs⁻¹, s)`:
`ξ(sxs⁻¹, sys⁻¹) + ξ(x, y) = β_s(x) + β_s(y) + β_s(xy)`.  (Three cocycle instances, char 2.) -/
theorem xi_conj_cobound (s x y : B) :
    ξ (s * x * s⁻¹, s * y * s⁻¹) + ξ (x, y)
      = (ξ (s, x) + ξ (s * x * s⁻¹, s)) + (ξ (s, y) + ξ (s * y * s⁻¹, s))
        + (ξ (s, x * y) + ξ (s * (x * y) * s⁻¹, s)) := by
  have hYs : s * y * s⁻¹ * s = s * y := by group
  have hXs : s * x * s⁻¹ * s = s * x := by group
  have hXY : s * x * s⁻¹ * (s * y * s⁻¹) = s * (x * y) * s⁻¹ := by group
  have hc1 := hcocycle (s * x * s⁻¹) (s * y * s⁻¹) s
  rw [hYs, hXY] at hc1
  have hc2 := hcocycle (s * x * s⁻¹) s y
  rw [hXs] at hc2
  have hc3 := hcocycle s x y
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc1 + hc2 + hc3

omit [Finite C] [Finite V] [Finite B] in
include hp hconj hcocycle hξq hq hns in
/-- Conjugation-invariance of the polar form: `polar q (c•v) (c•w) = polar q v w`.  The polar is
the fibre antisymmetrization (`polar_fibre`), and by `xi_conj_cobound` conjugation changes `ξ`
by a coboundary; the antisymmetrization of a coboundary vanishes on the commuting fibre
elements, so the polar is `C`-invariant. -/
theorem polar_conj (c : C) (v w : V) :
    polar q (c • v) (c • w) = polar q v w := by
  obtain ⟨s, hs⟩ := hp c
  have hcv : ∀ z : V, i (Multiplicative.ofAdd (c • z))
      = s * i (Multiplicative.ofAdd z) * s⁻¹ := by
    intro z; have h := hconj s z; rw [hs] at h; exact h.symm
  rw [polar_fibre i q hq hns ξ hcocycle hξq (c • v) (c • w),
      polar_fibre i q hq hns ξ hcocycle hξq v w, hcv v, hcv w]
  set av := i (Multiplicative.ofAdd v) with hav
  set bw := i (Multiplicative.ofAdd w) with hbw
  have hcomm : av * bw = bw * av := by
    rw [hav, hbw]
    exact (Commute.all (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)).map i
  have hAB := xi_conj_cobound ξ hcocycle s av bw
  have hBA := xi_conj_cobound ξ hcocycle s bw av
  rw [← hcomm] at hBA
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hAB + hBA

/-- The normalized section: `Function.surjInv hp` patched to send `1 ↦ 1`. -/
noncomputable def sigma : C → B := fun c =>
  letI := Classical.dec (c = 1)
  if c = 1 then 1 else Function.surjInv hp c

omit [Finite C] [Finite B] in
private theorem sigma_spec (c : C) : p (sigma p hp c) = c := by
  unfold sigma
  split
  · rename_i h; rw [map_one, h]
  · exact Function.surjInv_eq hp c

/-- The factor set of `sigma`, valued in `V` through `i⁻¹` (well-defined:
`σc·σd·σ(cd)⁻¹ ∈ ker p = i.range`).  [O: define via `Function.invFun i` + `hrange`;
prove `i (ofAdd (factorSet c d)) = sigma c * sigma d * (sigma (c*d))⁻¹`.] -/
noncomputable def factorSet (c d : C) : V :=
  Multiplicative.toAdd (Function.invFun i
    (sigma p hp c * sigma p hp d * (sigma p hp (c * d))⁻¹))

omit [Finite V] [DistribMulAction C V] [Finite C] [Finite B] in
include hp hrange in
/-- Defining property of the factor set: `i (ofAdd (f c d)) = σc · σd · σ(cd)⁻¹`
(well-defined since `σc·σd·σ(cd)⁻¹ ∈ ker p = i.range`). -/
theorem factorSet_spec (c d : C) :
    i (Multiplicative.ofAdd (factorSet p hp i c d))
      = sigma p hp c * sigma p hp d * (sigma p hp (c * d))⁻¹ := by
  unfold factorSet
  rw [ofAdd_toAdd]
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, hrange, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, sigma_spec]
  group

/-- The mixed transgression cochain `A c v = ξ(σc, i(c⁻¹•v)) + ξ(iv, σc)`. -/
noncomputable def mixedA (c : C) (v : V) : ZMod 2 :=
  ξ (sigma p hp c, i (Multiplicative.ofAdd (c⁻¹ • v)))
    + ξ (i (Multiplicative.ofAdd v), sigma p hp c)

omit [Finite V] [Finite C] [Finite B] in
include hp hconj hcocycle in
/-- **The additivity defect of `mixedA` is the fibre-restriction conjugation defect** (the
`D_c` of the Lemma 6.21 proof gap analysis): `mixedA c` fails additivity in `v` by exactly
`ξ(i(c⁻¹v), i(c⁻¹w)) + ξ(iv, iw)`.  Three `hcocycle` instances after two `hconj` moves;
this is what blocks `B_q^♭⁻¹ ∘ mixedA` and forces the `κ⁰_q` hypothesis. -/
theorem mixedA_defect (c : C) (v w : V) :
    mixedA p hp i ξ c (v + w) + mixedA p hp i ξ c v + mixedA p hp i ξ c w
      = ξ (i (Multiplicative.ofAdd (c⁻¹ • v)), i (Multiplicative.ofAdd (c⁻¹ • w)))
        + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w)) := by
  simp only [mixedA]
  have hm1v : i (Multiplicative.ofAdd v) * sigma p hp c
      = sigma p hp c * i (Multiplicative.ofAdd (c⁻¹ • v)) := by
    have h := hconj (sigma p hp c) (c⁻¹ • v)
    rw [sigma_spec, ← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h]; group
  have hm1w : i (Multiplicative.ofAdd w) * sigma p hp c
      = sigma p hp c * i (Multiplicative.ofAdd (c⁻¹ • w)) := by
    have h := hconj (sigma p hp c) (c⁻¹ • w)
    rw [sigma_spec, ← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h]; group
  set σ := sigma p hp c with hσ
  set Xv := i (Multiplicative.ofAdd v) with hXv
  set Xw := i (Multiplicative.ofAdd w) with hXw
  set Xcv := i (Multiplicative.ofAdd (c⁻¹ • v)) with hXcv
  set Xcw := i (Multiplicative.ofAdd (c⁻¹ • w)) with hXcw
  have hXvw : Xv * Xw = i (Multiplicative.ofAdd (v + w)) := by
    rw [hXv, hXw, ← map_mul, ← ofAdd_add]
  have hXcvw : Xcv * Xcw = i (Multiplicative.ofAdd (c⁻¹ • (v + w))) := by
    rw [hXcv, hXcw, ← map_mul, ← ofAdd_add, ← smul_add]
  have hA := hcocycle σ Xcv Xcw
  rw [hXcvw, show σ * Xcv = Xv * σ from hm1v.symm] at hA
  have hB := hcocycle Xv σ Xcw
  rw [show σ * Xcw = Xw * σ from hm1w.symm] at hB
  have hC := hcocycle Xv Xw σ
  rw [hXvw] at hC
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hA + hB + hC

omit [Finite V] [Finite C] [Finite B] in
include hp hrange hconj hcocycle hξq hq hns in
/-- **The key transgression identity** — the cochain-level eq. (116): `B_q^♭(f c d) = (δA)(c,d)`
as functionals on `V`, i.e. `polar q (f c d) v = A c v + A d (c⁻¹•v) + A (c*d) v`.  Proof: rewrite
the polar as a fibre antisymmetrization (`polar_fibre`), the factor set through `factorSet_spec`,
then close with a single char-2 `linear_combination` of nine `hcocycle` instances whose group
arguments are normalized by three `hconj`-conjugation moves (`m1`/`m2`/`m3`). -/
theorem key_transgression (c d : C) (v : V) :
    polar q (factorSet p hp i c d) v
      = mixedA p hp i ξ c v + mixedA p hp i ξ d (c⁻¹ • v) + mixedA p hp i ξ (c * d) v := by
  rw [polar_fibre i q hq hns ξ hcocycle hξq (factorSet p hp i c d) v,
      factorSet_spec p hp i hrange c d]
  simp only [mixedA, ← mul_smul, ← mul_inv_rev]
  -- normalization `ξ(1, ·) = 0 = ξ(·, 1)`
  have hone : ξ ((1 : B), (1 : B)) = 0 := by
    simpa [hq.map_zero] using hξq 0
  have hone_left : ∀ x : B, ξ ((1 : B), x) = 0 := by
    intro x
    have h := hcocycle 1 1 x
    rw [one_mul, one_mul, hone, add_zero, CharTwo.add_self_eq_zero] at h
    exact h.symm
  have hone_right : ∀ y : B, ξ (y, (1 : B)) = 0 := by
    intro y
    have h := hcocycle y 1 1
    rwa [mul_one, mul_one, hone, zero_add, CharTwo.add_self_eq_zero] at h
  -- conjugation-move relations (`hconj` + `sigma_spec`), raw form
  have m1 : i (Multiplicative.ofAdd v) * sigma p hp c
      = sigma p hp c * i (Multiplicative.ofAdd (c⁻¹ • v)) := by
    have h := hconj (sigma p hp c) (c⁻¹ • v)
    rw [sigma_spec, ← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h]; group
  have m2 : i (Multiplicative.ofAdd (c⁻¹ • v)) * sigma p hp d
      = sigma p hp d * i (Multiplicative.ofAdd ((c * d)⁻¹ • v)) := by
    have h := hconj (sigma p hp d) ((c * d)⁻¹ • v)
    rw [sigma_spec, mul_inv_rev, ← mul_smul, ← mul_assoc, mul_inv_cancel, one_mul] at h
    rw [← h]; group
  have m3 : sigma p hp (c * d) * i (Multiplicative.ofAdd ((c * d)⁻¹ • v))
      = i (Multiplicative.ofAdd v) * sigma p hp (c * d) := by
    have h := hconj (sigma p hp (c * d)) ((c * d)⁻¹ • v)
    rw [sigma_spec, ← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h]; group
  set a := sigma p hp c with ha
  set b := sigma p hp d with hb
  set m := sigma p hp (c * d) with hm
  set X := i (Multiplicative.ofAdd v) with hX
  set Xc := i (Multiplicative.ofAdd (c⁻¹ • v)) with hXc
  set Xcd := i (Multiplicative.ofAdd ((c * d)⁻¹ • v)) with hXcd
  -- derived moves
  have m4 : Xcd * m⁻¹ = m⁻¹ * X := by
    have h5 : Xcd = m⁻¹ * (X * m) := by rw [← m3]; group
    rw [h5]; group
  have m6 : X * (a * b) = a * b * Xcd := by
    rw [← mul_assoc, m1, mul_assoc, m2, ← mul_assoc]
  -- the nine cocycle instances, group arguments normalized by the moves
  have hA := hcocycle X (a * b) m⁻¹
  rw [m6] at hA
  have hB := hcocycle X a b
  rw [m1] at hB
  have hC := hcocycle a Xc b
  rw [m2] at hC
  have hD := hcocycle a b Xcd
  have hE := hcocycle (a * b) Xcd m⁻¹
  rw [m4] at hE
  have hF := hcocycle (a * b) m⁻¹ X
  have hG := hcocycle m Xcd m⁻¹
  rw [m4, m3] at hG
  have hH := hcocycle m m⁻¹ X
  rw [mul_inv_cancel, hone_left] at hH
  have hI := hcocycle X m m⁻¹
  rw [mul_inv_cancel, hone_right] at hI
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    hA + hB + hC + hD + hE + hF + hG + hH + hI

omit [Finite C] [Finite V] [Finite B] in
include hq hns hcocycle hξq in
/-- **The `κ⁰_q`-datum supplies the coherent equivariant lift** (Lemma 6.1 → the paper's
`α_c`-family): from an equivariant factor-set datum for `q` (`IsEquivariantFactorSet`),
transport the correction family `m` along a primitive `θ` of `dat.f + ξ|fibre` (two 2-cocycles
on `V` with the same diagonal `q`, so their difference is a symmetric zero-diagonal 2-cocycle —
`symm_cocycle_is_coboundary`).  The result satisfies the two identities of eqs. (59)/(60)
**with `ξ`'s own fibre restriction** in place of `dat.f` — the hypothesis shape consumed by
`splitting_of_global_cocycle`. -/
theorem equivariant_lift_of_factorSet (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q dat) :
    ∃ t : C → V → ZMod 2,
      (∀ (c : C) (v w : V),
        t c (v + w) + t c v + t c w
          = ξ (i (Multiplicative.ofAdd (c • v)), i (Multiplicative.ofAdd (c • w)))
            + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w)))
      ∧ (∀ (c d : C) (v : V), t (c * d) v = t c (d • v) + t d v) := by
  have h2 : ∀ v : V, v + v = 0 := exponent_two_of_nonsingular hq hns
  -- `S := dat.f + ξ|fibre` is a symmetric zero-diagonal 2-cocycle
  have hScoc : ∀ v w x : V,
      (dat.f (v + w) x + ξ (i (Multiplicative.ofAdd (v + w)), i (Multiplicative.ofAdd x)))
        + (dat.f v w + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w)))
      = (dat.f v (w + x) + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd (w + x))))
        + (dat.f w x + ξ (i (Multiplicative.ofAdd w), i (Multiplicative.ofAdd x))) := by
    intro v w x
    have h1 := hdat.f_cocycle v w x
    have h := hcocycle (i (Multiplicative.ofAdd v)) (i (Multiplicative.ofAdd w))
      (i (Multiplicative.ofAdd x))
    rw [← map_mul, ← ofAdd_add, ← map_mul, ← ofAdd_add] at h
    linear_combination h1 - h
  have hSsymm : ∀ v w : V,
      dat.f v w + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w))
        = dat.f w v + ξ (i (Multiplicative.ofAdd w), i (Multiplicative.ofAdd v)) := by
    intro v w
    have h1 := hdat.f_polar v w
    have h2' := polar_fibre i q hq hns ξ hcocycle hξq v w
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 + h2'
  have hSdiag : ∀ v : V,
      dat.f v v + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd v)) = 0 := by
    intro v
    have h1 := hdat.f_diag v
    have h2' := hξq v
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 + h2'
  obtain ⟨θ, -, hθ⟩ := symm_cocycle_is_coboundary h2
    (fun v w => dat.f v w + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w)))
    hScoc hSsymm hSdiag
  refine ⟨fun c v => dat.m c v + θ (c • v) + θ v, fun c v w => ?_, fun c d v => ?_⟩
  · show (dat.m c (v + w) + θ (c • (v + w)) + θ (v + w))
        + (dat.m c v + θ (c • v) + θ v) + (dat.m c w + θ (c • w) + θ w)
      = ξ (i (Multiplicative.ofAdd (c • v)), i (Multiplicative.ofAdd (c • w)))
        + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w))
    have hm := hdat.m_quad c v w
    have hθ1 := hθ (c • v) (c • w)
    have hθ2 := hθ v w
    rw [show c • v + c • w = c • (v + w) from (smul_add c v w).symm] at hθ1
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hm + hθ1 + hθ2
  · show dat.m (c * d) v + θ ((c * d) • v) + θ v
      = (dat.m c (d • v) + θ (c • d • v) + θ (d • v)) + (dat.m d v + θ (d • v) + θ v)
    have hm := hdat.m_mul c d v
    rw [show (c * d) • v = c • d • v from mul_smul c d v]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hm

include hp hrange hconj hcocycle hξq hq hns in
omit [Finite C] [Finite B] in
/-- **The assembled splitting** (= `lemma_6_21`, *relative to the fixed equivariant class*).
The `κ⁰_q` hypothesis is the family `(t, ht_quad, ht_mul)`: each `t c` is the central-correction
datum of an automorphism of the fibre extension `𝔽₂ ×_{ξ|fibre} V` over the `c`-action
(`ht_quad`), and the family composes coherently (`ht_mul`) — the paper's `α_c α_d = α_{cd}`;
it is supplied by `equivariant_lift_of_factorSet` from Lemma 6.1's `IsEquivariantFactorSet`.
Structure of the proof:

* **Additive primitive:** `Ã c := mixedA c + t c⁻¹` is additive in
  `v` (`mixedA_defect` cancels against `ht_quad` at `c⁻¹`) and has the same `C`-coboundary as
  `mixedA` (`ht_mul` telescopes), so `key_transgression` + `bflat_bijective` produce a
  `B_q^♭`-representable transgression primitive `g : C → V`.
* **Descent**: polar-adjoint injectivity (`bflat_bijective`) together with `polar_conj`
  (equivariance) upgrades the primitive to the `H²(C,V)`-coboundary equation
  `f c d = g c + c • g d + g (c*d)`.
* **Section**: from that coboundary equation, `s c := i(ofAdd (g c))⁻¹ · σ c` is a monoid
  homomorphism sectioning `p` (`hconj` + `factorSet_spec` + fibre 2-torsion). -/
theorem splitting_of_global_cocycle
    (t : C → V → ZMod 2)
    (ht_quad : ∀ (c : C) (v w : V),
      t c (v + w) + t c v + t c w
        = ξ (i (Multiplicative.ofAdd (c • v)), i (Multiplicative.ofAdd (c • w)))
          + ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd w)))
    (ht_mul : ∀ (c d : C) (v : V), t (c * d) v = t c (d • v) + t d v) :
    ∃ s : C →* B, ∀ cc : C, p (s cc) = cc := by
  -- injectivity of the polar adjoint `B_q^♭`, from `bflat_bijective`
  have hinj : ∀ x y : V, (∀ w, polar q x w = polar q y w) → x = y := by
    intro x y hxy
    obtain ⟨z, _, hz⟩ := bflat_bijective q hq hns (fun w => polar q x w)
      (hq.polar_add_right x)
    rw [hz x fun w => rfl]
    exact (hz y fun w => (hxy w).symm).symm
  -- the corrected transgression cochain `Ã c v = mixedA c v + t c⁻¹ v` is additive in `v`
  have hAadd : ∀ (c : C) (v w : V),
      mixedA p hp i ξ c (v + w) + t c⁻¹ (v + w)
        = (mixedA p hp i ξ c v + t c⁻¹ v) + (mixedA p hp i ξ c w + t c⁻¹ w) := by
    intro c v w
    have hd := mixedA_defect p hp i hconj ξ hcocycle c v w
    have hq' := ht_quad c⁻¹ v w
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hd + hq'
  -- existence of a `B_q^♭`-representable transgression primitive (the closed the Lemma 6.21 proof gap)
  obtain ⟨g, hg⟩ : ∃ g : C → V, ∀ (cc dd : C) (v : V),
      polar q (factorSet p hp i cc dd) v
        = polar q (g cc) v + polar q (g dd) (cc⁻¹ • v) + polar q (g (cc * dd)) v := by
    have hrep : ∀ c : C, ∃ x : V, ∀ w,
        polar q x w = mixedA p hp i ξ c w + t c⁻¹ w := fun c =>
      (bflat_bijective q hq hns (fun w => mixedA p hp i ξ c w + t c⁻¹ w)
        (hAadd c)).exists
    choose g hgrep using hrep
    refine ⟨g, fun cc dd v => ?_⟩
    have hk := key_transgression p hp i hrange hconj q hq hns ξ hcocycle hξq cc dd v
    have hm := ht_mul dd⁻¹ cc⁻¹ v
    rw [hgrep cc v, hgrep dd (cc⁻¹ • v), hgrep (cc * dd) v,
      show (cc * dd)⁻¹ = dd⁻¹ * cc⁻¹ from mul_inv_rev cc dd]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hk + hm
  -- descent: `f = δ g` in `H²(C, V)`
  have hcob : ∀ cc dd : C, factorSet p hp i cc dd = g cc + cc • g dd + g (cc * dd) := by
    intro cc dd
    apply hinj
    intro w
    have hmid : polar q (g dd) (cc⁻¹ • w) = polar q (cc • g dd) w := by
      have hpc := polar_conj p hp i hconj q hq hns ξ hcocycle hξq cc (g dd) (cc⁻¹ • w)
      rw [smul_smul, mul_inv_cancel, one_smul] at hpc
      exact hpc.symm
    rw [hg cc dd w, hmid, ← hq.polar_add_left, ← hq.polar_add_left]
  -- the splitting homomorphism `s cc = i(ofAdd (g cc))⁻¹ · σ cc`
  refine ⟨MonoidHom.mk' (fun cc => (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc) ?_, ?_⟩
  · intro cc dd
    have hmove : sigma p hp cc * (i (Multiplicative.ofAdd (g dd)))⁻¹
               = (i (Multiplicative.ofAdd (cc • g dd)))⁻¹ * sigma p hp cc := by
      have h := hconj (sigma p hp cc) (g dd)
      rw [sigma_spec] at h
      rw [← h]; group
    have hfs : sigma p hp cc * sigma p hp dd
             = i (Multiplicative.ofAdd (factorSet p hp i cc dd)) * sigma p hp (cc * dd) := by
      rw [factorSet_spec p hp i hrange cc dd]; group
    have hiprod : (i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
                * i (Multiplicative.ofAdd (factorSet p hp i cc dd))
                = i (Multiplicative.ofAdd (g (cc * dd))) := by
      rw [hcob cc dd]
      simp only [← map_inv, ← map_mul]
      congr 1
      simp only [← ofAdd_neg, ← ofAdd_add]
      congr 1
      abel
    have htors : (i (Multiplicative.ofAdd (g (cc * dd))))⁻¹
               = i (Multiplicative.ofAdd (g (cc * dd))) := by
      have h2 : g (cc * dd) + g (cc * dd) = 0 := exponent_two_of_nonsingular hq hns _
      rw [← map_inv, ← ofAdd_neg, neg_eq_of_add_eq_zero_left h2]
    have key : (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc
             * ((i (Multiplicative.ofAdd (g dd)))⁻¹ * sigma p hp dd)
             = i (Multiplicative.ofAdd (g (cc * dd))) * sigma p hp (cc * dd) := by
      calc (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc
              * ((i (Multiplicative.ofAdd (g dd)))⁻¹ * sigma p hp dd)
          = (i (Multiplicative.ofAdd (g cc)))⁻¹
              * (sigma p hp cc * (i (Multiplicative.ofAdd (g dd)))⁻¹) * sigma p hp dd := by group
        _ = (i (Multiplicative.ofAdd (g cc)))⁻¹
              * ((i (Multiplicative.ofAdd (cc • g dd)))⁻¹ * sigma p hp cc) * sigma p hp dd := by
              rw [hmove]
        _ = (i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
              * (sigma p hp cc * sigma p hp dd) := by group
        _ = (i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
              * (i (Multiplicative.ofAdd (factorSet p hp i cc dd)) * sigma p hp (cc * dd)) := by
              rw [hfs]
        _ = ((i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
              * i (Multiplicative.ofAdd (factorSet p hp i cc dd))) * sigma p hp (cc * dd) := by
              group
        _ = i (Multiplicative.ofAdd (g (cc * dd))) * sigma p hp (cc * dd) := by rw [hiprod]
    show (i (Multiplicative.ofAdd (g (cc * dd))))⁻¹ * sigma p hp (cc * dd)
       = (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc
         * ((i (Multiplicative.ofAdd (g dd)))⁻¹ * sigma p hp dd)
    rw [htors, key]
  · intro cc
    show p ((i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc) = cc
    rw [map_mul, map_inv, sigma_spec]
    have hker : i (Multiplicative.ofAdd (g cc)) ∈ p.ker := by
      rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [MonoidHom.mem_ker] at hker
    rw [hker, inv_one, one_mul]

end Design

end Transgression

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (116) = ⟦eq-transgressionformula⟧
  * eq. (59) = ⟦eq-mquadratic⟧
  * eq. (60) = ⟦eq-mcoherent⟧
  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
  * Lemma 6.21 = ⟦lem-transgression⟧
-/
