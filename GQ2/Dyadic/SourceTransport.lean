/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.QTwo
import GQ2.Dyadic.GammaRHom

/-!
# `SourceDataN` transport across an isomorphism  (dyadic campaign, ticket CB-TRN)

Work in progress.
-/

namespace GQ2.Dyadic.SourceTransport

open GQ2 GQ2.Dyadic GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-! ## §1 Precomposition with a continuous isomorphism

Every object the degree-`n` recursion counts is a set of *continuous maps out of the source*
cut out by a *pointwise* condition, so a continuous isomorphism of sources moves all of them by
precomposition.  §1 is that single mechanism; §§2–5 apply it family by family. -/

section Precomp

variable {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]

/-- Precomposition with `e : A ≃ₜ* B` is a bijection `Hom_c(B, Y) ≃ Hom_c(A, Y)`. -/
@[simps] def precompEquiv (e : A ≃ₜ* B) (Y : Type*) [Group Y] [TopologicalSpace Y] :
    ContinuousMonoidHom B Y ≃ ContinuousMonoidHom A Y where
  toFun f := f.comp (e : ContinuousMonoidHom A B)
  invFun g := g.comp (e.symm : ContinuousMonoidHom B A)
  left_inv f := ContinuousMonoidHom.ext fun b => congrArg f (e.apply_symm_apply b)
  right_inv g := ContinuousMonoidHom.ext fun a => congrArg g (e.symm_apply_apply a)

theorem precompEquiv_apply_apply (e : A ≃ₜ* B) {Y : Type*} [Group Y] [TopologicalSpace Y]
    (f : ContinuousMonoidHom B Y) (a : A) : precompEquiv e Y f a = f (e a) := rfl

/-- Precomposition on continuous *surjections* (`GQ2.ContSurj`). -/
@[simps] def contSurjEquiv (e : A ≃ₜ* B) (Y : Type*) [Group Y] [TopologicalSpace Y] :
    ContSurj B Y ≃ ContSurj A Y where
  toFun f := ⟨precompEquiv e Y f.1, f.2.comp e.surjective⟩
  invFun g := ⟨(precompEquiv e Y).symm g.1, g.2.comp e.symm.surjective⟩
  left_inv f := Subtype.ext ((precompEquiv e Y).left_inv f.1)
  right_inv g := Subtype.ext ((precompEquiv e Y).right_inv g.1)

end Precomp

/-! ## §2 Continuous cohomology under an isomorphism, for the trivial `𝔽₂`-action

The obstruction indicator `ι_Γ` (`GQ2.SectionEight.iotaB`) is a membership test against
`B²(Γ, 𝔽₂)`, so it transports as soon as the coboundary subgroup does.  Both sources carry
*their own* `DistribMulAction _ (ZMod 2)`; the actions correspond because both are trivial
(`WordCertificate.htriv` / `SourceDataN.htriv`), which is the only compatibility the differentials
need. -/

section Cohomology

variable {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
  [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
  [DistribMulAction A (ZMod 2)] [DistribMulAction B (ZMod 2)]

omit [IsTopologicalGroup A] [IsTopologicalGroup B] in
/-- **Coboundaries transport.**  If `φ` is the `δ¹` of a continuous `1`-cochain on `B`, then its
pullback along `e` is the `δ¹` of the pulled-back cochain.  Only *one* direction is proved here;
the equivalence follows by running it along `e.symm` (`mem_B2_comp_iff`). -/
theorem mem_B2_comp_of (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) {φ : B × B → ZMod 2}
    (hφ : φ ∈ B2 B (ZMod 2)) : (fun p : A × A => φ (e p.1, e p.2)) ∈ B2 A (ZMod 2) := by
  obtain ⟨ψ, hψc, rfl⟩ := hφ
  refine ⟨fun a => ψ (e a), hψc.comp e.continuous_toFun, funext fun p => ?_⟩
  show p.1 • ψ (e p.2) - ψ (e (p.1 * p.2)) + ψ (e p.1)
    = e p.1 • ψ (e p.2) - ψ (e p.1 * e p.2) + ψ (e p.1)
  rw [htA, htB, map_mul e]

omit [IsTopologicalGroup A] [IsTopologicalGroup B] in
/-- **The coboundary test is invariant under transport.** -/
theorem mem_B2_comp_iff (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) (φ : B × B → ZMod 2) :
    (fun p : A × A => φ (e p.1, e p.2)) ∈ B2 A (ZMod 2) ↔ φ ∈ B2 B (ZMod 2) := by
  refine ⟨fun h => ?_, mem_B2_comp_of htA htB e⟩
  have h2 := mem_B2_comp_of htB htA e.symm h
  have : (fun p : B × B => (fun r : A × A => φ (e r.1, e r.2)) (e.symm p.1, e.symm p.2)) = φ := by
    funext p; simp
  rwa [this] at h2

omit [IsTopologicalGroup A] [IsTopologicalGroup B] in
/-- **`ι_Γ` is invariant under transport** (the key naturality for `betaChi` and `QZero`). -/
theorem iotaB_comp (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) (φ : B × B → ZMod 2) :
    iotaB (fun p : A × A => φ (e p.1, e p.2)) = iotaB φ := by
  have key : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  by_cases h : φ ∈ B2 B (ZMod 2)
  · rw [iotaB_of_mem_B2 ((mem_B2_comp_iff htA htB e φ).mpr h), iotaB_of_mem_B2 h]
  · rw [key _ fun hc => h ((mem_B2_comp_iff htA htB e φ).mp (iotaB_eq_zero_iff.mp hc)),
      key _ fun hc => h (iotaB_eq_zero_iff.mp hc)]

end Cohomology

/-! ## §3 The `K`-boundary layer

`BoundaryLiftsK`, `LiftsOverK`, `mBK` and `MLifts` are all subtypes of `Hom_c(Γ, −)` (or of
`ContSurj Γ −`) cut out by pointwise conditions, so §1 moves them verbatim.  Every equivalence
below is `Equiv.subtypeEquiv` over a §1 bijection, and every `Nat.card` statement is
`Nat.card_congr` of one of them. -/

section KLayer

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]

/-- **Boundary lifts transport** (eq. (29) at the `K`-boundary): a `Y`-lift of the transported
boundary map is a `Y`-lift of the original, precomposed. -/
def boundaryLiftsKEquiv (e : A ≃ₜ* B) {Y : Type} [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) :
    BoundaryLiftsK b F T ≃ BoundaryLiftsK (precompEquiv e _ b) F T :=
  Equiv.subtypeEquiv (contSurjEquiv e Y) fun _ =>
    ⟨fun h a => h (e a), fun h β => by obtain ⟨a, rfl⟩ := e.surjective β; exact h a⟩

@[simp] theorem boundaryLiftsKEquiv_coe (e : A ≃ₜ* B) {Y : Type} [Group Y] [TopologicalSpace Y]
    [Finite Y] (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (T : MarkedTarget H E Y) (ρ : BoundaryLiftsK b F T) (a : A) :
    (boundaryLiftsKEquiv e b F T ρ).1.1 a = ρ.1.1 (e a) := rfl

/-- **The exact-image count is a transport invariant** (eq. (29)). -/
theorem exactImageCountK_comp (e : A ≃ₜ* B) {Y : Type} [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (T : MarkedTarget H E Y) :
    exactImageCountK (precompEquiv e _ b) F T = exactImageCountK b F T :=
  (Nat.card_congr (boundaryLiftsKEquiv e b F T)).symm

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **The `M`-stage lift set transports.** -/
def liftsOverKEquiv (e : A ≃ₜ* B) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    LiftsOverK RF b F ρ
      ≃ LiftsOverK RF (precompEquiv e _ b) F (boundaryLiftsKEquiv e b F RF.TC ρ) :=
  Equiv.subtypeEquiv (precompEquiv e RF.YB) fun _ =>
    ⟨fun h a => h (e a), fun h β => by obtain ⟨a, rfl⟩ := e.surjective β; exact h a⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The `B`-stage multiplicity `m_{Γ,λ}(B)` is a transport invariant.** -/
theorem mBK_comp (e : A ≃ₜ* B) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (l : RF.DR) : mBK RF (precompEquiv e _ b) F l = mBK RF b F l := by
  classical
  unfold mBK
  split_ifs with h
  · exact exactImageCountK_comp e b F RF.TB
  · refine (Nat.card_congr (Equiv.subtypeEquiv (boundaryLiftsKEquiv e b F RF.TB) fun f => ?_)).symm
    refine ⟨fun ⟨g, hg⟩ => ⟨precompEquiv e _ g, fun a => hg (e a)⟩, fun ⟨g, hg⟩ => ?_⟩
    exact ⟨(precompEquiv e _).symm g, fun β => by
      simpa using hg (e.symm β)⟩

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The lower map `ρ' = piBCiso⁻¹ ∘ ρ` transports** — definitionally, since it is a
postcomposition. -/
theorem rhoPrimeK_comp (e : A ≃ₜ* B) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (D : RadicalCoverData RF.YB) (hD : D.M = RF.MB) (ρ : BoundaryLiftsK b F RF.TC) :
    rhoPrimeK RF (precompEquiv e _ b) F D hD (boundaryLiftsKEquiv e b F RF.TC ρ)
      = precompEquiv e _ (rhoPrimeK RF b F D hD ρ) := rfl

end KLayer

/-! ## §4 The central-obstruction layer

`MLifts`, its central relation, `TCocycle` and `VCocycle` are again pointwise families over the
lower map, so §1 moves them.  The only non-`rfl` step is `TCocycle`/`VCocycle`'s crossed identity,
which needs `e (γδ) = e γ · e δ`. -/

section Obstruction

variable {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

/-- **Unrestricted `M`-lifts transport.** -/
def mLiftsEquiv (e : A ≃ₜ* B) (D : RadicalCoverData Bg)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) : MLifts D ρ ≃ MLifts D (precompEquiv e _ ρ) :=
  Equiv.subtypeEquiv (precompEquiv e Bg) fun _ =>
    ⟨fun h a => h (e a), fun h β => by obtain ⟨a, rfl⟩ := e.surjective β; exact h a⟩

omit [DiscreteTopology Bg] in
@[simp] theorem mLiftsEquiv_coe (e : A ≃ₜ* B) (D : RadicalCoverData Bg)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (f : MLifts D ρ) (a : A) :
    (mLiftsEquiv e D ρ f).1 a = f.1 (e a) := rfl

omit [DiscreteTopology Bg] in
/-- The central relation is preserved by the transport. -/
theorem mLiftsEquiv_central (e : A ≃ₜ* B) (D : RadicalCoverData Bg)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (f : MLifts D ρ) :
    (mLiftsEquiv e D ρ f).Central ↔ f.Central := by
  refine ⟨fun ⟨g, hg⟩ => ⟨(precompEquiv e _).symm g, fun β => by simpa using hg (e.symm β)⟩,
    fun ⟨g, hg⟩ => ⟨precompEquiv e _ g, fun a => hg (e a)⟩⟩

end Obstruction

end GQ2.Dyadic.SourceTransport
