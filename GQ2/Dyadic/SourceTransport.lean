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

section H2

variable [ContinuousSMul A (ZMod 2)] [ContinuousSMul B (ZMod 2)]

omit [IsTopologicalGroup A] [IsTopologicalGroup B] [ContinuousSMul A (ZMod 2)]
  [ContinuousSMul B (ZMod 2)] in
/-- The equivariance `ContCoh.H2comap` asks for, at the identity coefficient map and two trivial
actions. -/
theorem zmodTwo_compat (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) :
    ∀ (g : A) (n : ZMod 2), (AddMonoidHom.id (ZMod 2)) ((e : ContinuousMonoidHom A B) g • n)
      = g • (AddMonoidHom.id (ZMod 2)) n := fun g n => by
  show (e : ContinuousMonoidHom A B) g • n = g • n
  rw [htA, htB]

/-- The identity of `𝔽₂` as a continuous additive map, at the exact type `H2comap` demands
(`continuous_id` itself is stated at `id`, not at `⇑(AddMonoidHom.id _)`, and the coercion gap
breaks later `simp` calls). -/
theorem continuous_addMonoidHom_id_zmodTwo : Continuous ⇑(AddMonoidHom.id (ZMod 2)) :=
  continuous_id

/-- **`H²(−, 𝔽₂)` transports.**  `ContCoh.H2comap` in both directions; the two composites are the
identity because the coefficient map is `id` and `e.symm ∘ e = id`. -/
noncomputable def h2Equiv (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) :
    H2 B (ZMod 2) ≃ H2 A (ZMod 2) where
  toFun := H2comap (e : ContinuousMonoidHom A B) (AddMonoidHom.id _)
    continuous_addMonoidHom_id_zmodTwo (zmodTwo_compat htA htB e)
  invFun := H2comap (e.symm : ContinuousMonoidHom B A) (AddMonoidHom.id _)
    continuous_addMonoidHom_id_zmodTwo (zmodTwo_compat htB htA e.symm)
  left_inv x := by
    obtain ⟨φ, rfl⟩ := H2mk_surjective (G := B) (M := ZMod 2) x
    refine congrArg (H2mk B (ZMod 2)) (Subtype.ext (funext fun p => ?_))
    show φ.1 (e (e.symm p.1), e (e.symm p.2)) = φ.1 p
    rw [e.apply_symm_apply, e.apply_symm_apply]
  right_inv x := by
    obtain ⟨φ, rfl⟩ := H2mk_surjective (G := A) (M := ZMod 2) x
    refine congrArg (H2mk A (ZMod 2)) (Subtype.ext (funext fun p => ?_))
    show φ.1 (e.symm (e p.1), e.symm (e p.2)) = φ.1 p
    rw [e.symm_apply_apply, e.symm_apply_apply]

omit [IsTopologicalGroup A] [IsTopologicalGroup B] [ContinuousSMul A (ZMod 2)]
  [ContinuousSMul B (ZMod 2)] in
/-- **`#H²(−, 𝔽₂)` is a transport invariant** — the `SourceDataN.cardH2` clause. -/
theorem card_H2_comp (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B) :
    Nat.card (H2 A (ZMod 2)) = Nat.card (H2 B (ZMod 2)) :=
  (Nat.card_congr (h2Equiv htA htB e)).symm

end H2

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

/-! ## §5 Cocycles, the `χ`-obstruction and the base determinant form

`TCocycle`/`VCocycle` are pointwise families again — their crossed identities are the only place
where `e (γδ) = e γ · e δ` is needed rather than `rfl`.  Everything built on top of a `VCocycle`
(`fLift`, `tDef`, `chiDef`, `graphPullback`) is *literally* pointwise, so it commutes with the
transport definitionally, and `betaChi` / `QZero` then follow from §2's `iotaB_comp`. -/

section Cocycles

variable {A B : Type} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]
variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

omit [DiscreteTopology Bg] in
/-- Two `T`-cocycles with the same underlying function are equal (`VCocycle.ext`'s missing
`T`-side twin). -/
theorem tCocycle_ext {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)} {u v : TCocycle D ρ} (h : u.u = v.u) : u = v := by
  cases u; cases v; simp only [TCocycle.mk.injEq]; exact h

/-- **`T`-cocycles transport.** -/
def tCocycleEquiv [IsTopologicalGroup A] [IsTopologicalGroup B] (e : A ≃ₜ* B)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) :
    TCocycle D ρ ≃ TCocycle D (precompEquiv e _ ρ) where
  toFun u :=
    { u := fun a => u.u (e a)
      mem := fun a => u.mem (e a)
      cont := u.cont.comp e.continuous_toFun
      crossed := fun γ δ b hb => by
        have h := u.crossed (e γ) (e δ) b hb
        rwa [← map_mul e γ δ] at h }
  invFun v :=
    { u := fun β => v.u (e.symm β)
      mem := fun β => v.mem (e.symm β)
      cont := v.cont.comp e.symm.continuous_toFun
      crossed := fun γ δ b hb => by
        have h := v.crossed (e.symm γ) (e.symm δ) b
          (by show QuotientGroup.mk b = ρ (e (e.symm γ)); rwa [e.apply_symm_apply])
        rwa [← map_mul e.symm γ δ] at h }
  left_inv u := tCocycle_ext (funext fun β => congrArg u.u (e.apply_symm_apply β))
  right_inv v := tCocycle_ext (funext fun a => congrArg v.u (e.symm_apply_apply a))

variable {DD : DescData D}

/-- **`V`-cocycles transport.** -/
def vCocycleEquiv (e : A ≃ₜ* B) (DD : DescData D) (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) :
    VCocycle DD ρ ≃ VCocycle DD (precompEquiv e _ ρ) where
  toFun c :=
    { c := fun a => c.c (e a)
      cont := c.cont.comp e.continuous_toFun
      crossed := fun γ δ => by
        have h := c.crossed (e γ) (e δ)
        rwa [← map_mul e γ δ] at h }
  invFun v :=
    { c := fun β => v.c (e.symm β)
      cont := v.cont.comp e.symm.continuous_toFun
      crossed := fun γ δ => by
        have h := v.crossed (e.symm γ) (e.symm δ)
        rw [← map_mul e.symm γ δ] at h
        have hr : rho0 DD (precompEquiv e _ ρ) (e.symm γ) = rho0 DD ρ γ := by
          show liftC0 DD (ρ (e (e.symm γ))) = liftC0 DD (ρ γ)
          rw [e.apply_symm_apply]
        rwa [hr] at h }
  left_inv c := VCocycle.ext (funext fun β => congrArg c.c (e.apply_symm_apply β))
  right_inv v := VCocycle.ext (funext fun a => congrArg v.c (e.symm_apply_apply a))

omit [DiscreteTopology Bg] in
@[simp] theorem vCocycleEquiv_c (e : A ≃ₜ* B) (DD : DescData D)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (c : VCocycle DD ρ) (a : A) :
    (vCocycleEquiv e DD ρ c).c a = c.c (e a) := rfl

omit [DiscreteTopology Bg] in
theorem vCocycleEquiv_zero (e : A ≃ₜ* B) (DD : DescData D)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) :
    vCocycleEquiv e DD ρ 0 = 0 := VCocycle.ext rfl

variable {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
  (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [DiscreteTopology Bg] in
/-- The pointwise `B`-lift is transported pointwise — `rfl`. -/
theorem fLift_comp (e : A ≃ₜ* B) (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (c : VCocycle DD ρ)
    (a : A) : fLift S (vCocycleEquiv e DD ρ c) a = fLift S c (e a) := rfl

include hσ in
/-- The `T`-valued defect is transported along `e × e`. -/
theorem tDef_comp (e : A ≃ₜ* B) (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (c : VCocycle DD ρ)
    (p : A × A) : tDef S hσ (vCocycleEquiv e DD ρ c) p = tDef S hσ c (e p.1, e p.2) :=
  Subtype.ext (by
    show fLift S c (e p.1) * fLift S c (e p.2) * (fLift S c (e (p.1 * p.2)))⁻¹
      = fLift S c (e p.1) * fLift S c (e p.2) * (fLift S c (e p.1 * e p.2))⁻¹
    rw [map_mul e])

include hσ in
/-- …and so is its `χ`-pushforward. -/
theorem chiDef_comp (e : A ≃ₜ* B) (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (χ : ↥(TCharC D))
    (c : VCocycle DD ρ) :
    chiDef S hσ χ (vCocycleEquiv e DD ρ c) = fun p : A × A => chiDef S hσ χ c (e p.1, e p.2) :=
  funext fun p => congrArg (fun t : ↥D.T => χ.1 t) (tDef_comp S hσ e ρ c p)

include hσ in
/-- **`T`-liftability is a transport invariant.**  Both sides of the defining equation live in
`QLiftsOver`, a subtype of `Hom_c(Γ, B/T)`, so the witness moves by precomposition. -/
theorem tLiftable_comp (e : A ≃ₜ* B) (ρ : ContinuousMonoidHom B (Bg ⧸ D.M))
    (c : VCocycle DD ρ) : TLiftable hσ (vCocycleEquiv e DD ρ c) ↔ TLiftable hσ c := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨(mLiftsEquiv e D ρ).symm f, Subtype.ext (ContinuousMonoidHom.ext fun β => ?_)⟩
    have h := congrArg (fun g : QLiftsOver DD (precompEquiv e _ ρ) => g.1 (e.symm β)) hf
    show QuotientGroup.mk (f.1 (e.symm β)) = _
    refine h.trans ?_
    show iV DD (Multiplicative.ofAdd (c.c (e (e.symm β)))) * σ (rho0 DD ρ (e (e.symm β)))
      = iV DD (Multiplicative.ofAdd (c.c β)) * σ (rho0 DD ρ β)
    rw [e.apply_symm_apply]
  · rintro ⟨f, hf⟩
    exact ⟨mLiftsEquiv e D ρ f, Subtype.ext (ContinuousMonoidHom.ext fun a =>
      congrArg (fun g : QLiftsOver DD ρ => g.1 (e a)) hf)⟩

variable [DistribMulAction A (ZMod 2)] [DistribMulAction B (ZMod 2)]

include hσ in
/-- **The `χ`-component of the `T`-lifting obstruction is a transport invariant.** -/
theorem betaChi_comp (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (χ : ↥(TCharC D)) (c : VCocycle DD ρ) :
    betaChi S hσ χ (vCocycleEquiv e DD ρ c) = betaChi S hσ χ c := by
  rw [betaChi, betaChi, chiDef_comp S hσ e ρ χ c, iotaB_comp htA htB]

omit [DiscreteTopology Bg] in
/-- **The base determinant form `Q⁰` is a transport invariant.**  `graphPullback` is pointwise,
so this is `iotaB_comp` on the nose. -/
theorem qZero_comp (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B)
    (ρ : ContinuousMonoidHom B (Bg ⧸ D.M)) (c : VCocycle DD ρ) :
    QZero DD (precompEquiv e _ ρ) (vCocycleEquiv e DD ρ c) = QZero DD ρ c :=
  iotaB_comp htA htB e (graphPullback DD.dat (fun β => rho0 DD ρ β) c.c)

end Cocycles

/-! ## §6 The Gauss-`Z` residue

The last clause-level family: a `finsum` of `sign ∘ Q⁰` over `V`-cocycles, so §5's
`vCocycleEquiv` reindexes it and §5's `qZero_comp` matches the summands. -/

section GaussZ

variable {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
variable {A B : Type} [Group A] [TopologicalSpace A] [DistribMulAction A (ZMod 2)]
  [Group B] [TopologicalSpace B] [DistribMulAction B (ZMod 2)]

/-- **The Gauss-`Z` residue is a transport invariant.** -/
theorem gaussZResidueK_comp (htA : ∀ (γ : A) (m : ZMod 2), γ • m = m)
    (htB : ∀ (γ : B) (m : ZMod 2), γ • m = m) (e : A ≃ₜ* B)
    (b : ContinuousMonoidHom B ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) (G0 : ℤ)
    (hG : GaussZResidueK b F En l h G0) : GaussZResidueK (precompEquiv e _ b) F En l h G0 := by
  intro ρ₁
  obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F RF.TC).surjective ρ₁
  refine Eq.trans ?_ (hG ρ)
  refine Eq.trans (finsum_comp_equiv
    (vCocycleEquiv e (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))).symm ?_
  exact finsum_congr fun c => congrArg _ (qZero_comp htA htB e _ c)

end GaussZ

end GQ2.Dyadic.SourceTransport

/-! ## §7 The record-level transport -/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight GQ2.Dyadic.SourceTransport
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

/-- The boundary map of a precomposed tame/pro-2 pair **is** the precomposed boundary map —
`rfl`, since `sourceBoundaryMapK` is a `codRestrict` of a pointwise pair. -/
theorem sourceBoundaryMapK_comp {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {ΓA ΓB : ProfiniteGrp} (e : ContinuousMulEquiv ((ΓA : Type)) ((ΓB : Type)))
    (tame : ContinuousMonoidHom ΓB (Tq q)) (pro2 : ContinuousMonoidHom ΓB P)
    (compat : ∀ g : ΓB, nuTq q (tame g) = nuP (pro2 g)) :
    sourceBoundaryMapK (nuP := nuP)
        (tame.comp (e : ContinuousMonoidHom ((ΓA : Type)) ((ΓB : Type))))
        (pro2.comp (e : ContinuousMonoidHom ((ΓA : Type)) ((ΓB : Type))))
        (fun g => compat (e g))
      = precompEquiv e _ (sourceBoundaryMapK tame pro2 compat) := rfl

/-- **`SourceDataN` transport across a continuous isomorphism of carriers** (ticket CB-TRN).

Given a source `S` over the abstract slot `(n, q, P, hP, νP, SN)` and a topological isomorphism
`e : Γ' ≃ₜ* S.Γ`, this produces the *same* source read on `Γ'`: `tame`, `pro2` and the boundary
map are precomposed with `e`, and every one of the seven supply-obligation families is moved by
§§1–6.

The scalar action is **not** transported: `Γ'` carries its own `DistribMulAction _ (ZMod 2)`,
supplied here together with its continuity and triviality, because that is the shape every
consumer (`WordCertificate.smulZmod2`, `SourceDataN.smulZmod2`) already has.  Triviality of
*both* actions is what makes `ι_Γ` — hence `betaChi`, `QZero` and `#H²` — transportable at all;
it is the one genuine hypothesis of the construction. -/
noncomputable def SourceDataN.transport {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (S : SourceDataN n q P hP nuP SN) {Γ' : ProfiniteGrp}
    (e : ContinuousMulEquiv ((Γ' : Type)) ((S.Γ : Type)))
    (smul' : DistribMulAction ↥Γ' (ZMod 2))
    (hcont' : letI := smul'; ContinuousSMul ↥Γ' (ZMod 2))
    (htriv' : letI := smul'; ∀ (γ : ↥Γ') (m : ZMod 2), γ • m = m) :
    SourceDataN n q P hP nuP SN where
  Γ := Γ'
  tame := S.tame.comp (e : ContinuousMonoidHom ((Γ' : Type)) ((S.Γ : Type)))
  pro2 := S.pro2.comp (e : ContinuousMonoidHom ((Γ' : Type)) ((S.Γ : Type)))
  compat := fun g => S.compat (e g)
  surj := fun z => by
    obtain ⟨g, hg⟩ := S.surj z
    obtain ⟨a, rfl⟩ := e.surjective g
    exact ⟨a, hg⟩
  ker_pro2 := ker_comp_continuousMulEquiv e S.pro2 S.ker_pro2
  smulZmod2 := smul'
  contSMulZmod2 := hcont'
  htriv := htriv'
  tfg := IsTopologicallyFinGen.of_surjective
    (e.symm : ContinuousMonoidHom ((S.Γ : Type)) ((Γ' : Type))).toMonoidHom
    (e.symm : ContinuousMonoidHom ((S.Γ : Type)) ((Γ' : Type))).continuous_toFun
    e.symm.surjective S.tfg
  homCard := (Nat.card_congr (precompEquiv e (Multiplicative (ZMod 2)))).symm.trans S.homCard
  cardH2 := by
    letI := S.smulZmod2
    exact (card_H2_comp htriv' S.htriv e).trans S.cardH2
  liftsOver_card := fun RF b₁ F ρ₁ => by
    obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
    obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F RF.TC).surjective ρ₁
    exact (Nat.card_congr (liftsOverKEquiv e RF b F ρ)).symm.trans (S.liftsOver_card RF b F ρ)
  lem86 := fun Dd hnd ρ₁ hρ₁ => by
    obtain ⟨ρ, rfl⟩ := (precompEquiv e _).surjective ρ₁
    have hρ : Function.Surjective ρ := fun y => by
      obtain ⟨a, ha⟩ := hρ₁ y; exact ⟨e a, ha⟩
    rw [(Nat.card_congr (Equiv.subtypeEquiv (mLiftsEquiv e Dd ρ)
        fun f => (mLiftsEquiv_central e Dd ρ f).symm)).symm,
      (Nat.card_congr (mLiftsEquiv e Dd ρ)).symm]
    exact S.lem86 Dd hnd ρ hρ
  stageR136 := fun hE2 hRK hR2 b₁ F => by
    obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
    simp only [exactImageCountK_comp, mBK_comp]
    exact S.stageR136 hE2 hRK hR2 b F
  tcocycle_card := fun b₁ F En l h ρ₁ => by
    obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
    obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
    exact (Nat.card_congr (tCocycleEquiv e (rhoPrimeK _ b F (En.radData l h) rfl ρ))).symm.trans
      (S.tcocycle_card b F En l h ρ)
  hsep := fun b₁ F En l h Dsc ρ₁ c₁ hc => by
    letI := S.smulZmod2
    obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
    obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
    obtain ⟨c, rfl⟩ := (vCocycleEquiv e (En.descData l h)
      (rhoPrimeK _ b F (En.radData l h) rfl ρ)).surjective c₁
    refine (tLiftable_comp (descSigma_spec En l h Dsc) e _ c).mpr
      (S.hsep b F En l h Dsc ρ c fun χ => ?_)
    exact (betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
      htriv' S.htriv e _ χ c).symm.trans (hc χ)
  hpartial := fun b₁ F En l h Dsc ρ₁ χ hχ => by
    letI := S.smulZmod2
    obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
    obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
    obtain ⟨c, hcne⟩ := S.hpartial b F En l h Dsc ρ χ hχ
    refine ⟨vCocycleEquiv e (En.descData l h) _ c, fun heq => hcne ?_⟩
    have h1 := betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
      htriv' S.htriv e (rhoPrimeK _ b F (En.radData l h) rfl ρ) χ c
    have h2 := betaChi_comp (descSections En l h Dsc) (descSigma_spec En l h Dsc)
      htriv' S.htriv e (rhoPrimeK _ b F (En.radData l h) rfl ρ) χ 0
    exact h1.symm.trans (heq.trans h2)
  hZcard := fun b₁ F En l h hsimple hVne hnt ρ₁ => by
    obtain ⟨b, rfl⟩ := (precompEquiv e _).surjective b₁
    obtain ⟨ρ, rfl⟩ := (boundaryLiftsKEquiv e b F _).surjective ρ₁
    exact (Nat.card_congr (vCocycleEquiv e (En.descData l h)
      (rhoPrimeK _ b F (En.radData l h) rfl ρ))).symm.trans
      (S.hZcard b F En l h hsimple hVne hnt ρ)
  gaussZ_unramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram => by
    letI := S.smulZmod2
    exact gaussZResidueK_comp htriv' S.htriv e _ F _ l h _
      (S.gaussZ_unramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram)
  gaussZ_ramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram => by
    letI := S.smulZmod2
    exact gaussZResidueK_comp htriv' S.htriv e _ F _ l h _
      (S.gaussZ_ramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram)

/-- Changing the tame leg of a boundary map along an equality of homs; the `compat` legs are
proofs, so they need no relation.  (`rw [h]` cannot do this directly: `compat`'s *type* mentions
`tame`.) -/
theorem sourceBoundaryMapK_congr {q : ℕ} {P Γ : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {tame tame' : ContinuousMonoidHom Γ (Tq q)} {pro2 : ContinuousMonoidHom Γ P}
    (h : tame = tame') (compat : ∀ g : Γ, nuTq q (tame g) = nuP (pro2 g))
    (compat' : ∀ g : Γ, nuTq q (tame' g) = nuP (pro2 g)) :
    sourceBoundaryMapK tame pro2 compat = sourceBoundaryMapK tame' pro2 compat' := by
  subst h; rfl

/-! ## §8 The application: the genuine `n = 1` `WordCertificate`

AS4 left `WordCertificate`'s four analytic clauses open at `(n, q, R) = (1, 2, L_sq)` because
`sourceR_N`'s counts are statements about the `ℚ₂` carrier `GQ2.GammaR`.  §7 moves the whole
record across AS4's marked identification `gammaR_lSq_equiv_roe`, which closes them. -/

section NEqOne

open GQ2.Dyadic.QTwo GQ2.Dyadic.Words.LSq

noncomputable local instance absGalQ2_compactSpace_cbtrn : CompactSpace AbsGalQ2 := by
  change CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

noncomputable local instance absGalQ2_totallyDisconnectedSpace_cbtrn :
    TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

/-- **SD-R1's `n = 1` `Γ_R` source, read on the `L_sq` candidate group.**  `sourceR_N` at the
L-campaign's `GQ2.Roe.Labute.bLab`, transported along AS4's `gammaR_lSq_equiv_roe`; the scalar
trio is AS4-b's. -/
noncomputable def sourceLSq :
    SourceDataN 1 2 PiBd SectionThree.piBd_isProP nuTwo (standardNumerics 1) :=
  (sourceR_N GQ2.Roe.Labute.bLab).transport (Γ' := candidateGroup 1 2 (lSqW 0))
    gammaR_lSq_equiv_roe (gammaRSMulZmod2 1 2 (lSqW 0)) (gammaRContSMulZmod2 1 2 (lSqW 0))
    (gammaR_htriv 1 2 (lSqW 0))

@[simp] theorem sourceLSq_Γ : sourceLSq.Γ = candidateGroup 1 2 (lSqW 0) := rfl

/-- **F3b's tame specialization at `L_sq` is Roe's `φ_R`, read through §4 of AS4.**  Both are
continuous homs out of `Γ_{L_sq,1}`, so AS4-b's `gammaR_hom_ext` reduces the claim to the four
marked letters; on the left they are `tameMarking`'s, on the right AS4's `toRoe_*` followed by
`phiR_gamma*`. -/
theorem tameOfSpec_lSq_eq :
    TameSpec.tameOfSpec 1 2 (lSqW 0) tameSpecializes_lSq = sourceLSq.tame := by
  refine gammaR_hom_ext fun x => ?_
  -- ⚠ `rw` cannot be used to move to `sourceLSq.tame`: `sourceLSq.Γ` and `GammaR 1 2 (lSqW 0)`
  -- are the same type through different instance paths (AS4-b's recorded friction), so the
  -- rewrite motive fails at `instances` transparency where `show`/`exact` succeed.
  refine Eq.trans (TameSpec.tameOfSpec_gammaGen _ x) ?_
  show (tameMarking 1 2) x = phiR (toRoe (gammaGen 1 2 (lSqW 0) x))
  match x with
  | .sigma => rw [toRoe_sigma]; exact phiR_gammaSigma.symm
  | .tau => rw [toRoe_tau]; exact phiR_gammaTau.symm
  | .wild ⟨0, _⟩ =>
    show tameMarking 1 2 (Generator.wild 0)
      = phiR (toRoe (gammaGen 1 2 (lSqW 0) (Generator.wild 0)))
    rw [toRoe_x0]; exact phiR_gammaX0.symm
  | .wild ⟨1, _⟩ =>
    show tameMarking 1 2 (Generator.wild 1)
      = phiR (toRoe (gammaGen 1 2 (lSqW 0) (Generator.wild 1)))
    rw [toRoe_x1]; exact phiR_gammaX1.symm
  | .wild ⟨k + 2, hk⟩ => exact absurd hk (by omega)

/-- **The `n = 1` word certificate** (ticket CB-TRN's deliverable).

AS1's `WordCertificate` at `(n, q, R) = (1, 2, L_sq)` over SD-R1's slot
`(Π, ν₂, standardNumerics 1)`, **unconditional**: the `B`-Lab binder is `GQ2.Roe.Labute.bLab`
and the `AbsGalQ2` topology instances are file-local, exactly as in AS4's `DyadicRoute`.

Field provenance: `tameSpecialization`/`coreRel`/`proTwoWord`/`htame`/`hwild` are AS4's §6, the
scalar trio is AS4-b's §3, and the eight remaining fields — the whole eq.-(27) interface plus the
four analytic clauses AS4 could not cite — are `sourceLSq`, i.e. `sourceR_N` transported. -/
noncomputable def wordCertificateLSq :
    WordCertificate 1 2 (lSqW 0) PiBd SectionThree.piBd_isProP nuTwo (standardNumerics 1) where
  tameSpecialization := tameSpecializes_lSq
  coreRel := coreRelLSq
  proTwoWord := proTwoWord_lSq
  pro2 := sourceLSq.pro2
  ker_pro2 := sourceLSq.ker_pro2
  hpro2 := sourceLSq.pro2_surjective
  compat := fun g => by rw [tameOfSpec_lSq_eq]; exact sourceLSq.compat g
  tfg := sourceLSq.tfg
  smulZmod2 := gammaRSMulZmod2 1 2 (lSqW 0)
  contSMulZmod2 := gammaRContSMulZmod2 1 2 (lSqW 0)
  htriv := gammaR_htriv 1 2 (lSqW 0)
  exactLifting := ⟨fun RF b F ρ => sourceLSq.liftsOver_card RF b F ρ,
    fun D hnd ρ hρ => sourceLSq.lem86 D hnd ρ hρ,
    fun hE2 hRK hR2 b F => sourceLSq.stageR136 hE2 hRK hR2 b F⟩
  stokes := ⟨fun b F En l h ρ => sourceLSq.tcocycle_card b F En l h ρ,
    fun b F En l h Dsc ρ c hc => sourceLSq.hsep b F En l h Dsc ρ c hc,
    fun b F En l h Dsc ρ χ hχ => sourceLSq.hpartial b F En l h Dsc ρ χ hχ,
    fun b F En l h hsimple hVne hnt ρ => sourceLSq.hZcard b F En l h hsimple hVne hnt ρ⟩
  scalar := ⟨sourceLSq.homCard, sourceLSq.cardH2⟩
  determinant :=
    ⟨fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram => by
      rw [sourceBoundaryMapK_congr tameOfSpec_lSq_eq _ sourceLSq.compat]
      exact sourceLSq.gaussZ_unramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hunram,
    fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram => by
      rw [sourceBoundaryMapK_congr tameOfSpec_lSq_eq _ sourceLSq.compat]
      exact sourceLSq.gaussZ_ramified T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l h hram⟩
  htame := htame_lSq
  hwild := hwild_lSq_one

end NEqOne

end GQ2.Dyadic
