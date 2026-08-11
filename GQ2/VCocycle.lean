/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.AffineTLift

/-!
# The crossed `V`-cocycle layer

The `V`-side mirror of `CentralObstruction.TCocycle`, and the semidirect bijection it powers.
In the zero-edge regime `descended_splitting` (`AffineTLift.lean:503`) presents `Q = Bg/T` as a
split extension `1 → V → Q → C₀ → 1` (`B/T ≅ V ⋊ C₀`), so the continuous homomorphisms
`Γ → Q` over a fixed lower map `ρ' : Γ → C₀` are exactly the continuous **crossed `V`-cocycles**
`Z¹_{Γ,ρ}(V)`.  This file builds:

* **`rho0`** — the `C₀`-valued lower map `Γ → C₀` induced by `ρ : Γ → Bg/M` (through `piC₀`);
* **`VCocycle`** — a continuous crossed `1`-cocycle `Γ → V` over `ρ`, mirroring `TCocycle`,
  with its `AddCommGroup` structure;
* **`vCob`** — the principal-coboundary map `V → Z¹`, `v ↦ (γ ↦ ρ'(γ)·v − v)`, an `AddMonoidHom`,
  and `vCob_eq_zero_iff` (its kernel is the `ρ'`-fixed vectors — **freeness when `V^C = 0`**);
* **`vcocycleEquivLifts`** — the bijection `VCocycle ≃ {g : Γ →ₜ Q // piQbar ∘ g = ρ'}` via a
  splitting `σ` of `piQbar`;
* the **`B¹`-translation facts** — conjugating an `M`-lift `f` by `m ∈ M` keeps it over the same
  `ρ` (`mConj`), preserves `Central` (`mConj_central`), and translates its `T`-reduction `redT f`
  by the coboundary `vCob (descend m)` (`cocycleOf_mConj`).  This is the group-theoretic core of
  the Bug-1 recalibration (`docs/orchestration/p16d6c-handoff.md` §⚠): the central `red_T`-image is a free
  `B¹ = V`-torsor bundle, so its cardinality carries the missing `|B¹| = #V` factor (c1s), whose
  arithmetic close is c1c.

Since `DescData`'s `V`/`C₀` are opaque finite types (no topology), continuity of a `V`-cochain
`c : Γ → V` is stored through its embedding `iV ∘ ofAdd` into the discrete `Q = Bg/T`, and the
`σ ∘ ρ'` continuity factors through the discrete `Bg/M`.  Everything is source-generic
(`RadicalCoverData` + `DescData`), finite-group / generic-`Γ`; no B6/B7, all std-3.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- The quotient `Bg ⧸ D.T` of the discrete group `Bg` is discrete (mirror of
`CentralObstruction.discreteTopology_quotient`). -/
instance discreteTopology_quotient_T : DiscreteTopology (Bg ⧸ D.T) := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  rw [← Set.image_preimage_eq ({c} : Set (Bg ⧸ D.T)) QuotientGroup.mk_surjective]
  exact QuotientGroup.isOpenMap_coe _ (isOpen_discrete _)

section VCocycleLayer

variable (DD : DescData D) (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M))

/-- `piC₀` descends through `M = ker piC₀` to a map `Bg/M → C₀`. -/
noncomputable def liftC0 : (Bg ⧸ D.M) →* DD.C0 :=
  QuotientGroup.lift D.M DD.piC0 DD.hkerC0.ge

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
@[simp] theorem liftC0_mk (b : Bg) : liftC0 DD (QuotientGroup.mk b) = DD.piC0 b :=
  QuotientGroup.lift_mk' _ _ b

/-- **The `C₀`-valued lower map** `ρ' : Γ → C₀`, the descent of `ρ : Γ → Bg/M` through `piC₀`. -/
noncomputable def rho0 : Γ →* DD.C0 := (liftC0 DD).comp ρ.toMonoidHom

omit [DiscreteTopology Bg] in
/-- `ρ'(γ) = piC₀(b)` for any representative `b` of `ρ(γ)`. -/
theorem rho0_apply_of_rep (γ : Γ) (b : Bg) (hb : QuotientGroup.mk b = ρ γ) :
    rho0 DD ρ γ = DD.piC0 b := by
  show liftC0 DD (ρ γ) = DD.piC0 b
  rw [← hb, liftC0_mk]

/-- **A continuous crossed `V`-valued 1-cocycle over `ρ`** (the paper's `c ∈ Z¹_{Γ,ρ}(V)`):
`c(γδ) = c(γ) + ρ'(γ)·c(δ)`, with `ρ' = rho0` the `C₀`-valued descent of `ρ`.  The `V`-side
mirror of `TCocycle` (additive, valued directly in `V = M/T`).  Continuity is stored through the
embedding `iV ∘ ofAdd` into the discrete `Q = Bg/T`, since `V` carries no topology. -/
structure VCocycle where
  /-- The underlying function, valued in `V`. -/
  c : Γ → DD.Vmod
  cont : Continuous (fun γ => iV DD (Multiplicative.ofAdd (c γ)))
  crossed : ∀ γ δ : Γ, c (γ * δ) = c γ + rho0 DD ρ γ • c δ

variable {DD ρ}

omit [DiscreteTopology Bg] in
@[ext] theorem VCocycle.ext {u v : VCocycle DD ρ} (h : u.c = v.c) : u = v := by
  cases u; cases v; simp only [VCocycle.mk.injEq]; exact h

omit [DiscreteTopology Bg] in
/-- A crossed cocycle vanishes at `1`. -/
@[simp] theorem VCocycle.c_one (u : VCocycle DD ρ) : u.c 1 = 0 := by
  have h := u.crossed 1 1
  rw [mul_one, map_one, one_smul] at h
  simpa using h

/-! ### The additive structure on `Z¹` and the coboundary map -/

instance : Zero (VCocycle DD ρ) where
  zero :=
    { c := fun _ => 0
      cont := continuous_const
      crossed := fun γ δ => by simp }

omit [DiscreteTopology Bg] in
@[simp] theorem VCocycle.zero_c : (0 : VCocycle DD ρ).c = fun _ => 0 := rfl

instance : Add (VCocycle DD ρ) where
  add u w :=
    { c := fun γ => u.c γ + w.c γ
      cont := by
        simp only [ofAdd_add, map_mul]
        exact u.cont.mul w.cont
      crossed := fun γ δ => by
        show u.c (γ * δ) + w.c (γ * δ) = (u.c γ + w.c γ) + rho0 DD ρ γ • (u.c δ + w.c δ)
        rw [u.crossed, w.crossed, smul_add]; abel }

@[simp] theorem VCocycle.add_c (u w : VCocycle DD ρ) : (u + w).c = fun γ => u.c γ + w.c γ := rfl

/-- **The principal coboundary** `δv ∈ B¹_{Γ,ρ}(V)` of a vector `v : V`: `γ ↦ ρ'(γ)·v − v`.
This is the mathematical core of the Bug-1 recalibration: conjugating an `M`-lift by a lift of
`v` translates its `T`-reduction cocycle by `vCob v`. -/
noncomputable def vCob (DD : DescData D) (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)) (v : DD.Vmod) :
    VCocycle DD ρ where
  c := fun γ => rho0 DD ρ γ • v - v
  cont := (continuous_of_discreteTopology
      (f := fun x : Bg ⧸ D.M => iV DD (Multiplicative.ofAdd (liftC0 DD x • v - v)))).comp
    ρ.continuous_toFun
  crossed := fun γ δ => by
    show rho0 DD ρ (γ * δ) • v - v
      = (rho0 DD ρ γ • v - v) + rho0 DD ρ γ • (rho0 DD ρ δ • v - v)
    rw [map_mul, mul_smul, smul_sub]; abel

@[simp] private theorem vCob_c (DD : DescData D) (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)) (v : DD.Vmod) :
    (vCob DD ρ v).c = fun γ => rho0 DD ρ γ • v - v := rfl

/-- `vCob` is additive: `δ(v + w) = δv + δw`. -/
theorem vCob_add (v w : DD.Vmod) : vCob DD ρ (v + w) = vCob DD ρ v + vCob DD ρ w := by
  ext γ
  show rho0 DD ρ γ • (v + w) - (v + w)
    = (rho0 DD ρ γ • v - v) + (rho0 DD ρ γ • w - w)
  rw [smul_add]; abel

@[simp] private theorem vCob_zero : vCob DD ρ (0 : DD.Vmod) = 0 := by
  ext γ; show rho0 DD ρ γ • (0 : DD.Vmod) - 0 = 0; rw [smul_zero, sub_zero]

/-- **Freeness criterion** (`V^C = 0` clause of Bug 1): the coboundary `vCob v` is the trivial
cocycle iff `v` is fixed by every `ρ'(γ)`.  When `V` has no nonzero `im ρ'`-fixed vector (e.g.
`V^C = 0` with `ρ'` surjective), `v ↦ vCob v` is injective, so `B¹ ≅ V`. -/
theorem vCob_c_eq_zero_iff (v : DD.Vmod) :
    (vCob DD ρ v).c = (fun _ => 0) ↔ ∀ γ : Γ, rho0 DD ρ γ • v = v := by
  constructor
  · intro h γ
    simpa [sub_eq_zero] using congrFun h γ
  · intro h; funext γ; show rho0 DD ρ γ • v - v = 0; rw [h, sub_self]

/-- **Freeness of the `B¹`-translation** (the `V^C = 0` clause of Bug 1): if `V` carries no
nonzero `ρ'`-fixed vector (e.g. `V^C = 0` with `ρ'` surjective), the coboundary map `v ↦ vCob v`
is injective — the `V`-action by `B¹`-translation is free, so `B¹ ≅ V`.  This is what supplies the
missing `|B¹| = #V` factor of the c1s recalibration. -/
theorem vCob_injective (hfix : ∀ v : DD.Vmod, (∀ γ : Γ, rho0 DD ρ γ • v = v) → v = 0) :
    Function.Injective (vCob DD ρ) := by
  intro v w h
  apply sub_eq_zero.mp
  apply hfix
  intro γ
  rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
  simpa using congrFun (congrArg VCocycle.c h) γ

end VCocycleLayer

/-! ### The semidirect bijection `VCocycle ≃ {Γ →ₜ Q over ρ'}`

Via a splitting `σ : C₀ → Q` of `piQbar` (from `descended_splitting`), `Q = Bg/T ≅ V ⋊ C₀`, and a
continuous hom `Γ → Q` over `ρ'` decomposes as `γ ↦ iV(c γ) · σ(ρ'γ)` with `c ∈ Z¹_{Γ,ρ}(V)`. -/

section PureAlgebra
omit [TopologicalSpace Bg] [DiscreteTopology Bg]

/-- `iV` lands in `ker piQbar`. -/
@[simp] theorem piQbar_iV (DD : DescData D) (x : Multiplicative DD.Vmod) :
    piQbar DD (iV DD x) = 1 :=
  MonoidHom.mem_ker.mp (by rw [← iV_range]; exact ⟨x, rfl⟩)

/-- Every `q ∈ ker piQbar` is `iV(ofAdd v)` for some `v : V`. -/
theorem exists_iV_preimage (DD : DescData D) (q : Bg ⧸ D.T) (hq : piQbar DD q = 1) :
    ∃ v : DD.Vmod, iV DD (Multiplicative.ofAdd v) = q := by
  obtain ⟨w, hw⟩ : q ∈ (iV DD).range := by rw [iV_range]; exact MonoidHom.mem_ker.mpr hq
  exact ⟨Multiplicative.toAdd w, hw⟩

/-- `iV ∘ ofAdd` is injective on `V`. -/
theorem iV_ofAdd_inj (DD : DescData D) {a b : DD.Vmod}
    (h : iV DD (Multiplicative.ofAdd a) = iV DD (Multiplicative.ofAdd b)) : a = b :=
  Multiplicative.ofAdd.injective (iV_injective DD h)

/-- `iV ∘ ofAdd` sends `+` to `*`. -/
@[simp] theorem iV_ofAdd_add (DD : DescData D) (a b : DD.Vmod) :
    iV DD (Multiplicative.ofAdd (a + b))
      = iV DD (Multiplicative.ofAdd a) * iV DD (Multiplicative.ofAdd b) := by
  rw [ofAdd_add, map_mul]

/-- `iV ∘ ofAdd` sends negation to inversion. -/
@[simp] theorem iV_ofAdd_inv (DD : DescData D) (a : DD.Vmod) :
    iV DD (Multiplicative.ofAdd (-a)) = (iV DD (Multiplicative.ofAdd a))⁻¹ := by
  rw [ofAdd_neg, map_inv]

end PureAlgebra

/-- Continuous homomorphisms `Γ → Q = Bg/T` lying over the lower map `ρ' = rho0`. -/
abbrev QLiftsOver (DD : DescData D) (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)) : Type :=
  {g : ContinuousMonoidHom Γ (Bg ⧸ D.T) // ∀ γ : Γ, piQbar DD (g γ) = rho0 DD ρ γ}

/-! ### `M`-lift conjugation and `T`-reduction as a hom over `ρ'` -/

section Translation

variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

/-- The `T`-reduction of an `M`-lift, packaged as a hom `Γ → Q = Bg/T` over `ρ'`. -/
noncomputable def redTLift (DD : DescData D) (f : MLifts D ρ) : QLiftsOver DD ρ :=
  ⟨⟨MonoidHom.mk' (fun γ => QuotientGroup.mk (f.1 γ))
      (fun γ δ => by rw [map_mul, QuotientGroup.mk_mul]),
     (continuous_of_discreteTopology
        (f := (QuotientGroup.mk : Bg → Bg ⧸ D.T))).comp f.1.continuous_toFun⟩,
   fun γ => by
     show piQbar DD (QuotientGroup.mk (f.1 γ)) = rho0 DD ρ γ
     rw [show (QuotientGroup.mk (f.1 γ) : Bg ⧸ D.T) = piT (D := D) (f.1 γ) from rfl, piQbar_mk,
       rho0_apply_of_rep DD ρ γ (f.1 γ) (f.2 γ)]⟩

@[simp] theorem redTLift_apply (DD : DescData D) (f : MLifts D ρ) (γ : Γ) :
    (redTLift DD f).1 γ = QuotientGroup.mk (f.1 γ) := rfl

/-- **Conjugation of an `M`-lift by `m ∈ M`**: still an `M`-lift over the same `ρ` (since
`mk_M m = 1`). -/
def mConj (m : Bg) (hm : m ∈ D.M) (f : MLifts D ρ) : MLifts D ρ :=
  ⟨⟨MonoidHom.mk' (fun γ => m * f.1 γ * m⁻¹) (fun γ δ => by
       show m * f.1 (γ * δ) * m⁻¹ = (m * f.1 γ * m⁻¹) * (m * f.1 δ * m⁻¹)
       rw [map_mul]; group),
     (continuous_of_discreteTopology (f := fun x : Bg => m * x * m⁻¹)).comp f.1.continuous_toFun⟩,
   fun γ => by
     show QuotientGroup.mk (m * f.1 γ * m⁻¹) = ρ γ
     have hm1 : (QuotientGroup.mk m : Bg ⧸ D.M) = 1 := (QuotientGroup.eq_one_iff m).mpr hm
     rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hm1, one_mul, inv_one,
       mul_one, f.2 γ]⟩

@[simp] private theorem mConj_apply (m : Bg) (hm : m ∈ D.M) (f : MLifts D ρ) (γ : Γ) :
    (mConj m hm f).1 γ = m * f.1 γ * m⁻¹ := rfl

/-- Conjugation by `m ∈ M` preserves the central relation. -/
theorem mConj_central {m : Bg} (hm : m ∈ D.M) {f : MLifts D ρ} (hf : f.Central) :
    (mConj m hm f).Central := by
  obtain ⟨g, hg⟩ := hf
  refine ⟨⟨MonoidHom.mk'
      (fun γ => Function.surjInv D.C.surj m * g γ * (Function.surjInv D.C.surj m)⁻¹)
      (fun γ δ => by
        show Function.surjInv D.C.surj m * g (γ * δ) * (Function.surjInv D.C.surj m)⁻¹
          = (Function.surjInv D.C.surj m * g γ * (Function.surjInv D.C.surj m)⁻¹)
            * (Function.surjInv D.C.surj m * g δ * (Function.surjInv D.C.surj m)⁻¹)
        rw [map_mul]; group),
     (continuous_of_discreteTopology
        (f := fun x : D.C.cover =>
          Function.surjInv D.C.surj m * x * (Function.surjInv D.C.surj m)⁻¹)).comp
       g.continuous_toFun⟩,
   fun γ => by
     show D.C.p (Function.surjInv D.C.surj m * g γ * (Function.surjInv D.C.surj m)⁻¹)
       = m * f.1 γ * m⁻¹
     rw [map_mul, map_mul, map_inv, Function.surjInv_eq D.C.surj m, hg γ]⟩

end Translation

section Splitting

variable (DD : DescData D) (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M))
  (σ : DD.C0 →* Bg ⧸ D.T) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- `σ` conjugates `iV(ofAdd v)` to `iV(ofAdd (cc·v))` (the semidirect action via `iV_conj`). -/
theorem sigma_conj_iV (cc : DD.C0) (v : DD.Vmod) :
    σ cc * iV DD (Multiplicative.ofAdd v) * (σ cc)⁻¹ = iV DD (Multiplicative.ofAdd (cc • v)) := by
  rw [iV_conj DD (σ cc) v, hσ]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- The commutation form: `σ(cc)·iV(v) = iV(cc·v)·σ(cc)`. -/
theorem sigma_iV_comm (cc : DD.C0) (v : DD.Vmod) :
    σ cc * iV DD (Multiplicative.ofAdd v)
      = iV DD (Multiplicative.ofAdd (cc • v)) * σ cc := by
  rw [← sigma_conj_iV DD σ hσ cc v]; group

/-- `γ ↦ σ(ρ'γ)` is continuous (it factors through the discrete `Bg/M`). -/
theorem sigma_rho0_continuous : Continuous (fun γ => σ (rho0 DD ρ γ)) :=
  (continuous_of_discreteTopology (f := fun x : Bg ⧸ D.M => σ (liftC0 DD x))).comp
    ρ.continuous_toFun

include hσ in
/-- **Forward map** of the semidirect bijection: a crossed cocycle `c` gives the continuous hom
`γ ↦ iV(c γ) · σ(ρ'γ)` over `ρ'`. -/
noncomputable def qOfCocycle (u : VCocycle DD ρ) : QLiftsOver DD ρ :=
  ⟨⟨MonoidHom.mk'
      (fun γ => iV DD (Multiplicative.ofAdd (u.c γ)) * σ (rho0 DD ρ γ))
      (fun γ δ => by
        calc iV DD (Multiplicative.ofAdd (u.c (γ * δ))) * σ (rho0 DD ρ (γ * δ))
            = iV DD (Multiplicative.ofAdd (u.c γ + rho0 DD ρ γ • u.c δ))
                * σ (rho0 DD ρ γ * rho0 DD ρ δ) := by
              rw [u.crossed γ δ, map_mul (rho0 DD ρ) γ δ]
          _ = iV DD (Multiplicative.ofAdd (u.c γ))
                * iV DD (Multiplicative.ofAdd (rho0 DD ρ γ • u.c δ))
                * (σ (rho0 DD ρ γ) * σ (rho0 DD ρ δ)) := by
              rw [ofAdd_add, map_mul, map_mul σ]
          _ = iV DD (Multiplicative.ofAdd (u.c γ))
                * (iV DD (Multiplicative.ofAdd (rho0 DD ρ γ • u.c δ)) * σ (rho0 DD ρ γ))
                * σ (rho0 DD ρ δ) := by group
          _ = iV DD (Multiplicative.ofAdd (u.c γ))
                * (σ (rho0 DD ρ γ) * iV DD (Multiplicative.ofAdd (u.c δ)))
                * σ (rho0 DD ρ δ) := by rw [← sigma_iV_comm DD σ hσ]
          _ = iV DD (Multiplicative.ofAdd (u.c γ)) * σ (rho0 DD ρ γ)
                * (iV DD (Multiplicative.ofAdd (u.c δ)) * σ (rho0 DD ρ δ)) := by group),
     u.cont.mul (sigma_rho0_continuous DD ρ σ)⟩,
   fun γ => by
     show piQbar DD (iV DD (Multiplicative.ofAdd (u.c γ)) * σ (rho0 DD ρ γ)) = rho0 DD ρ γ
     rw [map_mul, piQbar_iV, one_mul, hσ]⟩

@[simp] theorem qOfCocycle_apply (u : VCocycle DD ρ) (γ : Γ) :
    (qOfCocycle DD ρ σ hσ u).1 γ = iV DD (Multiplicative.ofAdd (u.c γ)) * σ (rho0 DD ρ γ) := rfl

omit [DiscreteTopology Bg] in
include hσ in
/-- The `V`-coordinate of a hom `g : Γ → Q` over `ρ'` exists: `g γ · σ(ρ'γ)⁻¹ ∈ ker piQbar`. -/
theorem exists_cocycleFun (g : QLiftsOver DD ρ) (γ : Γ) :
    ∃ v : DD.Vmod, iV DD (Multiplicative.ofAdd v) = g.1 γ * (σ (rho0 DD ρ γ))⁻¹ :=
  exists_iV_preimage DD _ (by rw [map_mul, map_inv, g.2 γ, hσ, mul_inv_cancel])

include hσ in
/-- **Inverse map** of the semidirect bijection: the `V`-coordinate cocycle of a hom `g` over
`ρ'`, `c γ := iV⁻¹(g γ · σ(ρ'γ)⁻¹)`. -/
noncomputable def cocycleOfQ (g : QLiftsOver DD ρ) : VCocycle DD ρ where
  c := fun γ => Classical.choose (exists_cocycleFun DD ρ σ hσ g γ)
  cont := (g.1.continuous_toFun.mul (continuous_inv.comp (sigma_rho0_continuous DD ρ σ))).congr
    fun γ => (Classical.choose_spec (exists_cocycleFun DD ρ σ hσ g γ)).symm
  crossed := fun γ δ => by
    apply iV_ofAdd_inj DD
    have hγδ := Classical.choose_spec (exists_cocycleFun DD ρ σ hσ g (γ * δ))
    have hγ := Classical.choose_spec (exists_cocycleFun DD ρ σ hσ g γ)
    have hδ := Classical.choose_spec (exists_cocycleFun DD ρ σ hσ g δ)
    rw [hγδ, ofAdd_add, map_mul (iV DD),
      ← sigma_conj_iV DD σ hσ (rho0 DD ρ γ) (Classical.choose (exists_cocycleFun DD ρ σ hσ g δ)),
      hγ, hδ, map_mul g.1 γ δ, map_mul (rho0 DD ρ) γ δ, map_mul σ]
    group

include hσ in
/-- The defining spec of `cocycleOfQ`: `iV(c γ) = g γ · σ(ρ'γ)⁻¹`. -/
theorem cocycleOfQ_spec (g : QLiftsOver DD ρ) (γ : Γ) :
    iV DD (Multiplicative.ofAdd ((cocycleOfQ DD ρ σ hσ g).c γ)) = g.1 γ * (σ (rho0 DD ρ γ))⁻¹ :=
  Classical.choose_spec (exists_cocycleFun DD ρ σ hσ g γ)

include hσ in
/-- **The semidirect bijection** `Z¹_{Γ,ρ}(V) ≃ {Γ →ₜ Q over ρ'}` (the Prop. 8.9 assembly): via a splitting
`σ` of `piQbar`, crossed `V`-cocycles are exactly the continuous homs `Γ → Q = Bg/T` lying over
the lower map `ρ'`.  This is the paper's `B/T ≅ V ⋊ C₀` presentation at the level of `Γ`-points. -/
noncomputable def vcocycleEquivLifts : VCocycle DD ρ ≃ QLiftsOver DD ρ where
  toFun := qOfCocycle DD ρ σ hσ
  invFun := cocycleOfQ DD ρ σ hσ
  left_inv u := VCocycle.ext (funext fun γ => by
    apply iV_ofAdd_inj DD
    rw [cocycleOfQ_spec DD ρ σ hσ, qOfCocycle_apply]
    group)
  right_inv g := by
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro γ
    show iV DD (Multiplicative.ofAdd ((cocycleOfQ DD ρ σ hσ g).c γ)) * σ (rho0 DD ρ γ) = g.1 γ
    rw [cocycleOfQ_spec DD ρ σ hσ]
    group

include hσ in
/-- **Conjugation ↔ coboundary translation** (the semidirect action, the algebraic heart of the
Bug-1 recalibration): conjugating the hom `qOfCocycle c` by `iV(v)` adds the principal coboundary
`vCob v` to its cocycle.  `V` (via `iV`) acts on the fibre `{Γ →ₜ Q over ρ'}` by translation
through `B¹`. -/
theorem qOfCocycle_conj (c : VCocycle DD ρ) (v : DD.Vmod) (γ : Γ) :
    iV DD (Multiplicative.ofAdd v) * (qOfCocycle DD ρ σ hσ c).1 γ
        * (iV DD (Multiplicative.ofAdd v))⁻¹
      = (qOfCocycle DD ρ σ hσ (c + vCob DD ρ v)).1 γ := by
  rw [qOfCocycle_apply, qOfCocycle_apply]
  have hcob : (c + vCob DD ρ v).c γ = c.c γ + (v - rho0 DD ρ γ • v) := by
    show c.c γ + (vCob DD ρ v).c γ = _
    rw [vCob_c]
    show c.c γ + (rho0 DD ρ γ • v - v) = c.c γ + (v - rho0 DD ρ γ • v)
    congr 1
    have hnw : -(rho0 DD ρ γ • v - v) = rho0 DD ρ γ • v - v :=
      neg_eq_of_add_eq_zero_left (Vmod_exp2 DD _)
    rw [← hnw, neg_sub]
  rw [hcob, ← iV_ofAdd_inv DD v]
  rw [show iV DD (Multiplicative.ofAdd v) * (iV DD (Multiplicative.ofAdd (c.c γ)) * σ (rho0 DD ρ γ))
        * iV DD (Multiplicative.ofAdd (-v))
      = iV DD (Multiplicative.ofAdd v) * iV DD (Multiplicative.ofAdd (c.c γ))
        * (σ (rho0 DD ρ γ) * iV DD (Multiplicative.ofAdd (-v))) from by group]
  rw [sigma_iV_comm DD σ hσ (rho0 DD ρ γ) (-v), ← mul_assoc, ← iV_ofAdd_add, ← iV_ofAdd_add,
    smul_neg,
    show v + c.c γ + -(rho0 DD ρ γ • v) = c.c γ + (v - rho0 DD ρ γ • v) from by abel]

include hσ in
/-- **The `B¹`-translation fact** (the Prop. 8.9 assembly, the algebraic core of Bug 1): conjugating an
`M`-lift `f` by `m ∈ M` translates the `V`-cocycle of its `T`-reduction by the principal
coboundary `vCob (descend m)`.  Together with `mConj_central` this shows `V` (via `descend`) acts
on the central `red_T`-image by `B¹`-translation — free when `V^C = 0` (`vCob_c_eq_zero_iff`), so
the image carries the missing `|B¹| = #V` factor (c1s). -/
theorem cocycleOf_mConj (m : Bg) (hm : m ∈ D.M) (f : MLifts D ρ) :
    cocycleOfQ DD ρ σ hσ (redTLift DD (mConj m hm f))
      = cocycleOfQ DD ρ σ hσ (redTLift DD f)
        + vCob DD ρ (Multiplicative.toAdd (DD.descend ⟨m, hm⟩)) := by
  set v := Multiplicative.toAdd (DD.descend ⟨m, hm⟩) with hv
  have hiv : iV DD (Multiplicative.ofAdd v) = QuotientGroup.mk m := by
    show iV DD (DD.descend ⟨m, hm⟩) = QuotientGroup.mk m
    rw [iV_spec]; rfl
  suffices h : redTLift DD (mConj m hm f)
      = qOfCocycle DD ρ σ hσ (cocycleOfQ DD ρ σ hσ (redTLift DD f) + vCob DD ρ v) by
    rw [h]; exact (vcocycleEquivLifts DD ρ σ hσ).left_inv _
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro γ
  rw [← qOfCocycle_conj DD ρ σ hσ (cocycleOfQ DD ρ σ hσ (redTLift DD f)) v γ,
    show qOfCocycle DD ρ σ hσ (cocycleOfQ DD ρ σ hσ (redTLift DD f)) = redTLift DD f
      from (vcocycleEquivLifts DD ρ σ hσ).right_inv (redTLift DD f)]
  show QuotientGroup.mk ((mConj m hm f).1 γ)
    = iV DD (Multiplicative.ofAdd v) * QuotientGroup.mk (f.1 γ) * (iV DD (Multiplicative.ofAdd v))⁻¹
  rw [hiv, mConj_apply, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

end Splitting

end AffineTLift

end SectionEight

end GQ2
