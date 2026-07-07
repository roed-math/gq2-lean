import GQ2.MStageCount
import GQ2.RStageGammaA

/-!
# P-17i: the `Γ_A`-side `M`-stage multiplicity count (`hmultA`)

The `M`-stage lane of `thm_4_2` (`GQ2/SectionNine.lean`, the `R = ⊥` branch) applies
`mStage_partition` at both sources with multiplicity `mult = |M_B|²`; the `G_ℚ₂` count is
`RecursionFrame.liftsOver_card_local` (`GQ2/MStageCount.lean`).  This file supplies the **`Γ_A`**
count `#LiftsOver_{Γ_A}(ρ) = |M_B|²` (`hmultA`).

The proof mirrors `liftsOver_card_local` (the `#H² = 1` torsor bridge at the descended module
`M_B`), with the two `Γ_A`-specific substitutions of the P-16d6e5 `RStageGammaA` playbook:

* **the `Z¹` count** — there is no local Euler characteristic for `Γ_A`; the candidate duality
  supplies it instead.  `z1Equiv` (`WordCohBridge`, P-16c1) identifies `Z¹_cont(Γ_A, M_B)` with the
  Fox–Heisenberg word cocycles `Z¹_word(markC ρ)`, and `prop_5_15` clause 2 (`IsSelfDual`) counts
  those as `|M_B|² · #fixedPts_C(M_B^∨)`.  This is exactly the `hZcount_gammaA` route at module
  `M_B` instead of `R`.  `#fixedPts = 1` is the source-independent `lemma_7_1_dual` bridge, proved
  inline (identical to `liftsOver_card_local`'s `hfix`).
* **nonemptiness** — `Γ_A` has no degree-2 word↔continuous bridge, so the `#H² = 1 ⟹ coboundary`
  route of the local proof is unavailable.  Instead `liftsOver_nonempty_gammaA` ports the
  `hsep_hom_gammaA` + L5-descent argument (`RStageGammaA`) from `(π_B, R)` to `(π_BC, M_B)`: a
  set-lift marking's relator values land in `M_B`, the trace-span duality forces their correction
  (since `(M_B^∨)^C = 0`), and the corrected marking descends.

Axioms (target at close): `⊆ std-3 + B6 + B7` (as `liftsOver_card_local` / `hZcount_gammaA`).
-/

namespace GQ2

namespace SectionEight

open ContCoh SectionSeven WordCohBridge GQ2.FoxH RStageGammaA

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}

/-- **Nonemptiness of the `Γ_A` `B`-lift fibre** (P-17i, the M-stage residue): every lower
boundary lift `ρ : Γ_A ↠ C` lifts to a continuous homomorphism `Γ_A → B` through `π_{BC}`.

Ported from `RStageGammaA.hsep_hom_gammaA` (which lifts through `π_B : Y ↠ B`) to `π_{BC} : B ↠ C`
(kernel `M_B`, 2-torsion by `MB_elem`): a set-lift marking of `ρ` has relator values in `M_B`, and
since `(M_B^∨)^C = 0` (`lemma_7_1_dual`, the `hfix` group theory) the trace-span duality forces
those values to be correctable, whence the corrected marking descends (L5). -/
theorem RecursionFrame.liftsOver_nonempty_gammaA
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaA ↥boundarySubgroup)
    (F : BoundaryFrame H E) (ρ : BoundaryLifts b F RF.TC) :
    Nonempty (RF.LiftsOver b F ρ) := by
  sorry

/-- **`hmultA` for `Γ_A`**, assuming the fibre is nonempty: `#LiftsOver(ρ) = |M_B|²`.  The
`Z¹`-torsor bridge (`liftsOver_card_local`'s Step 2) is source-generic once a base lift exists;
the `Z¹` count is the candidate-duality route (`z1Equiv` + `prop_5_15` clause 2), and `hfix = 1`
is the `lemma_7_1_dual` bridge, both mirroring the local proof. -/
theorem RecursionFrame.liftsOver_card_gammaA_of_nonempty
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaA ↥boundarySubgroup)
    (F : BoundaryFrame H E) (ρ : BoundaryLifts b F RF.TC)
    (hne : Nonempty (RF.LiftsOver b F ρ)) :
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2 := by
  classical
  -- `M_B` is normal (the kernel of `π_{BC}`) and elementary abelian
  haveI hMBn : RF.MB.Normal := RF.ker_piBC ▸ RF.piBC.normal_ker
  have hcomm : ∀ x ∈ RF.MB, ∀ y ∈ RF.MB, x * y = y * x := by
    intro x hx y hy
    have hxy := RF.MB_elem _ (mul_mem hx hy)
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
      _ = y * x := by
          rw [inv_eq_of_mul_eq_one_right (RF.MB_elem _ hy),
            inv_eq_of_mul_eq_one_right (RF.MB_elem _ hx)]
  have hconj_eq : ∀ {u v : RF.YB}, RF.piBC u = RF.piBC v → ∀ m : ↥RF.MB,
      u * m.1 * u⁻¹ = v * m.1 * v⁻¹ := by
    intro u v huv m
    have hm : u⁻¹ * v ∈ RF.MB := by
      rw [← RF.ker_piBC]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, huv, inv_mul_cancel])
    have hcm := hcomm _ hm _ m.2
    calc u * m.1 * u⁻¹
        = u * (m.1 * (u⁻¹ * v) * (u⁻¹ * v)⁻¹) * u⁻¹ := by group
      _ = u * ((u⁻¹ * v) * m.1 * (u⁻¹ * v)⁻¹) * u⁻¹ := by rw [← hcm]
      _ = v * m.1 * v⁻¹ := by group
  -- the set-section of `π_{BC}` and the lower map (over `GA`, for `z1Equiv`)
  set sec : RF.YC → RF.YB := Function.surjInv RF.piBC_surj with hsecdef
  have hsec : ∀ c, RF.piBC (sec c) = c := fun c => Function.surjInv_eq RF.piBC_surj c
  set θ : ContinuousMonoidHom GA RF.YC :=
    ⟨ρ.1.1.toMonoidHom, ρ.1.1.continuous_toFun⟩ with hθdef
  have hθs : Function.Surjective ⇑θ := ρ.1.2
  -- `M_B` as an additive `𝔽₂`-space with the `ρ`-conjugation action
  letI : CommGroup ↥RF.MB :=
    { (inferInstance : Group ↥RF.MB) with
      mul_comm := fun a b => Subtype.ext (hcomm _ a.2 _ b.2) }
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actC : DistribMulAction RF.YC (Additive ↥RF.MB) :=
    { smul := fun c m => Additive.ofMul
        ⟨sec c * (Additive.toMul m).1 * (sec c)⁻¹,
          hMBn.conj_mem _ (Additive.toMul m).2 _⟩
      one_smul := fun m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec 1 * (Additive.toMul m).1 * (sec 1)⁻¹ = (Additive.toMul m).1
        have h1 : sec 1 ∈ RF.MB := by
          rw [← RF.ker_piBC]
          exact MonoidHom.mem_ker.mpr (hsec 1)
        rw [hcomm _ h1 _ (Additive.toMul m).2]; group
      mul_smul := fun c c' m => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec (c * c') * (Additive.toMul m).1 * (sec (c * c'))⁻¹
          = sec c * (sec c' * (Additive.toMul m).1 * (sec c')⁻¹) * (sec c)⁻¹
        rw [show sec c * (sec c' * (Additive.toMul m).1 * (sec c')⁻¹) * (sec c)⁻¹
            = (sec c * sec c') * (Additive.toMul m).1 * (sec c * sec c')⁻¹ from by group]
        exact hconj_eq (by rw [hsec, map_mul, hsec, hsec]) (Additive.toMul m)
      smul_zero := fun c => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec c * (1 : RF.YB) * (sec c)⁻¹ = 1
        group
      smul_add := fun c m m' => by
        apply Additive.toMul.injective; apply Subtype.ext
        show sec c * ((Additive.toMul m).1 * (Additive.toMul m').1) * (sec c)⁻¹
          = (sec c * (Additive.toMul m).1 * (sec c)⁻¹)
              * (sec c * (Additive.toMul m').1 * (sec c)⁻¹)
        group }
  letI actG : DistribMulAction GA (Additive ↥RF.MB) :=
    DistribMulAction.compHom (Additive ↥RF.MB) θ.toMonoidHom
  have hcomp : ∀ (γ : GA) (a : Additive ↥RF.MB), γ • a = θ γ • a := fun _ _ => rfl
  have hA₂ : ∀ a : Additive ↥RF.MB, a + a = 0 := fun a => by
    apply Additive.toMul.injective
    show (Additive.toMul a) * (Additive.toMul a) = 1
    exact Subtype.ext (RF.MB_elem _ (Additive.toMul a).2)
  haveI : ContinuousSMul GA (Additive ↥RF.MB) := by
    refine ⟨?_⟩
    have hfac : (fun p : GA × Additive ↥RF.MB => p.1 • p.2)
        = (fun q : RF.YC × Additive ↥RF.MB => q.1 • q.2)
          ∘ (fun p : GA × Additive ↥RF.MB => (θ p.1, p.2)) := by funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((θ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  -- Step 3': the `Z¹` count via the candidate duality (`z1Equiv` + `prop_5_15` clause 2)
  have adm := markC_admissible θ hθs
  have key : Nat.card (Z1 GA (Additive ↥RF.MB))
      = Nat.card (Additive ↥RF.MB) ^ 2
        * Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) := by
    rw [Nat.card_congr (z1Equiv θ hcomp hθs hA₂).toEquiv,
      (GQ2.FoxH.prop_5_15 (markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.1]
  -- Step 4: `#fixedPts = 1` ⟵ `lemma_7_1_dual` (the `(M^∨)^C = 0` group theory, source-free)
  have hfix : Nat.card (fixedPts RF.YC (ElemDual (Additive ↥RF.MB))) = 1 := by
    have hzero : ∀ lam : ElemDual (Additive ↥RF.MB),
        (∀ g : RF.YC, g • lam = lam) → lam = 0 := by
      intro lam hlam
      by_contra hlamne
      have hinv : ∀ (c : RF.YC) (a : Additive ↥RF.MB), lam (c • a) = lam a := by
        intro c a
        have h2 : (c⁻¹ • lam) a = lam a := by rw [hlam c⁻¹]
        rwa [ElemDual.smul_apply, inv_inv] at h2
      have hmem : ∀ k : ↥Blk.K, RF.piB k.1 ∈ RF.MB := by
        intro k
        rw [RF.MB_eq]; exact Subgroup.mem_map.mpr ⟨k.1, k.2, rfl⟩
      let s : ↥Blk.K →* ↥RF.MB :=
        (RF.piB.comp Blk.K.subtype).codRestrict RF.MB (fun k => hmem k)
      have hs : ∀ k : ↥Blk.K, (s k).1 = RF.piB k.1 := fun _ => rfl
      have hs_surj : Function.Surjective s := by
        intro m
        obtain ⟨k, hk, hkeq⟩ := (RF.MB_eq ▸ m.2 : m.1 ∈ Blk.K.map RF.piB)
        exact ⟨⟨k, hk⟩, Subtype.ext hkeq⟩
      let φ : ↥Blk.K →* Multiplicative (ZMod 2) :=
        { toFun := fun k => Multiplicative.ofAdd (lam (Additive.ofMul (s k)))
          map_one' := by simp
          map_mul' := fun a b => by simp [map_mul] }
      have hφ_apply : ∀ k, φ k = Multiplicative.ofAdd (lam (Additive.ofMul (s k))) := fun _ => rfl
      have hφne : φ ≠ 1 := by
        intro hφ1
        apply hlamne
        ext a
        show lam a = 0
        obtain ⟨k, hk⟩ := hs_surj (Additive.toMul a)
        have h0 : lam (Additive.ofMul (s k)) = 0 := by
          have hk1 : φ k = 1 := by rw [hφ1]; rfl
          have := congrArg Multiplicative.toAdd hk1
          simpa [hφ_apply] using this
        rw [hk] at h0
        exact h0
      have hφsurj : Function.Surjective φ := by
        intro y
        rcases eq_or_ne y 1 with rfl | hy
        · exact ⟨1, map_one φ⟩
        · obtain ⟨k, hk⟩ := not_forall.mp (fun hh => hφne (MonoidHom.ext hh))
          refine ⟨k, ?_⟩
          have hpin : ∀ z : Multiplicative (ZMod 2), z ≠ 1 → z = Multiplicative.ofAdd 1 := by
            decide
          rw [hpin _ hk, hpin _ hy]
      set X : Subgroup Y := φ.ker.map Blk.K.subtype with hXdef
      have hXK : X ≤ Blk.K := by rw [hXdef]; exact Subgroup.map_subtype_le _
      have hRX : Blk.R ≤ X := by
        intro r hr
        have hrK : r ∈ Blk.K := frattiniLike_le Blk.K hr
        refine Subgroup.mem_map.mpr ⟨⟨r, hrK⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker, hφ_apply]
        have hs1 : s ⟨r, hrK⟩ = 1 := Subtype.ext (by
          rw [hs]
          show RF.piB r = 1
          exact (RF.ker_piB.symm ▸ hr : r ∈ RF.piB.ker))
        rw [hs1]; simp
      have hXnormal : X.Normal := by
        rw [hXdef]
        refine ⟨fun x hx y => ?_⟩
        obtain ⟨k, hkker, hkeq⟩ := Subgroup.mem_map.mp hx
        have hxK : x ∈ Blk.K := hkeq ▸ k.2
        have hyk : y * x * y⁻¹ ∈ Blk.K := Blk.hK.conj_mem x hxK y
        refine Subgroup.mem_map.mpr ⟨⟨y * x * y⁻¹, hyk⟩, ?_, rfl⟩
        rw [MonoidHom.mem_ker] at hkker ⊢
        rw [hφ_apply] at hkker ⊢
        have hconj : Additive.ofMul (s ⟨y * x * y⁻¹, hyk⟩)
            = (RF.piBC (RF.piB y)) • Additive.ofMul (s ⟨x, hxK⟩) := by
          have hact : (RF.piBC (RF.piB y)) • Additive.ofMul (s ⟨x, hxK⟩)
              = Additive.ofMul (⟨sec (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1
                  * (sec (RF.piBC (RF.piB y)))⁻¹,
                  hMBn.conj_mem _ (s ⟨x, hxK⟩).2 _⟩ : ↥RF.MB) := rfl
          rw [hact]
          congr 1
          apply Subtype.ext
          rw [hs]
          show RF.piB (y * x * y⁻¹)
            = sec (RF.piBC (RF.piB y)) * (s ⟨x, hxK⟩).1 * (sec (RF.piBC (RF.piB y)))⁻¹
          rw [hs, map_mul, map_mul, map_inv]
          exact (hconj_eq (hsec (RF.piBC (RF.piB y))) ⟨RF.piB x, hmem ⟨x, hxK⟩⟩).symm
        rw [hconj, hinv]
        have hkx : s ⟨x, hxK⟩ = s k := congrArg s (Subtype.ext hkeq.symm)
        rw [hkx]; exact hkker
      have hidx : (X.subgroupOf Blk.K).index = 2 := by
        have hcm : X.subgroupOf Blk.K = φ.ker := by
          rw [hXdef, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective Blk.K.subtype_injective]
        show Nat.card (↥Blk.K ⧸ (X.subgroupOf Blk.K)) = 2
        rw [hcm, Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv]
        simp
      exact absurd ⟨X, hXnormal, hRX, hXK, hidx⟩ (lemma_7_1_dual Blk)
    rw [Nat.card_eq_one_iff_unique]
    exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
      ⟨⟨0, fun c => smul_zero c⟩⟩⟩
  -- Step 2: the `Z¹`-torsor bridge (source-generic once a base lift `f₀` exists)
  have htorsor : Nat.card (RF.LiftsOver b F ρ)
      = Nat.card (Z1 GA (Additive ↥RF.MB)) := by
    obtain ⟨f₀⟩ := hne
    have hsmul : ∀ (γ : GA) (a : Additive ↥RF.MB),
        γ • a = Additive.ofMul (⟨f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹,
              hMBn.conj_mem _ (Additive.toMul a).2 _⟩ : ↥RF.MB) := by
      intro γ a
      rw [hcomp]
      apply Additive.toMul.injective; apply Subtype.ext
      show sec (θ γ) * (Additive.toMul a).1 * (sec (θ γ))⁻¹
        = f₀.1 γ * (Additive.toMul a).1 * (f₀.1 γ)⁻¹
      exact hconj_eq (by rw [hsec]; exact (f₀.2 γ).symm) (Additive.toMul a)
    have hmemf : ∀ (f : RF.LiftsOver b F ρ) (γ : GA),
        f.1 γ * (f₀.1 γ)⁻¹ ∈ RF.MB := by
      intro f γ
      rw [← RF.ker_piBC]
      exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, f.2 γ, f₀.2 γ, mul_inv_cancel])
    refine Nat.card_congr
      { toFun := fun f => ⟨fun γ => Additive.ofMul ⟨f.1 γ * (f₀.1 γ)⁻¹, hmemf f γ⟩, ?_⟩
        invFun := fun c => ⟨(⟨MonoidHom.mk'
            (fun γ : GA => (Additive.toMul (c.1 γ)).1 * f₀.1 γ) ?_, ?_⟩ :
              ContinuousMonoidHom GA RF.YB), ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · -- forward lands in `Z¹`
      rw [mem_Z1_iff]
      refine ⟨((continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1 * p.2⁻¹)).comp
        (f.1.continuous_toFun.prodMk f₀.1.continuous_toFun)).subtype_mk (hmemf f), ?_⟩
      intro g s
      rw [hsmul g (Additive.ofMul ⟨f.1 s * (f₀.1 s)⁻¹, hmemf f s⟩)]
      apply Additive.toMul.injective; apply Subtype.ext
      show f.1 (g * s) * (f₀.1 (g * s))⁻¹
        = f.1 g * (f₀.1 g)⁻¹ * (f₀.1 g * (f.1 s * (f₀.1 s)⁻¹) * (f₀.1 g)⁻¹)
      rw [show f.1 (g * s) = f.1 g * f.1 s from map_mul f.1 g s,
        show f₀.1 (g * s) = f₀.1 g * f₀.1 s from map_mul f₀.1 g s]; group
    · -- inverse is a hom
      intro g h
      show (Additive.toMul (c.1 (g * h))).1 * f₀.1 (g * h)
        = (Additive.toMul (c.1 g)).1 * f₀.1 g * ((Additive.toMul (c.1 h)).1 * f₀.1 h)
      rw [(mem_Z1_iff.mp c.2).2 g h,
        show f₀.1 (g * h) = f₀.1 g * f₀.1 h from map_mul f₀.1 g h, hsmul g (c.1 h)]
      show (Additive.toMul (c.1 g)).1 * (f₀.1 g * (Additive.toMul (c.1 h)).1 * (f₀.1 g)⁻¹)
          * (f₀.1 g * f₀.1 h) = _
      group
    · -- inverse is continuous
      exact (continuous_of_discreteTopology
          (f := fun p : Additive ↥RF.MB × RF.YB => (Additive.toMul p.1).1 * p.2)).comp
        ((mem_Z1_iff.mp c.2).1.prodMk f₀.1.continuous_toFun)
    · -- inverse lands over `ρ`
      intro γ
      show RF.piBC ((Additive.toMul (c.1 γ)).1 * f₀.1 γ) = ρ.1.1 γ
      have hcker : RF.piBC ((Additive.toMul (c.1 γ)).1) = 1 := by
        have hmem : ((Additive.toMul (c.1 γ)).1 : RF.YB) ∈ RF.piBC.ker := by
          rw [RF.ker_piBC]
          exact (Additive.toMul (c.1 γ)).2
        exact MonoidHom.mem_ker.mp hmem
      rw [map_mul, hcker, one_mul, f₀.2 γ]
    · -- left inverse
      intro f
      apply Subtype.ext; apply ContinuousMonoidHom.ext; intro γ
      show f.1 γ * (f₀.1 γ)⁻¹ * f₀.1 γ = f.1 γ
      group
    · -- right inverse
      intro c
      apply Subtype.ext; funext γ
      show Additive.ofMul (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩
          : ↥RF.MB) = c.1 γ
      rw [show (⟨(Additive.toMul (c.1 γ)).1 * f₀.1 γ * (f₀.1 γ)⁻¹, _⟩ : ↥RF.MB)
          = Additive.toMul (c.1 γ) from Subtype.ext (by group)]
      rfl
  rw [htorsor, key, hfix, mul_one]
  rfl

/-- **`hmultA` for `Γ_A`**: `#LiftsOver(ρ) = |M_B|²` over every lower boundary lift. -/
theorem RecursionFrame.liftsOver_card_gammaA
    (RF : RecursionFrame T Blk) (b : ContinuousMonoidHom GammaA ↥boundarySubgroup)
    (F : BoundaryFrame H E) (ρ : BoundaryLifts b F RF.TC) :
    Nat.card (RF.LiftsOver b F ρ) = (Nat.card ↥RF.MB) ^ 2 :=
  RF.liftsOver_card_gammaA_of_nonempty b F ρ (RF.liftsOver_nonempty_gammaA b F ρ)

end SectionEight

end GQ2
