/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionSeven.ModuleCore

/-!
# Proposition 7.4: the `H_V` averaging, step 2, and the simple-head determinant

Split off from `GQ2.SectionSeven`, building on `GQ2.SectionSeven.ModuleCore`.  This file assembles
the genuinely tame tier and concludes Proposition 7.4:

* the **`H_V` averaging** (Prop 7.4 step 2 back half) and the **tame extension**;
* **Prop 7.4, step 2** (`q_λ|_{T₀} = 0`);
* **Proposition 7.4** itself (`prop_7_4`).

See `GQ2.SectionSeven` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionSeven

open QuadraticFp2

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

variable {L : Subgroup Y}

/-- **H_V averaging (Prop. 7.4 step 2)** (std-3): given a hom `σ₀ : K → 𝔽₂` whose
restriction to `K ∩ S` is `Y`-invariant and which is `Y_V`-invariant (shear-vanishing), the
`H_V`-average of `σ₀` over an odd normal `Ctil ◁ Y` moving `V = P/S` is a `Y`-invariant hom
extending `σ₀|_{K∩S}`.  The module/averaging tier: `Y_V = ker(blockPerm)` acts trivially on `V`
(`hYVtriv`), `K/(K∩S)` is abelian (`hcomm`), and `(V∨)^Ctil = 0` is `fixed_zero_of_moves`
(A, simplicity) composed with `dual_vanish_concrete` (F1, odd averaging) — feeding
`quotient_average`.  The tame construction of `Ctil` is a **case split** (`by_cases` on whether the
tame inertia `⟨cH τ⟩` moves `V`): ramified `Ctil := π⁻¹⟨cH τ⟩` (odd via `odd_preimage_quot`), or
unramified `Ctil := ⊤` with `Y/Y_V` odd (`unram_odd`: `H_V` cyclic `cyc_YV` + `O₂(H_V) = 1`).
[the Prop. 7.4 proof CLOSED.] -/
private theorem hv_average_helper {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L)
    (σ₀ : Y → ZMod 2)
    (hσ₀hom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → σ₀ (k * l) = σ₀ k + σ₀ l)
    (hσ₀KSinv : ∀ k, k ∈ B.K ⊓ B.S → ∀ y : Y, σ₀ (y * k * y⁻¹) = σ₀ k)
    (hσ₀YV : ∀ (z : Y), (∀ k, k ∈ B.K → z * k * z⁻¹ * k⁻¹ ∈ B.K ⊓ B.S) →
      ∀ k, k ∈ B.K → σ₀ (z * k * z⁻¹) = σ₀ k) :
    ∃ ψ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l) ∧
      (∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k) ∧
      (∀ k, k ∈ B.K ⊓ B.S → ψ k = σ₀ k) := by
  classical
  -- `Y_V := ker(blockPerm)` is the kernel of the `Y`-action on `V = P/S`, normal.  With the module
  -- core (`fixed_zero_of_moves` (A) + `dual_vanish_concrete` (F1)) the whole obligation reduces to
  -- the tame construction: an odd normal `Ctil` that **moves** `V`.
  have hYVn : ((blockPerm B.S B.P B.hS B.hP).ker).Normal :=
    (blockPerm B.S B.P B.hS B.hP).normal_ker
  -- `Y_V` acts trivially on `V = P/S`: `z` fixing `[k⁻¹]` (`k ∈ K ≤ P`) gives `[z,k] ∈ S`.
  have hYVtriv : ∀ z, z ∈ (blockPerm B.S B.P B.hS B.hP).ker → ∀ k, k ∈ B.K →
      z * k * z⁻¹ * k⁻¹ ∈ B.S := by
    intro z hz k hk
    have hkiP : k⁻¹ ∈ B.P := B.hKP (B.K.inv_mem hk)
    have hfix : (QuotientGroup.mk (conjHom B.P B.hP z ⟨k⁻¹, hkiP⟩)
          : ↥B.P ⧸ B.S.subgroupOf B.P) = QuotientGroup.mk ⟨k⁻¹, hkiP⟩ := by
      rw [← blockPerm_apply_mk B.S B.P B.hS B.hP z ⟨k⁻¹, hkiP⟩, MonoidHom.mem_ker.mp hz]
      rfl
    have h1 : (conjHom B.P B.hP z ⟨k⁻¹, hkiP⟩)⁻¹ * (⟨k⁻¹, hkiP⟩ : ↥B.P)
        ∈ B.S.subgroupOf B.P := QuotientGroup.eq.mp hfix
    have h2 := Subgroup.mem_subgroupOf.mp h1
    have hcoe : (((conjHom B.P B.hP z ⟨k⁻¹, hkiP⟩)⁻¹ * (⟨k⁻¹, hkiP⟩ : ↥B.P) : ↥B.P) : Y)
        = z * k * z⁻¹ * k⁻¹ := by
      show (z * k⁻¹ * z⁻¹)⁻¹ * k⁻¹ = z * k * z⁻¹ * k⁻¹
      group
    rwa [hcoe] at h2
  have hσ₀YV' : ∀ k, k ∈ B.K → ∀ z, z ∈ (blockPerm B.S B.P B.hS B.hP).ker →
      σ₀ (z * k * z⁻¹) = σ₀ k := by
    intro k hk z hz
    exact hσ₀YV z (fun k' hk' => Subgroup.mem_inf.mpr
      ⟨B.K.mul_mem (B.hK.conj_mem k' hk' z) (B.K.inv_mem hk'), hYVtriv z hz k' hk'⟩) k hk
  -- `K/(K∩S)` is abelian: commutators of `K` lie in `R ≤ K ∩ S ≤ S`.
  have hcomm : ∀ a, a ∈ B.K → ∀ b, b ∈ B.K → a * b * a⁻¹ * b⁻¹ ∈ B.S := by
    intro a ha b hb
    have hR : a * b * a⁻¹ * b⁻¹ ∈ B.frattiniK :=
      Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, rfl⟩)
    exact (Subgroup.mem_inf.mp (lemma_7_1_head B hR)).2
  -- **Remaining tame construction**: an odd normal `Ctil` that moves `V = P/S`.
  obtain ⟨Ctil, hCtiln, hodd, hmoves⟩ :
      ∃ Ctil : Subgroup Y, Ctil.Normal ∧
        Odd (Nat.card (↥Ctil ⧸ (((blockPerm B.S B.P B.hS B.hP).ker).subgroupOf Ctil))) ∧
        (∃ p, p ∈ B.P ∧ ∃ c, c ∈ Ctil ∧ c⁻¹ * p * c * p⁻¹ ∉ B.S) := by
    -- `L ≤ Y_V` (P1: `L` acts trivially on `V = P/S`), so `ker π = L ≤ Y_V`.
    have hLYV : L ≤ (blockPerm B.S B.P B.hS B.hP).ker :=
      L_le_blockPerm_ker B.S B.P L B.hS B.hP B.hL B.hSP B.hPL B.h2L B.chief
    have hkerYV : π.ker ≤ (blockPerm B.S B.P B.hS B.hP).ker := hkerπ.le.trans hLYV
    -- tame structure of `H = Y/L` via `cH`: `I_H = ⟨cH τ⟩` normal + odd.
    have hgen : Subgroup.closure {cH tameSigma, cH tameTau} = ⊤ :=
      SectionThree.gen_ttame_quotient cH.toMonoidHom cH.continuous_toFun hcH
    have hrel : (cH tameSigma)⁻¹ * cH tameTau * cH tameSigma = (cH tameTau) ^ 2 := by
      have h := congrArg cH tame_relation
      simpa only [conjP, map_mul, map_inv, map_pow] using h
    have hIH_normal : (Subgroup.zpowers (cH tameTau)).Normal :=
      Tame.zpowers_normal_of_tame hgen hrel
    have hIH_odd : Odd (orderOf (cH tameTau)) := Tame.tame_odd_order (orderOf_pos _).ne' hrel
    by_cases hram : ∃ p, p ∈ B.P ∧ ∃ c, c ∈ (Subgroup.zpowers (cH tameTau)).comap π ∧
        c⁻¹ * p * c * p⁻¹ ∉ B.S
    · -- **ramified**: `I_H` moves `V`, so `Ctil := π⁻¹⟨cH τ⟩` (odd over `Y_V`, moves `V`).
      exact ⟨(Subgroup.zpowers (cH tameTau)).comap π, hIH_normal.comap π,
        odd_preimage_quot π hπ (blockPerm B.S B.P B.hS B.hP).ker hkerYV (cH tameTau) hIH_odd, hram⟩
    · -- **unramified**: `I_H` acts trivially, so `Ctil := ⊤` moves `V` (`nontrivial_action`),
      -- and `Y/Y_V = H_V` is odd (`O₂(H_V) = 1`, `H_V` cyclic).
      refine ⟨⊤, Subgroup.normal_top, ?_, ?_⟩
      · haveI hYVnorm : ((blockPerm B.S B.P B.hS B.hP).ker).Normal :=
          (blockPerm B.S B.P B.hS B.hP).normal_ker
        have hP2 : IsPGroup 2 B.P := fun g => by
          obtain ⟨n, hn⟩ := B.h2L ⟨g.1, B.hPL g.2⟩
          exact ⟨n, by ext; simpa using congrArg Subtype.val hn⟩
        push Not at hram
        -- `I_H`'s preimage acts trivially, so `π⁻¹⟨cH τ⟩ ≤ Y_V`
        have hIHYV : (Subgroup.zpowers (cH tameTau)).comap π
            ≤ (blockPerm B.S B.P B.hS B.hP).ker := by
          intro c hc
          rw [MonoidHom.mem_ker]
          refine Equiv.Perm.ext fun q => ?_
          refine QuotientGroup.induction_on q fun p => ?_
          show blockPerm B.S B.P B.hS B.hP c (QuotientGroup.mk p) = QuotientGroup.mk p
          rw [blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hcoe : (((conjHom B.P B.hP c p)⁻¹ * p : ↥B.P) : Y)
              = c * (p : Y)⁻¹ * c⁻¹ * (p : Y) := by
            show (c * (p : Y) * c⁻¹)⁻¹ * (p : Y) = c * (p : Y)⁻¹ * c⁻¹ * (p : Y); group
          rw [hcoe]
          have h := hram (p : Y)⁻¹ (B.P.inv_mem p.2) c⁻¹ (inv_mem hc)
          have hgoal : c * (p : Y)⁻¹ * c⁻¹ * (p : Y)
              = (c⁻¹)⁻¹ * (p : Y)⁻¹ * c⁻¹ * ((p : Y)⁻¹)⁻¹ := by group
          rw [hgoal]; exact h
        -- so `cH τ ∈ map π Y_V`, hence `Y/Y_V` is cyclic and odd (`unram_odd`)
        obtain ⟨yτ, hyτ⟩ := hπ (cH tameTau)
        have hyτIH : yτ ∈ (Subgroup.zpowers (cH tameTau)).comap π := by
          rw [Subgroup.mem_comap, hyτ]; exact Subgroup.mem_zpowers _
        have htYV : cH tameTau ∈ ((blockPerm B.S B.P B.hS B.hP).ker).map π :=
          ⟨yτ, hIHYV hyτIH, hyτ⟩
        have hcyc : IsCyclic (Y ⧸ (blockPerm B.S B.P B.hS B.hP).ker) :=
          cyc_YV π hπ _ hkerYV (cH tameSigma) (cH tameTau) hgen htYV
        rw [top_quot_card]
        exact unram_odd B.S B.P B.hS B.hP B.hSP hP2 B.chief hcyc
      · obtain ⟨y, p, hpP, hmove⟩ := B.nontrivial_action
        exact ⟨p, hpP, y⁻¹, Subgroup.mem_top _, by rw [inv_inv]; exact hmove⟩
  -- module core: (A) simplicity `V^Ctil = 0`, then (F1) averaging `(V∨)^Ctil = 0`
  have hfix0 : ∀ k, k ∈ B.K → (∀ c, c ∈ Ctil → c⁻¹ * k * c * k⁻¹ ∈ B.S) → k ∈ B.S :=
    fixed_zero_of_moves B.S B.P B.K Ctil B.hS B.hP hCtiln B.hSP.le B.hKP B.chief hmoves
  have hVC : ∀ φ : Y → ZMod 2, (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → φ (k * l) = φ k + φ l) →
      (∀ k, k ∈ B.K ⊓ B.S → φ k = 0) →
      (∀ (c : Y), c ∈ Ctil → ∀ k, k ∈ B.K → φ (c⁻¹ * k * c) = φ k) →
      ∀ k, k ∈ B.K → φ k = 0 := by
    intro φ hφhom hφ0 hφCinv
    exact dual_vanish_concrete B.S B.K Ctil ((blockPerm B.S B.P B.hS B.hP).ker)
      B.hS B.hK hCtiln hYVn hcomm hYVtriv hodd hfix0 φ hφhom
      (fun k hk hkS => hφ0 k (Subgroup.mem_inf.mpr ⟨hk, hkS⟩)) hφCinv
  exact quotient_average B ((blockPerm B.S B.P B.hS B.hP).ker) Ctil hYVn hCtiln hodd σ₀
    hσ₀hom hσ₀KSinv hσ₀YV' hVC

/-- **Tame extension (Prop 7.4 step 2, front half)**: the square functional `k ↦ λ(k²)` on
`K ∩ S` extends to a `Y`-invariant hom `ψ : K → 𝔽₂`.  Now assembled from the reduction (`σ := λ∘sq`
is a `Y`-invariant hom on `K∩S` killing `R`, via `lemma_7_2` + `lam_comm_vanish`), the hom
extension `sigma0_extends` (`σ₀ : K → 𝔽₂`), the automatic `Y_V`-invariance of `σ₀` (shear-vanishing,
from `q`-invariance), and the std-3 `H_V`-averaging lemma `hv_average_helper`. -/
private theorem key_extension {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L) (hRN : B.frattiniK.Normal)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩) :
    ∃ ψ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l) ∧
      (∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k) ∧
      (∀ k, k ∈ B.K ⊓ B.S → ∀ (hkk : k * k ∈ B.frattiniK), ψ k = lam ⟨k * k, hkk⟩) := by
  classical
  haveI := B.hK
  haveI := B.hS
  obtain ⟨hcentral, hr2, _hK4⟩ := lemma_7_2 π hπ hkerπ cH hcH B
  have hcomm_kill := lam_comm_vanish B hRN lam hlam_hom hlam_conj
  have lam_one : lam 1 = 0 := by simpa using hlam_hom 1 1
  have hsq : ∀ k, k ∈ B.K → k * k ∈ B.frattiniK := fun k hk =>
    Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)
  set σ : Y → ZMod 2 := fun y => if h : y * y ∈ B.frattiniK then lam ⟨y * y, h⟩ else 0 with hσdef
  -- reduction: `σ` is a hom on `K ∩ S`
  have hσhom : ∀ k, k ∈ B.K ⊓ B.S → ∀ l, l ∈ B.K ⊓ B.S → σ (k * l) = σ k + σ l := by
    intro k hk l hl
    have hkK := (Subgroup.mem_inf.mp hk).1
    have hlK := (Subgroup.mem_inf.mp hl).1
    have hklK : k * l ∈ B.K := mul_mem hkK hlK
    have hcomm : l * k * l⁻¹ * k⁻¹ ∈ B.frattiniK :=
      Subgroup.subset_closure (Or.inr ⟨l, hlK, k, hkK, rfl⟩)
    rw [hσdef]
    simp only [dif_pos (hsq _ hklK), dif_pos (hsq _ hkK), dif_pos (hsq _ hlK)]
    have e : (⟨(k * l) * (k * l), hsq _ hklK⟩ : ↥B.frattiniK)
        = (⟨l * k * l⁻¹ * k⁻¹, hcomm⟩ * ⟨k * k, hsq k hkK⟩) * ⟨l * l, hsq l hlK⟩ :=
      Subtype.ext (by
        show (k * l) * (k * l) = l * k * l⁻¹ * k⁻¹ * (k * k) * (l * l)
        have hc' : k * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * k :=
          (hcentral (l * k * l⁻¹ * k⁻¹) hcomm k hkK).symm
        calc (k * l) * (k * l)
            = k * (l * k * l⁻¹ * k⁻¹) * (k * l * l) := by group
          _ = (l * k * l⁻¹ * k⁻¹) * k * (k * l * l) := by rw [hc']
          _ = l * k * l⁻¹ * k⁻¹ * (k * k) * (l * l) := by group)
    rw [e, hlam_hom, hlam_hom, hcomm_kill l hlK k hk hcomm, zero_add]
  have hσR : ∀ r, r ∈ B.frattiniK → σ r = 0 := by
    intro r hr
    rw [hσdef]
    simp only [dif_pos (by rw [hr2 r hr]; exact one_mem _ : r * r ∈ B.frattiniK)]
    have : (⟨r * r, by rw [hr2 r hr]; exact one_mem _⟩ : ↥B.frattiniK) = 1 := Subtype.ext (hr2 r hr)
    rw [this, lam_one]
  -- hom extension `σ₀`
  obtain ⟨σ₀, hσ₀hom, hσ₀ext⟩ := sigma0_extends B σ hσhom hσR
  -- `σ₀|_{K∩S}` is `Y`-invariant (`q`-invariance)
  have hσ₀KSinv : ∀ k, k ∈ B.K ⊓ B.S → ∀ y : Y, σ₀ (y * k * y⁻¹) = σ₀ k := by
    intro k hk y
    have hkK := (Subgroup.mem_inf.mp hk).1
    have hyk : y * k * y⁻¹ ∈ B.K ⊓ B.S := Subgroup.mem_inf.mpr
      ⟨B.hK.conj_mem k hkK y, B.hS.conj_mem k (Subgroup.mem_inf.mp hk).2 y⟩
    rw [hσ₀ext _ hyk, hσ₀ext _ hk, hσdef]
    simp only [dif_pos (hsq _ (B.hK.conj_mem k hkK y)), dif_pos (hsq k hkK)]
    have e : (⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩ : ↥B.frattiniK)
        = ⟨y * (k * k) * y⁻¹, hRN.conj_mem _ (hsq k hkK) y⟩ := Subtype.ext (by group)
    rw [e, hlam_conj y (k * k) (hsq k hkK)]
  -- shear-vanishing: `σ₀` is `Y_V`-invariant
  have hσ₀YV : ∀ (z : Y), (∀ k, k ∈ B.K → z * k * z⁻¹ * k⁻¹ ∈ B.K ⊓ B.S) →
      ∀ k, k ∈ B.K → σ₀ (z * k * z⁻¹) = σ₀ k := by
    intro z hz k hk
    have hs : z * k * z⁻¹ * k⁻¹ ∈ B.K ⊓ B.S := hz k hk
    set s := z * k * z⁻¹ * k⁻¹ with hsdef
    have hsK : s ∈ B.K := (Subgroup.mem_inf.mp hs).1
    have hzk : z * k * z⁻¹ = s * k := by rw [hsdef]; group
    have hσs : σ s = 0 := by
      have hqinv : σ (z * k * z⁻¹) = σ k := by
        rw [hσdef]
        simp only [dif_pos (hsq _ (B.hK.conj_mem k hk z)), dif_pos (hsq k hk)]
        have e : (⟨(z * k * z⁻¹) * (z * k * z⁻¹), hsq _ (B.hK.conj_mem k hk z)⟩ : ↥B.frattiniK)
            = ⟨z * (k * k) * z⁻¹, hRN.conj_mem _ (hsq k hk) z⟩ := Subtype.ext (by group)
        rw [e, hlam_conj z (k * k) (hsq k hk)]
      have hsplit : σ (s * k) = σ s + σ k := by
        have hskK : s * k ∈ B.K := mul_mem hsK hk
        have hcomm2 : k * s * k⁻¹ * s⁻¹ ∈ B.frattiniK :=
          Subgroup.subset_closure (Or.inr ⟨k, hk, s, hsK, rfl⟩)
        rw [hσdef]
        simp only [dif_pos (hsq _ hskK), dif_pos (hsq _ hsK), dif_pos (hsq k hk)]
        have e : (⟨(s * k) * (s * k), hsq _ hskK⟩ : ↥B.frattiniK)
            = (⟨k * s * k⁻¹ * s⁻¹, hcomm2⟩ * ⟨s * s, hsq s hsK⟩) * ⟨k * k, hsq k hk⟩ :=
          Subtype.ext (by
            show (s * k) * (s * k) = k * s * k⁻¹ * s⁻¹ * (s * s) * (k * k)
            have hc' : s * (k * s * k⁻¹ * s⁻¹) = (k * s * k⁻¹ * s⁻¹) * s :=
              (hcentral (k * s * k⁻¹ * s⁻¹) hcomm2 s hsK).symm
            calc (s * k) * (s * k)
                = s * (k * s * k⁻¹ * s⁻¹) * (s * k * k) := by group
              _ = (k * s * k⁻¹ * s⁻¹) * s * (s * k * k) := by rw [hc']
              _ = k * s * k⁻¹ * s⁻¹ * (s * s) * (k * k) := by group)
        rw [e, hlam_hom, hlam_hom, hcomm_kill k hk s hs hcomm2, zero_add]
      rw [hzk] at hqinv
      have h2 : σ s + σ k = 0 + σ k := by rw [zero_add]; exact hsplit.symm.trans hqinv
      exact add_right_cancel h2
    rw [hzk, hσ₀hom s hsK k hk, hσ₀ext s hs, hσs, zero_add]
  -- `H_V` averaging
  obtain ⟨ψ, hψhom, hψYinv, hψext⟩ :=
    hv_average_helper π hπ hkerπ cH hcH B σ₀ hσ₀hom hσ₀KSinv hσ₀YV
  refine ⟨ψ, hψhom, hψYinv, fun k hk hkk => ?_⟩
  rw [hψext k hk, hσ₀ext k hk]
  simp only [hσdef, dif_pos hkk]

/-- **Prop 7.4, step 2** (`q_λ|_{T₀} = 0`): a `Y`-invariant additive `λ : R → 𝔽₂` kills the
squares of `K ∩ S`.  Proved from the tame extension (`key_extension`) and the abstract-block
endgame (`invariant_hom_absurd`): if some `λ(t²) ≠ 0`, the extended `Y`-invariant hom `ψ` is
nonzero there, contradicting `lemma_7_1_dual`. -/
private theorem lam_sq_vanish {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L) (hRN : B.frattiniK.Normal)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩) :
    ∀ t, t ∈ B.K ⊓ B.S → ∀ (h : t * t ∈ B.frattiniK), lam ⟨t * t, h⟩ = 0 := by
  classical
  obtain ⟨ψ, hψhom, hψinv, hψext⟩ :=
    key_extension π hπ hkerπ cH hcH B hRN lam hlam_hom hlam_conj
  intro t₀ ht₀ h
  by_contra hne
  exact invariant_hom_absurd B ψ hψhom hψinv t₀ (Subgroup.mem_inf.mp ht₀).1
    (by rw [hψext t₀ ht₀ h]; exact hne)

/-- **Proposition 7.4**: for every nonzero `Y`-invariant functional `λ ∈ D_R = (R^∨)^C`, the
pushout square map of the central extension `1 → 𝔽₂ → K_λ → M → 1` kills `T₀` and its polar
form kills `(T₀, M)`; hence it descends to a **nonzero, nonsingular, `Y`-invariant** quadratic
form `q̄_λ : V → 𝔽₂` on the simple head `V = P/S` — the form §8's Gauss sums live on.
Stated with the square-map spec `λ(k²) = q̄(k mod S)` (`hsq` supplies `k² ∈ R`, Lemma 7.2's
clause, so 7.4 is consumable independently).  The framed-target head data (as in `lemma_7_2`)
encode §7's standing hypothesis, under which
the paper proves 7.4; its step 2 (`q_λ|_{T₀} = 0`) consumes `H¹(H_V, V^∨) = 0`, which needs
the tame structure and fails for general finite heads.  See `docs/section67-extraction.md`.] -/
theorem prop_7_4 {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L)
    (hRN : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y : Y) (r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩)
    (hlam_ne : lam ≠ 0) :
    ∃ qbar : (↥B.P ⧸ (B.S.subgroupOf B.P)) → ZMod 2,
      (∀ (k : Y) (hk : k ∈ B.K), lam ⟨k * k, hsq k hk⟩
        = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩)) ∧
      qbar ≠ 0 ∧
      (∀ (y : Y) (p : Y) (hp : p ∈ B.P),
        qbar (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
          = qbar (QuotientGroup.mk ⟨p, hp⟩)) := by
  classical
  haveI := B.hS
  have hB := lam_comm_vanish B hRN lam hlam_hom hlam_conj
  have hA := lam_sq_vanish π hπ hkerπ cH hcH B hRN lam hlam_hom hlam_conj
  -- master well-definedness: representatives in the same `S`-coset have equal square-values
  have hwd : ∀ (k k' : Y) (hk : k ∈ B.K) (hk' : k' ∈ B.K),
      (QuotientGroup.mk (⟨k, B.hKP hk⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = QuotientGroup.mk ⟨k', B.hKP hk'⟩ →
      lam ⟨k * k, hsq k hk⟩ = lam ⟨k' * k', hsq k' hk'⟩ := by
    intro k k' hk hk' hmk
    rw [QuotientGroup.eq] at hmk
    have htS : k⁻¹ * k' ∈ B.S := Subgroup.mem_subgroupOf.mp hmk
    have htK : k⁻¹ * k' ∈ B.K := B.K.mul_mem (B.K.inv_mem hk) hk'
    have hcm : k⁻¹ * (k⁻¹ * k') * k⁻¹⁻¹ * (k⁻¹ * k')⁻¹ ∈ B.frattiniK :=
      comm_mem_R B (B.K.inv_mem hk) htK
    have e : (⟨k' * k', hsq k' hk'⟩ : ↥B.frattiniK)
        = (⟨k * k, hsq k hk⟩ * ⟨k⁻¹ * (k⁻¹ * k') * k⁻¹⁻¹ * (k⁻¹ * k')⁻¹, hcm⟩)
            * ⟨(k⁻¹ * k') * (k⁻¹ * k'), hsq _ htK⟩ := Subtype.ext (by
      show k' * k'
        = k * k * (k⁻¹ * (k⁻¹ * k') * k⁻¹⁻¹ * (k⁻¹ * k')⁻¹) * ((k⁻¹ * k') * (k⁻¹ * k'))
      group)
    rw [e, hlam_hom, hlam_hom,
      hB k⁻¹ (B.K.inv_mem hk) (k⁻¹ * k') (Subgroup.mem_inf.mpr ⟨htK, htS⟩) hcm,
      hA (k⁻¹ * k') (Subgroup.mem_inf.mpr ⟨htK, htS⟩) (hsq _ htK), add_zero, add_zero]
  -- every class has a `K`-representative
  have hdec : ∀ v : ↥B.P ⧸ B.S.subgroupOf B.P,
      ∃ k, ∃ hk : k ∈ B.K, (QuotientGroup.mk (⟨k, B.hKP hk⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = v := by
    intro v
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective v
    have hp' : (p : Y) ∈ (B.K : Set Y) * (B.S : Set Y) := by
      rw [← Subgroup.mul_normal B.K B.S, B.gen]
      exact p.2
    obtain ⟨k, hk, s, hs, hks⟩ := hp'
    refine ⟨k, hk, ?_⟩
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    show k⁻¹ * (p : Y) ∈ B.S
    have hkp : k⁻¹ * (p : Y) = s := by rw [← hks]; group
    rw [hkp]
    exact hs
  choose w hwK hwmk using hdec
  refine ⟨fun v => lam ⟨w v * w v, hsq (w v) (hwK v)⟩, ?_, ?_, ?_⟩
  · -- the square-map spec
    intro k hk
    exact (hwd (w _) k (hwK _) hk (hwmk _)).symm
  · -- nonzero
    intro h0
    have h0v : ∀ v, lam ⟨w v * w v, hsq (w v) (hwK v)⟩ = 0 := fun v => congrFun h0 v
    have lam_one : lam 1 = 0 := by simpa using hlam_hom 1 1
    -- squares vanish under λ
    have hsqv : ∀ (k : Y) (hk : k ∈ B.K), lam ⟨k * k, hsq k hk⟩ = 0 := by
      intro k hk
      rw [hwd k (w _) hk (hwK _) (hwmk _).symm]
      exact h0v _
    -- commutators vanish under λ
    have hcomm0 : ∀ (a b : Y), a ∈ B.K → b ∈ B.K →
        ∀ h : a * b * a⁻¹ * b⁻¹ ∈ B.frattiniK, lam ⟨a * b * a⁻¹ * b⁻¹, h⟩ = 0 := by
      intro a b ha hb h
      have hx : a⁻¹ ∈ B.K := B.K.inv_mem ha
      have hxy : a⁻¹ * b ∈ B.K := B.K.mul_mem hx hb
      have e : (⟨(a⁻¹ * b) * (a⁻¹ * b), hsq _ hxy⟩ : ↥B.frattiniK)
          = (⟨a⁻¹ * a⁻¹, hsq _ hx⟩ * ⟨a * b * a⁻¹ * b⁻¹, h⟩) * ⟨b * b, hsq b hb⟩ :=
        Subtype.ext (by
          show (a⁻¹ * b) * (a⁻¹ * b) = a⁻¹ * a⁻¹ * (a * b * a⁻¹ * b⁻¹) * (b * b)
          group)
      have h1 := hsqv (a⁻¹ * b) hxy
      rw [e, hlam_hom, hlam_hom, hsqv a⁻¹ hx, hsqv b hb, zero_add, add_zero] at h1
      exact h1
    -- so λ kills all of `R = Φ(K)`, contradicting `hlam_ne`
    let Z' : Subgroup Y :=
      { carrier := {x | ∃ hx : x ∈ B.frattiniK, lam ⟨x, hx⟩ = 0}
        one_mem' := ⟨one_mem _, lam_one⟩
        mul_mem' := by
          rintro a b ⟨ha, la⟩ ⟨hb, lb⟩
          refine ⟨mul_mem ha hb, ?_⟩
          have h := hlam_hom ⟨a, ha⟩ ⟨b, hb⟩
          rw [la, lb, add_zero] at h
          exact h
        inv_mem' := by
          rintro a ⟨ha, la⟩
          refine ⟨inv_mem ha, ?_⟩
          have h := hlam_hom ⟨a, ha⟩ ⟨a⁻¹, inv_mem ha⟩
          have e : (⟨a, ha⟩ * ⟨a⁻¹, inv_mem ha⟩ : ↥B.frattiniK) = 1 := Subtype.ext (by
            show a * a⁻¹ = 1
            group)
          rw [e, lam_one, la, zero_add] at h
          exact h.symm }
    have hRZ : B.frattiniK ≤ Z' := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x (⟨k, hk, rfl⟩ | ⟨k, hk, l, hl, rfl⟩)
      · exact ⟨sq_mem_R B hk, hsqv k hk⟩
      · exact ⟨comm_mem_R B hk hl, hcomm0 k l hk hl _⟩
    apply hlam_ne
    funext r
    obtain ⟨hr', h0'⟩ := hRZ r.2
    have hre : lam r = lam ⟨r.1, hr'⟩ := rfl
    rw [hre, h0']
    rfl
  · -- `Y`-invariance
    intro y p hp
    have hkK : w (QuotientGroup.mk ⟨p, hp⟩) ∈ B.K := hwK _
    set k := w (QuotientGroup.mk ⟨p, hp⟩) with hkdef
    have hkpS : k⁻¹ * p ∈ B.S := by
      have hkp := hwmk (QuotientGroup.mk (⟨p, hp⟩ : ↥B.P))
      rw [QuotientGroup.eq] at hkp
      exact Subgroup.mem_subgroupOf.mp hkp
    have hmk1 : (QuotientGroup.mk (⟨y * k * y⁻¹, B.hKP (B.hK.conj_mem k hkK y)⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P)
          = QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩ := by
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (y * k * y⁻¹)⁻¹ * (y * p * y⁻¹) ∈ B.S
      have e : (y * k * y⁻¹)⁻¹ * (y * p * y⁻¹) = y * (k⁻¹ * p) * y⁻¹ := by group
      rw [e]
      exact B.hS.conj_mem _ hkpS y
    have step1 : lam ⟨w (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
          * w (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩), hsq _ (hwK _)⟩
        = lam ⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩ :=
      hwd (w _) (y * k * y⁻¹) (hwK _) (B.hK.conj_mem k hkK y) ((hwmk _).trans hmk1.symm)
    have step2 : lam ⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩
        = lam ⟨k * k, hsq k hkK⟩ := by
      have e : (⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩ : ↥B.frattiniK)
          = ⟨y * (k * k) * y⁻¹, hRN.conj_mem _ (hsq k hkK) y⟩ := Subtype.ext (by
        show (y * k * y⁻¹) * (y * k * y⁻¹) = y * (k * k) * y⁻¹
        group)
      rw [e]
      exact hlam_conj y (k * k) (hsq k hkK)
    exact step1.trans step2


end SectionSeven

end GQ2
