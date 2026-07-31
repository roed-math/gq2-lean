/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.PropSevenFour
import GQ2.Block.FormFields

/-!
# The block-form enrichment fields at a general residue cardinality (ticket SD-R1, SEAM A ripple)

Clone of the `cH`-consuming half of `GQ2/Block/FormFields.lean` (328 ln), re-typed at F3's
`Tq q` on top of `GQ2/Dyadic/Recursion/PropSevenFour.lean`'s `prop_7_4K`.

## What is reused rather than cloned

`GQ2/Block/FormFields.lean`'s file-level `variable` binds `cH`, but Lean includes a section
variable only where it is *used*, and nine of its declarations never touch it.  Those are
consumed by import, unchanged:

* `BlockDR` (:38), `blockDR_normal` (:42), `blockHRn` (:48), `blockHsq` (:54), `blockHidx`
  (:61), `blockHlt` (:69) — the character-index layer;
* `blockScalarCover` (:240), `blockScalarCover_p` (:247), `blockZ_pow_lam` (:255) — the scalar
  cover layer.

So the `K`-side and the `ℚ₂` side share one `BlockDR` and one `blockScalarCover`; only the
sixteen form fields below are duplicated.

## The parameterization delta

Every clone gains `{q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)` and takes
`cH : ContinuousMonoidHom (Tq q) H`.  **`prop_7_4` is applied exactly once in the whole file**
(`FormFields.lean:77`, inside `blockProp74`); that single application becomes `prop_7_4K hq0
hqe …`.  Every other declaration threads `cH`/`hcH` without inspecting them, so all sixteen
bodies are byte-identical to their models modulo the `…K` renaming.

Axioms: none beyond std-3; each clone's print equals its model's.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionSeven GQ2.SectionEight GQ2.SectionNine QuadraticFp2

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
  {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
  (cH : ContinuousMonoidHom (Tq q) H) (hcH : Function.Surjective cH)
variable [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]

/-! ## The Prop 7.4 / mForm packages -/

/-- The Prop 7.4 output existential for the block character `λ_l`. -/
noncomputable def blockProp74K (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :=
  prop_7_4K hq0 hqe T.piY T.piY_surjective T.ker_piY cH hcH Blk (blockHRn T Blk) (blockHsq T Blk)
    (blockLam Blk l.1) (blockLam_hom Blk l.1 (blockHidx T Blk l hlne))
    (blockLam_conj Blk l.1 l.2.1 (blockHRn T Blk))
    (blockLam_ne Blk l.1 (blockHlt T Blk l hlne))

/-- The descended form `q̄_λ` on `V = P/S` (Prop 7.4's output, multiplicative model). -/
noncomputable def blockQbarRawK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) → ZMod 2 :=
  (blockProp74K T Blk hq0 hqe cH hcH l hlne).choose

/-- The mForm output existential (the `M_B`-level square form). -/
noncomputable def blockMFormK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :=
  mForm_of_qbar Blk (QuotientGroup.mk' Blk.frattiniK) (QuotientGroup.ker_mk' Blk.frattiniK)
    (blockLam Blk l.1) (blockLam_hom Blk l.1 (blockHidx T Blk l hlne)) (blockHsq T Blk)
    (blockQbarRawK T Blk hq0 hqe cH hcH l hlne) (blockProp74K T Blk hq0 hqe cH hcH l hlne).choose_spec.1

/-- The `M_B`-level square form `q_λ` (the Enrichment `q` field). -/
noncomputable def blockQK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ↥(Blk.K.map (QuotientGroup.mk' Blk.frattiniK)) → ZMod 2 :=
  (blockMFormK T Blk hq0 hqe cH hcH l hlne).choose

/-- The descended form on `Vmod = Additive (P/S)` (the Enrichment `qbar` field). -/
noncomputable def blockQbarK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) → ZMod 2 :=
  fun v => blockQbarRawK T Blk hq0 hqe cH hcH l hlne (Additive.toMul v)

/-! ## Direct consequences (Prop 7.4 / mForm clauses) -/
omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- `hspec`: `λ(k²) = q̄(⟦k⟧)`. -/
theorem blockHspecK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ∀ (k : Y) (hk : k ∈ Blk.K),
      blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩
        = blockQbarRawK T Blk hq0 hqe cH hcH l hlne (QuotientGroup.mk ⟨k, Blk.hKP hk⟩) :=
  (blockProp74K T Blk hq0 hqe cH hcH l hlne).choose_spec.1

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- `q̄_λ ≠ 0` (Prop 7.4 nonzero). -/
theorem blockHneK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    blockQbarRawK T Blk hq0 hqe cH hcH l hlne ≠ 0 :=
  (blockProp74K T Blk hq0 hqe cH hcH l hlne).choose_spec.2.1

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- Raw `Y`-invariance of `q̄_λ` (Prop 7.4 third clause). -/
theorem blockHinvRawK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ∀ (y p : Y) (hp : p ∈ Blk.P),
      blockQbarRawK T Blk hq0 hqe cH hcH l hlne
          (QuotientGroup.mk ⟨y * p * y⁻¹, Blk.hP.conj_mem p hp y⟩)
        = blockQbarRawK T Blk hq0 hqe cH hcH l hlne (QuotientGroup.mk ⟨p, hp⟩) :=
  (blockProp74K T Blk hq0 hqe cH hcH l hlne).choose_spec.2.2

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- mForm value clause: `q_λ(π_B k) = λ(k²)`. -/
theorem blockHvalK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ∀ (k : Y) (hk : k ∈ Blk.K),
      blockQK T Blk hq0 hqe cH hcH l hlne
          ⟨QuotientGroup.mk' Blk.frattiniK k, Subgroup.mem_map_of_mem _ hk⟩
        = blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩ :=
  (blockMFormK T Blk hq0 hqe cH hcH l hlne).choose_spec.1

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- `hrad`: `T_B` lies in the polar radical of `q_λ`. -/
theorem blockHradK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ∀ (t : Y ⧸ Blk.frattiniK)
      (ht : t ∈ ((Blk.K ⊓ Blk.S) ⊔ Blk.frattiniK).map (QuotientGroup.mk' Blk.frattiniK))
      (m : Y ⧸ Blk.frattiniK) (hm : m ∈ Blk.K.map (QuotientGroup.mk' Blk.frattiniK)),
      polarMul (blockQK T Blk hq0 hqe cH hcH l hlne) (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩)
        ⟨t, blockT_map_le_blockM_map Blk (QuotientGroup.mk' Blk.frattiniK) ht⟩ ⟨m, hm⟩ = 0 :=
  (blockMFormK T Blk hq0 hqe cH hcH l hlne).choose_spec.2.1

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal] in
/-- `hTzero`: `q_λ` vanishes on `T_B`. -/
theorem blockHTzeroK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ∀ (t : Y ⧸ Blk.frattiniK)
      (ht : t ∈ ((Blk.K ⊓ Blk.S) ⊔ Blk.frattiniK).map (QuotientGroup.mk' Blk.frattiniK)),
      blockQK T Blk hq0 hqe cH hcH l hlne
          ⟨t, blockT_map_le_blockM_map Blk (QuotientGroup.mk' Blk.frattiniK) ht⟩ = 0 :=
  (blockMFormK T Blk hq0 hqe cH hcH l hlne).choose_spec.2.2

/-! ## Quadraticity, nonsingularity -/
omit [(Blk.S.subgroupOf Blk.P).Normal] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] [Blk.K.Normal] in
/-- `hquad`: `q̄_λ` is a quadratic form (biadditive polar). -/
theorem blockHquadK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    letI := blockPS_commGroup Blk
    IsQuadraticFp2 (blockQbarK T Blk hq0 hqe cH hcH l hlne) := by
  haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
  letI := blockPS_commGroup Blk
  exact isQuadraticFp2_of_mul (blockQbarRawK T Blk hq0 hqe cH hcH l hlne)
    (blockQbar_map_zero Blk (blockHRn T Blk) (blockHsq T Blk) (blockLam Blk l.1)
      (blockLam_hom Blk l.1 (blockHidx T Blk l hlne)) (blockQbarRawK T Blk hq0 hqe cH hcH l hlne)
      (blockHspecK T Blk hq0 hqe cH hcH l hlne))
    (blockQbar_polar_add Blk (blockHRn T Blk) (blockHsq T Blk) (blockLam Blk l.1)
      (blockLam_hom Blk l.1 (blockHidx T Blk l hlne))
      (blockLam_conj Blk l.1 l.2.1 (blockHRn T Blk)) (blockQbarRawK T Blk hq0 hqe cH hcH l hlne)
      (blockHspecK T Blk hq0 hqe cH hcH l hlne))

omit [(Blk.S.subgroupOf Blk.P).Normal] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  [TopologicalSpace Y] [DiscreteTopology Y] [Blk.frattiniK.Normal] [Blk.K.Normal] in
/-- `hns`: `q̄_λ` is nonsingular. -/
theorem blockHnsK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    letI := blockPS_commGroup Blk
    Nonsingular (blockQbarK T Blk hq0 hqe cH hcH l hlne) := by
  haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
  letI := blockPS_commGroup Blk
  refine nonsingular_of_mul (blockQbarRawK T Blk hq0 hqe cH hcH l hlne) ?_
  exact blockQbar_nonsingular_mul Blk (blockHRn T Blk) (blockHsq T Blk) (blockLam Blk l.1)
    (blockLam_hom Blk l.1 (blockHidx T Blk l hlne))
    (blockLam_conj Blk l.1 l.2.1 (blockHRn T Blk)) (blockQbarRawK T Blk hq0 hqe cH hcH l hlne)
    (blockHspecK T Blk hq0 hqe cH hcH l hlne) (Function.ne_iff.mp (blockHneK T Blk hq0 hqe cH hcH l hlne))
    (blockHinvRawK T Blk hq0 hqe cH hcH l hlne)

/-! ## Invariance packaged over the `C = Y/K` action -/

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]
  [Blk.frattiniK.Normal] in
/-- `hinv`: `q̄_λ` is invariant under the `Y/K`-action (`blockActV`). -/
theorem blockHinvK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    letI := blockActV Blk
    IsInvariant (Y ⧸ Blk.K) (blockQbarK T Blk hq0 hqe cH hcH l hlne) := by
  haveI := Blk.hK
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  intro c v
  induction c using QuotientGroup.induction_on with | _ y =>
  obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (QuotientGroup.mk p) := by rw [hp]; rfl
  rw [hv]
  show blockQbarRawK T Blk hq0 hqe cH hcH l hlne
      (Additive.toMul ((QuotientGroup.mk' Blk.K y) • Additive.ofMul (QuotientGroup.mk p)))
    = blockQbarRawK T Blk hq0 hqe cH hcH l hlne (Additive.toMul (Additive.ofMul (QuotientGroup.mk p)))
  rw [blockActV_mk' Blk y (Additive.ofMul (QuotientGroup.mk p)), blockActVY_mk Blk y p]
  exact blockHinvRawK T Blk hq0 hqe cH hcH l hlne y (p : Y) p.2

/-! ## The coupling `hqbar : q_λ = q̄_λ ∘ descend` -/
omit [Blk.K.Normal] [TopologicalSpace E] [DiscreteTopology E] [Finite E] [TopologicalSpace Y]
  [DiscreteTopology Y] in
/-- `hqbar`: `q_λ(m) = q̄_λ(descend m)`. -/
theorem blockHqbarK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK) :
    ∀ m : ↥(blockMB Blk),
      blockQK T Blk hq0 hqe cH hcH l hlne m
        = blockQbarRawK T Blk hq0 hqe cH hcH l hlne (blockDescend Blk m) := by
  haveI hRn := blockHRn T Blk
  haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
  haveI := Blk.hK
  intro m
  obtain ⟨k, rfl⟩ := blockKappa_surjective Blk m
  have hval := blockHvalK T Blk hq0 hqe cH hcH l hlne (k : Y) k.2
  have hspec := blockHspecK T Blk hq0 hqe cH hcH l hlne (k : Y) k.2
  have hqeq : blockQK T Blk hq0 hqe cH hcH l hlne (blockKappa Blk k)
      = blockLam Blk l.1 ⟨(k : Y) * (k : Y), blockHsq T Blk (k : Y) k.2⟩ := hval
  rw [blockDescend_kappa Blk k, blockAlpha_apply Blk k, hqeq, hspec]
  rfl

omit [TopologicalSpace E] [DiscreteTopology E] [Finite E] [(Blk.S.subgroupOf Blk.P).Normal]
  [Blk.K.Normal] in
/-- `hq`: the cover square relation `x² = z^{q_λ(p x)}` on `M_B`. -/
theorem blockHqK (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.frattiniK)
    (x : (blockScalarCover T Blk hE2 l hlne).cover)
    (hx : (blockScalarCover T Blk hE2 l hlne).p x ∈ Blk.K.map (QuotientGroup.mk' Blk.frattiniK)) :
    x * x = (blockScalarCover T Blk hE2 l hlne).z
      ^ (blockQK T Blk hq0 hqe cH hcH l hlne ⟨(blockScalarCover T Blk hE2 l hlne).p x, hx⟩).val := by
  obtain ⟨k, hk, hpk⟩ := Subgroup.mem_map.mp hx
  -- lift `k` into the cover `Y ⧸ l.1` (ascribed to the cover type to keep products cover-typed)
  set kk : (blockScalarCover T Blk hE2 l hlne).cover := QuotientGroup.mk' l.1 k with hkk
  -- `p kk = ⟦k⟧_R = p x`, so `x * kk⁻¹ ∈ ker p`
  have hpkk : (blockScalarCover T Blk hE2 l hlne).p kk
      = (blockScalarCover T Blk hE2 l hlne).p x := by
    rw [hkk, blockScalarCover_p T Blk hE2 l hlne k, ← hpk]
  have hu : x * kk⁻¹ ∈ (blockScalarCover T Blk hE2 l hlne).p.ker :=
    MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hpkk, mul_inv_cancel])
  -- `x * x = kk * kk` : `x` differs from `kk` by a central element of order 2
  have hsqx : x * x = kk * kk := by
    rcases eq_one_or_z_of_mem_ker (blockScalarCover T Blk hE2 l hlne) hu with he | he
    · rw [mul_inv_eq_one.mp he]
    · rw [mul_inv_eq_iff_eq_mul.mp he]
      calc (blockScalarCover T Blk hE2 l hlne).z * kk
            * ((blockScalarCover T Blk hE2 l hlne).z * kk)
          = (blockScalarCover T Blk hE2 l hlne).z
              * (kk * (blockScalarCover T Blk hE2 l hlne).z) * kk := by simp only [mul_assoc]
        _ = (blockScalarCover T Blk hE2 l hlne).z
              * ((blockScalarCover T Blk hE2 l hlne).z * kk) * kk := by
              rw [(blockScalarCover T Blk hE2 l hlne).central kk]
        _ = ((blockScalarCover T Blk hE2 l hlne).z * (blockScalarCover T Blk hE2 l hlne).z)
              * (kk * kk) := by simp only [mul_assoc]
        _ = kk * kk := by rw [(blockScalarCover T Blk hE2 l hlne).z_sq, one_mul]
  -- `q_λ(p x) = λ(k*k)`, and `kk * kk = ⟦k*k⟧_l = z^{λ(k*k)}` (`blockZ_pow_lam`)
  have hqval : blockQK T Blk hq0 hqe cH hcH l hlne ⟨(blockScalarCover T Blk hE2 l hlne).p x, hx⟩
      = blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩ := by
    have hval := blockHvalK T Blk hq0 hqe cH hcH l hlne k hk
    have hxeq : (⟨(blockScalarCover T Blk hE2 l hlne).p x, hx⟩ :
          ↥(Blk.K.map (QuotientGroup.mk' Blk.frattiniK)))
        = ⟨QuotientGroup.mk' Blk.frattiniK k, Subgroup.mem_map_of_mem _ hk⟩ :=
      Subtype.ext hpk.symm
    rw [hxeq, hval]
  rw [hsqx, hqval, hkk]
  show QuotientGroup.mk' l.1 k * QuotientGroup.mk' l.1 k
    = (blockScalarCover T Blk hE2 l hlne).z ^ (blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩).val
  rw [← map_mul]
  exact blockZ_pow_lam T Blk hE2 l hlne (k * k) (blockHsq T Blk k hk)

end GQ2.Dyadic
