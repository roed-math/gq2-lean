import GQ2.SectionNine
import GQ2.FrameEnrichment
import GQ2.Block.Descent
import GQ2.Block.Char

/-!
# P-17d2b — the concrete block-form enrichment fields (scratch)

Assembly of the §9 block enrichment's non-κ⁰ fields for the concrete frame
`RF = blockFrame T Blk hE2`: `q`/`qbar` (from `prop_7_4` + `mForm_of_qbar`), the coupling
`hqbar`, the radical/vanishing clauses `hrad`/`hTzero`, invariance `hinv`, quadraticity/
nonsingularity `hquad`/`hns` (P-17d2c packaging), and the frame-local cover square `hq`.

All per-`λ` items are stated over `l : BlockDR T Blk` (defeq to `RF.DR`) with `hlne : l.1 ≠ Blk.R`
(defeq-encoding of `l ≠ RF.zeroDR`); the final assembly (P-17d3) drops them into the record.
-/

namespace GQ2

open SectionSeven SectionEight SectionNine QuadraticFp2

open scoped Classical

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)
  (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
variable [Blk.R.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]

/-- The scalar-character index type; reducibly `(blockFrame T Blk hE2).DR`. -/
abbrev BlockDR : Type :=
  {R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}

/-- Each `l : BlockDR` is `Y`-normal (its defining property), as an instance. -/
instance blockDR_normal (l : BlockDR T Blk) : (l.1).Normal := l.2.1

/-- `R = Φ(K)` is `Y`-normal. -/
theorem blockHRn : Blk.R.Normal := frattiniLike_normal Blk.K Blk.hK

/-- `k² ∈ R` for `k ∈ K` (public route: squares generate `Φ(K)`). -/
theorem blockHsq : ∀ k ∈ Blk.K, k * k ∈ Blk.R :=
  fun k hk => Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)

/-- The relative index is exactly 2 for a proper `l`. -/
theorem blockHidx (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    (l.1.subgroupOf Blk.R).index = 2 :=
  relIndex_two_of_le Blk l.1 l.2.2.1 l.2.2.2 hlne

/-- `l.1 < Blk.R`. -/
theorem blockHlt (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) : (l.1 : Subgroup Y) < Blk.R :=
  lt_of_le_of_ne l.2.2.1 hlne

/-! ## The Prop 7.4 / mForm packages -/

/-- The Prop 7.4 output existential for the block character `λ_l`. -/
noncomputable def blockProp74 (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :=
  prop_7_4 T.piY T.piY_surjective T.ker_piY cH hcH Blk (blockHRn T Blk) (blockHsq T Blk)
    (blockLam Blk l.1) (blockLam_hom Blk l.1 (blockHidx T Blk l hlne))
    (blockLam_conj Blk l.1 l.2.1 (blockHRn T Blk))
    (blockLam_ne Blk l.1 (blockHlt T Blk l hlne))

/-- The descended form `q̄_λ` on `V = P/S` (Prop 7.4's output, multiplicative model). -/
noncomputable def blockQbarRaw (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) → ZMod 2 :=
  (blockProp74 T Blk cH hcH l hlne).choose

/-- The mForm output existential (the `M_B`-level square form). -/
noncomputable def blockMForm (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :=
  mForm_of_qbar Blk (QuotientGroup.mk' Blk.R) (QuotientGroup.ker_mk' Blk.R)
    (blockLam Blk l.1) (blockLam_hom Blk l.1 (blockHidx T Blk l hlne)) (blockHsq T Blk)
    (blockQbarRaw T Blk cH hcH l hlne) (blockProp74 T Blk cH hcH l hlne).choose_spec.1

/-- The `M_B`-level square form `q_λ` (the Enrichment `q` field). -/
noncomputable def blockQ (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ↥(Blk.K.map (QuotientGroup.mk' Blk.R)) → ZMod 2 :=
  (blockMForm T Blk cH hcH l hlne).choose

/-- The descended form on `Vmod = Additive (P/S)` (the Enrichment `qbar` field). -/
noncomputable def blockQbar (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P) → ZMod 2 :=
  fun v => blockQbarRaw T Blk cH hcH l hlne (Additive.toMul v)

/-! ## Direct consequences (Prop 7.4 / mForm clauses) -/

/-- `hspec`: `λ(k²) = q̄(⟦k⟧)`. -/
theorem blockHspec (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ∀ (k : Y) (hk : k ∈ Blk.K),
      blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩
        = blockQbarRaw T Blk cH hcH l hlne (QuotientGroup.mk ⟨k, Blk.hKP hk⟩) :=
  (blockProp74 T Blk cH hcH l hlne).choose_spec.1

/-- `q̄_λ ≠ 0` (Prop 7.4 nonzero). -/
theorem blockHne (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    blockQbarRaw T Blk cH hcH l hlne ≠ 0 :=
  (blockProp74 T Blk cH hcH l hlne).choose_spec.2.1

/-- Raw `Y`-invariance of `q̄_λ` (Prop 7.4 third clause). -/
theorem blockHinvRaw (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ∀ (y p : Y) (hp : p ∈ Blk.P),
      blockQbarRaw T Blk cH hcH l hlne
          (QuotientGroup.mk ⟨y * p * y⁻¹, Blk.hP.conj_mem p hp y⟩)
        = blockQbarRaw T Blk cH hcH l hlne (QuotientGroup.mk ⟨p, hp⟩) :=
  (blockProp74 T Blk cH hcH l hlne).choose_spec.2.2

/-- mForm value clause: `q_λ(π_B k) = λ(k²)`. -/
theorem blockHval (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ∀ (k : Y) (hk : k ∈ Blk.K),
      blockQ T Blk cH hcH l hlne
          ⟨QuotientGroup.mk' Blk.R k, Subgroup.mem_map_of_mem _ hk⟩
        = blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩ :=
  (blockMForm T Blk cH hcH l hlne).choose_spec.1

/-- `hrad`: `T_B` lies in the polar radical of `q_λ`. -/
theorem blockHrad (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ∀ (t : Y ⧸ Blk.R) (ht : t ∈ ((Blk.K ⊓ Blk.S) ⊔ Blk.R).map (QuotientGroup.mk' Blk.R))
      (m : Y ⧸ Blk.R) (hm : m ∈ Blk.K.map (QuotientGroup.mk' Blk.R)),
      polarMul (blockQ T Blk cH hcH l hlne) (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩)
        ⟨t, blockT_map_le_blockM_map Blk (QuotientGroup.mk' Blk.R) ht⟩ ⟨m, hm⟩ = 0 :=
  (blockMForm T Blk cH hcH l hlne).choose_spec.2.1

/-- `hTzero`: `q_λ` vanishes on `T_B`. -/
theorem blockHTzero (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ∀ (t : Y ⧸ Blk.R) (ht : t ∈ ((Blk.K ⊓ Blk.S) ⊔ Blk.R).map (QuotientGroup.mk' Blk.R)),
      blockQ T Blk cH hcH l hlne
          ⟨t, blockT_map_le_blockM_map Blk (QuotientGroup.mk' Blk.R) ht⟩ = 0 :=
  (blockMForm T Blk cH hcH l hlne).choose_spec.2.2

/-! ## Quadraticity, nonsingularity (P-17d2c packaging) -/

/-- `hquad`: `q̄_λ` is a quadratic form (biadditive polar). -/
theorem blockHquad (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    letI := blockPS_commGroup Blk
    IsQuadraticFp2 (blockQbar T Blk cH hcH l hlne) := by
  haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
  letI := blockPS_commGroup Blk
  exact isQuadraticFp2_of_mul (blockQbarRaw T Blk cH hcH l hlne)
    (blockQbar_map_zero Blk (blockHRn T Blk) (blockHsq T Blk) (blockLam Blk l.1)
      (blockLam_hom Blk l.1 (blockHidx T Blk l hlne)) (blockQbarRaw T Blk cH hcH l hlne)
      (blockHspec T Blk cH hcH l hlne))
    (blockQbar_polar_add Blk (blockHRn T Blk) (blockHsq T Blk) (blockLam Blk l.1)
      (blockLam_hom Blk l.1 (blockHidx T Blk l hlne))
      (blockLam_conj Blk l.1 l.2.1 (blockHRn T Blk)) (blockQbarRaw T Blk cH hcH l hlne)
      (blockHspec T Blk cH hcH l hlne))

/-- `hns`: `q̄_λ` is nonsingular. -/
theorem blockHns (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    letI := blockPS_commGroup Blk
    Nonsingular (blockQbar T Blk cH hcH l hlne) := by
  haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
  letI := blockPS_commGroup Blk
  refine nonsingular_of_mul (blockQbarRaw T Blk cH hcH l hlne) ?_
  exact blockQbar_nonsingular_mul Blk (blockHRn T Blk) (blockHsq T Blk) (blockLam Blk l.1)
    (blockLam_hom Blk l.1 (blockHidx T Blk l hlne))
    (blockLam_conj Blk l.1 l.2.1 (blockHRn T Blk)) (blockQbarRaw T Blk cH hcH l hlne)
    (blockHspec T Blk cH hcH l hlne) (Function.ne_iff.mp (blockHne T Blk cH hcH l hlne))
    (blockHinvRaw T Blk cH hcH l hlne)

/-! ## Invariance packaged over the `C = Y/K` action -/

/-- `hinv`: `q̄_λ` is invariant under the `Y/K`-action (`blockActV`). -/
theorem blockHinv (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    letI := blockActV Blk
    IsInvariant (Y ⧸ Blk.K) (blockQbar T Blk cH hcH l hlne) := by
  haveI := Blk.hK
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  intro c v
  induction c using QuotientGroup.induction_on with | _ y =>
  obtain ⟨p, hp⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
  have hv : v = Additive.ofMul (QuotientGroup.mk p) := by rw [hp]; rfl
  rw [hv]
  show blockQbarRaw T Blk cH hcH l hlne
      (Additive.toMul ((QuotientGroup.mk' Blk.K y) • Additive.ofMul (QuotientGroup.mk p)))
    = blockQbarRaw T Blk cH hcH l hlne (Additive.toMul (Additive.ofMul (QuotientGroup.mk p)))
  rw [blockActV_mk' Blk y (Additive.ofMul (QuotientGroup.mk p)), blockActVY_mk Blk y p]
  exact blockHinvRaw T Blk cH hcH l hlne y (p : Y) p.2

/-! ## The coupling `hqbar : q_λ = q̄_λ ∘ descend` -/

/-- `hqbar`: `q_λ(m) = q̄_λ(descend m)`. -/
theorem blockHqbar (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    ∀ m : ↥(blockMB Blk),
      blockQ T Blk cH hcH l hlne m
        = blockQbarRaw T Blk cH hcH l hlne (blockDescend Blk m) := by
  haveI hRn := blockHRn T Blk
  haveI : (Blk.S.subgroupOf Blk.P).Normal := Blk.hS.subgroupOf Blk.P
  haveI := Blk.hK
  intro m
  obtain ⟨k, rfl⟩ := blockKappa_surjective Blk m
  have hval := blockHval T Blk cH hcH l hlne (k : Y) k.2
  have hspec := blockHspec T Blk cH hcH l hlne (k : Y) k.2
  have hqeq : blockQ T Blk cH hcH l hlne (blockKappa Blk k)
      = blockLam Blk l.1 ⟨(k : Y) * (k : Y), blockHsq T Blk (k : Y) k.2⟩ := hval
  rw [blockDescend_kappa Blk k, blockAlpha_apply Blk k, hqeq, hspec]
  rfl

/-! ## The frame-local cover square `hq` -/

/-- The scalar cover of `l` (reducibly `RF.scalarCover l (·)`). -/
noncomputable def blockScalarCover (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) :
    CentralCover (Y ⧸ Blk.R) :=
  (blockFrame T Blk hE2).scalarCover l (fun heq => hlne (congrArg Subtype.val heq))

/-- The cover projection sends `⟦y⟧_l` to `⟦y⟧_R`. -/
theorem blockScalarCover_p (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) (y : Y) :
    (blockScalarCover T Blk hE2 l hlne).p (QuotientGroup.mk' l.1 y) = QuotientGroup.mk' Blk.R y :=
  rfl

/-- Auxiliary: for `r ∈ R`, the class `⟦r⟧_{l} = z^{λ_l(r)}` in the cover. -/
theorem blockZ_pow_lam (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R) (r : Y) (hr : r ∈ Blk.R) :
    QuotientGroup.mk' l.1 r
      = (blockScalarCover T Blk hE2 l hlne).z ^ (blockLam Blk l.1 ⟨r, hr⟩).val := by
  have hp1 : (blockScalarCover T Blk hE2 l hlne).p (QuotientGroup.mk' l.1 r) = 1 := by
    rw [blockScalarCover_p T Blk hE2 l hlne r, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff r).mpr hr
  have hmemker : QuotientGroup.mk' l.1 r ∈ (blockScalarCover T Blk hE2 l hlne).p.ker :=
    MonoidHom.mem_ker.mpr hp1
  by_cases hrl : r ∈ l.1
  · have h0 : blockLam Blk l.1 ⟨r, hr⟩ = 0 := (blockLam_eq_zero_iff Blk l.1 ⟨r, hr⟩).mpr hrl
    rw [h0, show (0 : ZMod 2).val = 0 by decide, pow_zero, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff r).mpr hrl
  · have h1 : blockLam Blk l.1 ⟨r, hr⟩ = 1 := by unfold blockLam; rw [if_neg hrl]
    have hmkne : QuotientGroup.mk' l.1 r ≠ 1 := by
      rw [QuotientGroup.mk'_apply]; exact fun hh => hrl ((QuotientGroup.eq_one_iff r).mp hh)
    rw [h1, show (1 : ZMod 2).val = 1 by decide, pow_one]
    rcases eq_one_or_z_of_mem_ker (blockScalarCover T Blk hE2 l hlne) hmemker with he | he
    · exact absurd he hmkne
    · exact he

/-- `hq`: the cover square relation `x² = z^{q_λ(p x)}` on `M_B`. -/
theorem blockHq (l : BlockDR T Blk) (hlne : l.1 ≠ Blk.R)
    (x : (blockScalarCover T Blk hE2 l hlne).cover)
    (hx : (blockScalarCover T Blk hE2 l hlne).p x ∈ Blk.K.map (QuotientGroup.mk' Blk.R)) :
    x * x = (blockScalarCover T Blk hE2 l hlne).z
      ^ (blockQ T Blk cH hcH l hlne ⟨(blockScalarCover T Blk hE2 l hlne).p x, hx⟩).val := by
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
  have hqval : blockQ T Blk cH hcH l hlne ⟨(blockScalarCover T Blk hE2 l hlne).p x, hx⟩
      = blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩ := by
    have hval := blockHval T Blk cH hcH l hlne k hk
    have hxeq : (⟨(blockScalarCover T Blk hE2 l hlne).p x, hx⟩ :
          ↥(Blk.K.map (QuotientGroup.mk' Blk.R)))
        = ⟨QuotientGroup.mk' Blk.R k, Subgroup.mem_map_of_mem _ hk⟩ :=
      Subtype.ext hpk.symm
    rw [hxeq, hval]
  rw [hsqx, hqval, hkk]
  show QuotientGroup.mk' l.1 k * QuotientGroup.mk' l.1 k
    = (blockScalarCover T Blk hE2 l hlne).z ^ (blockLam Blk l.1 ⟨k * k, blockHsq T Blk k hk⟩).val
  rw [← map_mul]
  exact blockZ_pow_lam T Blk hE2 l hlne (k * k) (blockHsq T Blk k hk)

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 7.4 = ⟦prop-simpleheaddet⟧
-/
