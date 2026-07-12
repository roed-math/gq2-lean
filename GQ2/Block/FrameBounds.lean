import GQ2.Block.FrameImpl

/-!
# P-17g: the Lemma 9.4 descent bounds for `blockFrame`

Displays (145)/(148)/(153) of the paper's §9 induction: the marked-kernel cardinalities of the
`blockFrame`'s stage targets and of the pulled-back strata all drop strictly below `|L_Y|`, which
is what lets the master induction (P-17i) recurse on `n = Nat.card ↥T.LY`.

Stated against `blockFrameImpl` (P-17c, committed); `SectionNine.blockFrame` delegates to it, so
these apply to `blockFrame` by definitional unfolding.

* `card_LB_mul` / `card_LB_lt` — `|L_B|·|R| = |L_Y|`, and `|L_B| < |L_Y|` when `R ≠ ⊥`.
* `card_LC_lt` — `|L_C| < |L_Y|` (from `K ≠ ⊥`).
* `four_le_card_K` — `4 ≤ |K|` (the `dim V ≥ 2` input: `|K| = 2` collapses the `Y`-action mod `S`).
* `card_stratum_LB_lt` — (148): a proper `C`-onto stratum of a central cover of `B` has
  `|stratum.L| < |L_Y|` (double cover ×2 against the index-2 `J∩L_B < L_B`, ÷|R| via `R ≠ ⊥`).
* `card_stratum_LC_lt` — (153): any stratum of a central cover of `C` has `|stratum.L| < |L_Y|`
  (trivial `⊆ p⁻¹(L_C)` bound `= 2|L_C|`, against `4 ≤ |K|`).

All bounds are **cover-generic** (independent of which `CentralCover`), which is what lets P-17i
apply them to `prop_8_9`'s ∃-quantified phase family.
-/

namespace GQ2

open SectionEight SectionSeven
open scoped Pointwise

/-! ## General card helpers -/

section Helpers

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

omit [Finite G'] in
/-- **Preimage cardinality under a surjection**: `|f⁻¹(S)| = |S|·|ker f|`. -/
lemma card_comap_of_surjective {f : G' →* G} (hf : Function.Surjective f) (S : Subgroup G) :
    Nat.card ↥(S.comap f) = Nat.card ↥S * Nat.card ↥f.ker := by
  have hidx : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : Nat.card ↥(S.comap f) * S.index = Nat.card G' := by
    rw [← Subgroup.index_comap_of_surjective S hf]; exact Subgroup.card_mul_index _
  have h2 : Nat.card ↥S * S.index = Nat.card G := Subgroup.card_mul_index _
  have h3 : Nat.card G' = Nat.card G * Nat.card ↥f.ker := by
    have hq : Nat.card G' = Nat.card (G' ⧸ f.ker) * Nat.card ↥f.ker :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have he : Nat.card (G' ⧸ f.ker) = Nat.card G :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv
    rw [hq, he]
  -- cancel the (nonzero) index
  have : Nat.card ↥(S.comap f) * S.index = (Nat.card ↥S * Nat.card ↥f.ker) * S.index := by
    rw [h1, h3, ← h2]; ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) this

/-- **Image cardinality under `mk'`**: for `N ≤ H` with `N` normal, the image of `H` in `G/N`
has size `|H|/|N|`, i.e. `|H.map (mk' N)| · |N| = |H|` (Lagrange on `H ↠ H/N`). -/
lemma card_map_mk'_mul {N Hs : Subgroup G} [N.Normal] (hNH : N ≤ Hs) :
    Nat.card ↥(Hs.map (QuotientGroup.mk' N)) * Nat.card ↥N = Nat.card ↥Hs := by
  have hcomap := card_comap_of_surjective (QuotientGroup.mk'_surjective N)
    (Hs.map (QuotientGroup.mk' N))
  rw [QuotientGroup.comap_map_mk', sup_of_le_right hNH, QuotientGroup.ker_mk'] at hcomap
  exact hcomap.symm

/-- **The preimage of a subgroup under a central cover doubles it**: `|p⁻¹(L)| = 2·|L|`. -/
lemma centralCover_card_comap (C : CentralCover G) (L : Subgroup G) :
    Nat.card ↥(L.comap C.p) = 2 * Nat.card ↥L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_comap_of_surjective C.surj L, C.ker_eq, Nat.card_zpowers,
    orderOf_eq_prime (by rw [pow_two]; exact C.z_sq) C.z_ne, mul_comm]

omit [Finite G] in
/-- `|H.subgroupOf K| = |H ⊓ K|` (the intersection viewed inside `K`, `K.subtype` injective). -/
lemma card_subgroupOf_eq_inf (A K : Subgroup G) :
    Nat.card ↥(A.subgroupOf K) = Nat.card ↥(A ⊓ K) := by
  have e : (A.subgroupOf K).map K.subtype = A ⊓ K := by
    show (A.comap K.subtype).map K.subtype = A ⊓ K
    rw [Subgroup.map_comap_eq, Subgroup.range_subtype, inf_comm]
  rw [Nat.card_congr (Subgroup.equivMapOfInjective (A.subgroupOf K) K.subtype
    (Subgroup.subtype_injective K)).toEquiv, e]

/-- **Central covers are at most 2-to-1**: for any subgroup `W` of the cover, `|W| ≤ 2·|p(W)|`. -/
lemma centralCover_card_le_two_mul_card_map (C : CentralCover G) (W : Subgroup C.cover) :
    Nat.card ↥W ≤ 2 * Nat.card ↥(W.map C.p) := by
  calc Nat.card ↥W ≤ Nat.card ↥((W.map C.p).comap C.p) :=
        Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective (Subgroup.le_comap_map C.p W))
    _ = 2 * Nat.card ↥(W.map C.p) := centralCover_card_comap C _

end Helpers

/-! ## Setup -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY) (hE2 : ∀ e : E, e ^ 2 = 1)

/-- `R = Φ(K)` is normal in `Y`. -/
instance : (Blk.frattiniK).Normal := frattiniLike_normal Blk.K Blk.hK

/-- `K` is normal in `Y` (block field, re-exposed as an instance). -/
instance : (Blk.K).Normal := Blk.hK

-- The topology stack on `H`/`E`/`Y` is only needed to *build* `blockFrameImpl`; every bound
-- below depends only on its group-level fields (`.TB.LY`/`.MB`/`.YB` reduce past the topology).
omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y]

lemma blockFrameImpl_R_le_LY : Blk.frattiniK ≤ T.LY :=
  (frattiniLike_le Blk.K).trans (Blk.hKP.trans Blk.hPL)

lemma blockFrameImpl_K_le_LY : Blk.K ≤ T.LY := Blk.hKP.trans Blk.hPL

/-- `K ≠ ⊥`: else `K ⊔ S = S = P` contradicts `S < P`. -/
lemma blockFrameImpl_K_ne_bot : Blk.K ≠ ⊥ := by
  intro hK
  have hSP : Blk.S = Blk.P := by rw [← Blk.gen, hK, bot_sup_eq]
  exact absurd hSP Blk.hSP.ne

/-! ### Field-projection reductions -/

@[simp] lemma blockFrameImpl_TB_LY :
    (blockFrameImpl T Blk hE2).TB.LY = T.LY.map (QuotientGroup.mk' Blk.frattiniK) := rfl

@[simp] lemma blockFrameImpl_TC_LY :
    (blockFrameImpl T Blk hE2).TC.LY = T.LY.map (QuotientGroup.mk' Blk.K) := rfl


/-- `M ≤ L_B` in `B` (both images of `K ≤ L_Y`), stated in projection form so it composes with
`Cov`'s `(blockFrameImpl …).YB`-typed subgroups. -/
lemma blockFrameImpl_MB_le_TB_LY :
    (blockFrameImpl T Blk hE2).MB ≤ (blockFrameImpl T Blk hE2).TB.LY := by
  show Blk.K.map (QuotientGroup.mk' Blk.frattiniK) ≤ T.LY.map (QuotientGroup.mk' Blk.frattiniK)
  exact Subgroup.map_mono (blockFrameImpl_K_le_LY T Blk)

/-! ## (145) — the stage-target bounds -/

/-- **(145a)**: `|L_B|·|R| = |L_Y|`. -/
lemma card_LB_mul :
    Nat.card ↥(blockFrameImpl T Blk hE2).TB.LY * Nat.card ↥Blk.frattiniK = Nat.card ↥T.LY := by
  rw [blockFrameImpl_TB_LY]
  exact card_map_mk'_mul (blockFrameImpl_R_le_LY T Blk)

/-- **(145b)**: `|L_B| < |L_Y|` when `R ≠ ⊥`. -/
lemma card_LB_lt (hR : Blk.frattiniK ≠ ⊥) :
    Nat.card ↥(blockFrameImpl T Blk hE2).TB.LY < Nat.card ↥T.LY := by
  have hmul := card_LB_mul T Blk hE2
  have hR2 : 1 < Nat.card ↥Blk.frattiniK :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot _).mpr hR)
  have hLB : 0 < Nat.card ↥(blockFrameImpl T Blk hE2).TB.LY := Nat.card_pos
  nlinarith [hmul, hR2, hLB]

/-- **(145c)**: `|L_C| < |L_Y|` (`K ≠ ⊥`). -/
lemma card_LC_lt :
    Nat.card ↥(blockFrameImpl T Blk hE2).TC.LY < Nat.card ↥T.LY := by
  have hmul : Nat.card ↥(blockFrameImpl T Blk hE2).TC.LY * Nat.card ↥Blk.K = Nat.card ↥T.LY := by
    rw [blockFrameImpl_TC_LY]; exact card_map_mk'_mul (blockFrameImpl_K_le_LY T Blk)
  have hK2 : 1 < Nat.card ↥Blk.K :=
    Finite.one_lt_card_iff_nontrivial.mpr
      ((Subgroup.nontrivial_iff_ne_bot _).mpr (blockFrameImpl_K_ne_bot T Blk))
  have hLC : 0 < Nat.card ↥(blockFrameImpl T Blk hE2).TC.LY := Nat.card_pos
  nlinarith [hmul, hK2, hLC]

/-! ## `4 ≤ |K|` — the `dim V ≥ 2` input for (153) -/

/-- **`4 ≤ |K|`** (paper: `dim V ≥ 2`).  If `|K| = 2` then `K` is central (normal of order 2),
so `[Y, P] ≤ S` (extending across `P = K·S`), contradicting `nontrivial_action`. -/
lemma four_le_card_K : 4 ≤ Nat.card ↥Blk.K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Blk.hS
  have hK2grp : IsPGroup 2 Blk.K := Blk.h2L.to_le (blockFrameImpl_K_le_LY T Blk)
  obtain ⟨n, hn⟩ := hK2grp.exists_card_eq
  -- `|K| ≠ 2`: else `K` central (normal of order 2) ⟹ `[Y, P] ≤ S`, contradicting nontriviality
  have hKne2 : Nat.card ↥Blk.K ≠ 2 := by
    intro hcard2
    obtain ⟨g, -, hg_uniq⟩ := (Nat.card_eq_two_iff' (1 : ↥Blk.K)).mp hcard2
    have hcentral : ∀ k ∈ Blk.K, ∀ y : Y, y * k * y⁻¹ = k := by
      intro k hk y
      by_cases hk1 : k = 1
      · subst hk1; group
      · have hconj : y * k * y⁻¹ ∈ Blk.K := Blk.hK.conj_mem k hk y
        have ek : (⟨k, hk⟩ : ↥Blk.K) ≠ 1 := by
          simp only [ne_eq, Subgroup.mk_eq_one]; exact hk1
        have econj : (⟨y * k * y⁻¹, hconj⟩ : ↥Blk.K) ≠ 1 := by
          simp only [ne_eq, Subgroup.mk_eq_one]
          intro h; apply hk1
          have hkk : k = y⁻¹ * (y * k * y⁻¹) * y := by group
          rw [hkk, h]; group
        have : (⟨y * k * y⁻¹, hconj⟩ : ↥Blk.K) = (⟨k, hk⟩ : ↥Blk.K) :=
          (hg_uniq _ econj).trans (hg_uniq _ ek).symm
        exact congrArg Subtype.val this
    have hcomm : ∀ (y k : Y), k ∈ Blk.K → y * k * y⁻¹ * k⁻¹ ∈ Blk.S := by
      intro y k hk; rw [hcentral k hk y]; simp
    have hcommP : ∀ (y p : Y), p ∈ Blk.P → y * p * y⁻¹ * p⁻¹ ∈ Blk.S := by
      intro y p hp
      rw [← Blk.gen] at hp
      have hp' : p ∈ (Blk.K : Set Y) * (Blk.S : Set Y) := by
        rw [← Subgroup.mul_normal Blk.K Blk.S]; exact hp
      obtain ⟨k, hk, s, hs, rfl⟩ := hp'
      have heq : y * (k * s) * y⁻¹ * (k * s)⁻¹
          = (y * k * y⁻¹ * k⁻¹) * (k * ((y * s * y⁻¹) * s⁻¹) * k⁻¹) := by group
      rw [heq]
      exact mul_mem (hcomm y k hk)
        (Blk.hS.conj_mem _ (mul_mem (Blk.hS.conj_mem s hs y) (inv_mem hs)) k)
    obtain ⟨y, p, hpP, hnot⟩ := Blk.nontrivial_action
    exact hnot (hcommP y p hpP)
  -- `|K| = 2ⁿ`, `≠ 1` (`K ≠ ⊥`), `≠ 2` ⟹ `n ≥ 2` ⟹ `2ⁿ ≥ 4`
  have hn2 : 2 ≤ n := by
    rcases n with _ | _ | n
    · rw [pow_zero] at hn; exact absurd (Subgroup.card_eq_one.mp hn) (blockFrameImpl_K_ne_bot T Blk)
    · rw [pow_one] at hn; exact absurd hn hKne2
    · omega
  rw [hn]
  calc (4 : ℕ) = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2

/-! ## (148)/(153) — the pulled-back stratum bounds -/

/-- **(148)**: for a central cover `Cov` of `B`, a proper (`J ≠ ⊤`) `C`-onto (`J ⊔ M = ⊤`)
stratum has marked kernel `< |L_Y|`. -/
lemma card_stratum_LB_lt (hR : Blk.frattiniK ≠ ⊥) (Cov : CentralCover (blockFrameImpl T Blk hE2).YB)
    (J' : Subgroup Cov.cover)
    (hJ' : Function.Surjective
      ((Cov.pullTarget (blockFrameImpl T Blk hE2).TB).piY.comp J'.subtype))
    (hJtop : J'.map Cov.p ≠ ⊤)
    (hJC : J'.map Cov.p ⊔ (blockFrameImpl T Blk hE2).MB = ⊤) :
    Nat.card ↥((Cov.pullTarget (blockFrameImpl T Blk hE2).TB).stratum J' hJ').LY
      < Nat.card ↥T.LY := by
  set LB := (blockFrameImpl T Blk hE2).TB.LY with hLB
  set MB := (blockFrameImpl T Blk hE2).MB with hMB
  set J := J'.map Cov.p with hJdef
  -- reduce `stratum.LY` to the concrete intersection `p⁻¹(L_B) ⊓ J'`
  have key : Nat.card ↥((Cov.pullTarget (blockFrameImpl T Blk hE2).TB).stratum J' hJ').LY
      = Nat.card ↥(LB.comap Cov.p ⊓ J') := by
    rw [show ((Cov.pullTarget (blockFrameImpl T Blk hE2).TB).stratum J' hJ').LY
        = (LB.comap Cov.p).subgroupOf J' from rfl, card_subgroupOf_eq_inf]
  rw [key]
  -- `W := p⁻¹(L_B) ⊓ J'`; `p(W) ≤ L_B ⊓ J`
  have hWmap : (LB.comap Cov.p ⊓ J').map Cov.p ≤ LB ⊓ J :=
    le_trans (Subgroup.map_inf_le (LB.comap Cov.p) J' Cov.p)
      (inf_le_inf (Subgroup.map_comap_le Cov.p LB) le_rfl)
  -- `L_B ⊓ J < L_B` (proper): else `M ≤ L_B ≤ J` forces `J = J ⊔ M = ⊤`
  have hproper : ¬ LB ≤ J := fun hle =>
    hJtop ((sup_eq_left.mpr ((blockFrameImpl_MB_le_TB_LY T Blk hE2).trans hle)).symm.trans hJC)
  -- Lagrange in `L_B`: `|L_B ⊓ J| · relindex = |L_B|`, with `relindex ≥ 2`
  have hlag : Nat.card ↥(LB ⊓ J) * (J.subgroupOf LB).index = Nat.card ↥LB := by
    have hc : Nat.card ↥(LB ⊓ J) = Nat.card ↥(J.subgroupOf LB) := by
      rw [card_subgroupOf_eq_inf, inf_comm]
    rw [hc]; exact Subgroup.card_mul_index _
  have hidx2 : 2 ≤ (J.subgroupOf LB).index := by
    have hne1 : (J.subgroupOf LB).index ≠ 1 := fun h1 =>
      hproper (Subgroup.subgroupOf_eq_top.mp (Subgroup.index_eq_one.mp h1))
    have hne0 : (J.subgroupOf LB).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hstep4 : 2 * Nat.card ↥(LB ⊓ J) ≤ Nat.card ↥LB := by
    rw [← hlag, mul_comm 2]; gcongr
  -- chain: `|W| ≤ 2|p(W)| ≤ 2|L_B ⊓ J| ≤ |L_B| < |L_Y|`
  calc Nat.card ↥(LB.comap Cov.p ⊓ J')
      ≤ 2 * Nat.card ↥((LB.comap Cov.p ⊓ J').map Cov.p) :=
        centralCover_card_le_two_mul_card_map Cov _
    _ ≤ 2 * Nat.card ↥(LB ⊓ J) := by
        gcongr; exact Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hWmap)
    _ ≤ Nat.card ↥LB := hstep4
    _ < Nat.card ↥T.LY := by rw [hLB]; exact card_LB_lt T Blk hE2 hR

/-- **(153)**: for a central cover `Cov` of `C`, any stratum has marked kernel `< |L_Y|`
(trivial `⊆ p⁻¹(L_C)` bound `= 2|L_C|`, against `4 ≤ |K|`). -/
lemma card_stratum_LC_lt (Cov : CentralCover (blockFrameImpl T Blk hE2).YC)
    (J' : Subgroup Cov.cover)
    (hJ' : Function.Surjective
      ((Cov.pullTarget (blockFrameImpl T Blk hE2).TC).piY.comp J'.subtype)) :
    Nat.card ↥((Cov.pullTarget (blockFrameImpl T Blk hE2).TC).stratum J' hJ').LY
      < Nat.card ↥T.LY := by
  -- `stratum.LY = (L_C.comap p).subgroupOf J' ≤`-card `p⁻¹(L_C)`, of size `2·|L_C|`
  have hle : Nat.card ↥((Cov.pullTarget (blockFrameImpl T Blk hE2).TC).stratum J' hJ').LY
      ≤ 2 * Nat.card ↥(T.LY.map (QuotientGroup.mk' Blk.K)) := by
    refine le_trans (Nat.le_of_dvd Nat.card_pos ?_)
      (le_of_eq (centralCover_card_comap Cov (T.LY.map (QuotientGroup.mk' Blk.K))))
    exact Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.subtype_injective J')
  -- `2·|L_C| < |L_C|·|K| = |L_Y|` via `4 ≤ |K|`
  have hmul : Nat.card ↥(T.LY.map (QuotientGroup.mk' Blk.K)) * Nat.card ↥Blk.K = Nat.card ↥T.LY :=
    card_map_mk'_mul (blockFrameImpl_K_le_LY T Blk)
  have hK4 : 4 ≤ Nat.card ↥Blk.K := four_le_card_K T Blk
  have hLCpos : 0 < Nat.card ↥(T.LY.map (QuotientGroup.mk' Blk.K)) := Nat.card_pos
  nlinarith [hle, hmul, hK4, hLCpos]

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 9.4 = ⟦lem-strictdecrease⟧ (= lemma 8.16 in current tex)
-/
