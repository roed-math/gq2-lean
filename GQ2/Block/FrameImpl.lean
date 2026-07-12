import GQ2.RadicalEdge.Bridge
import GQ2.FiniteGroupLemmas

/-!
# P-17c: the concrete recursion frame of a §7 block (`blockFrame` implementation)

Constructs the `SectionEight.RecursionFrame T Blk` of the paper's §9 induction from a marked
target `T` and a §7 minimal block `Blk` on `T.LY`.  The `B`-stage is `Y/R` and the `C`-stage is
`Y/K` (`R = Φ(K) ≤ K`); the head and θ-decoration descend through these quotients
(`R ≤ K ≤ L_Y = ker π_Y` for the head; `lemma_7_3` + `hE2` — `K ⊆ ker θ` — for the decoration).
The scalar-character index `D_R` is the subtype of `Y`-normal index-≤2 subgroups of `R`, and each
nonzero `λ` gives the scalar central cover `Y/λ ↠ Y/R` with central generator the class of an
`r₀ ∈ R ∖ λ` (centrality: `R/λ` is an order-2 normal subgroup of `Y/λ`, hence central).

This is the implementation half of `GQ2.SectionNine.blockFrame` (P-17c); `SectionNine.blockFrame`
delegates to `blockFrameImpl`.
-/

namespace GQ2

open SectionEight SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- **The concrete recursion frame of a §7 block** (P-17c). -/
noncomputable def blockFrameImpl (T : MarkedTarget H E Y) (Blk : MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) : RecursionFrame T Blk := by
  haveI hRn : Blk.R.Normal := frattiniLike_normal Blk.K Blk.hK
  haveI hKn : Blk.K.Normal := Blk.hK
  have hRK : Blk.R ≤ Blk.K := frattiniLike_le Blk.K
  have hKL : Blk.K ≤ T.LY := Blk.hKP.trans Blk.hPL
  have hRkerpi : Blk.R ≤ T.piY.ker := by rw [T.ker_piY]; exact hRK.trans hKL
  have hKkerpi : Blk.K ≤ T.piY.ker := by rw [T.ker_piY]; exact hKL
  have hKkerth : Blk.K ≤ T.thetaY.ker := lemma_7_3 Blk hE2 T.thetaY
  have hRkerth : Blk.R ≤ T.thetaY.ker := hRK.trans hKkerth
  letI : TopologicalSpace (Y ⧸ Blk.R) := ⊥
  haveI : DiscreteTopology (Y ⧸ Blk.R) := ⟨rfl⟩
  letI : TopologicalSpace (Y ⧸ Blk.K) := ⊥
  haveI : DiscreteTopology (Y ⧸ Blk.K) := ⟨rfl⟩
  haveI : Finite (Subgroup Y) :=
    Finite.of_injective (fun G : Subgroup Y => (G : Set Y)) SetLike.coe_injective
  haveI hfDR : Fintype {R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2} :=
    Fintype.ofFinite _
  exact
    { YB := Y ⧸ Blk.R
      piB := QuotientGroup.mk' Blk.R
      piB_surj := QuotientGroup.mk'_surjective Blk.R
      ker_piB := QuotientGroup.ker_mk' Blk.R
      TB :=
        { LY := T.LY.map (QuotientGroup.mk' Blk.R)
          normal := T.normal.map (QuotientGroup.mk' Blk.R) (QuotientGroup.mk'_surjective Blk.R)
          isPGroup_two := T.isPGroup_two.map _
          piY := QuotientGroup.lift Blk.R T.piY hRkerpi
          piY_surjective := fun hh => by
            obtain ⟨y, hy⟩ := T.piY_surjective hh
            exact ⟨QuotientGroup.mk' Blk.R y, by
              rwa [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']⟩
          ker_piY := by rw [QuotientGroup.ker_lift, T.ker_piY]
          thetaY := QuotientGroup.lift Blk.R T.thetaY hRkerth }
      TB_head := QuotientGroup.lift_comp_mk' Blk.R T.piY hRkerpi
      TB_theta := QuotientGroup.lift_comp_mk' Blk.R T.thetaY hRkerth
      YC := Y ⧸ Blk.K
      piC := QuotientGroup.mk' Blk.K
      piC_surj := QuotientGroup.mk'_surjective Blk.K
      ker_piC := QuotientGroup.ker_mk' Blk.K
      TC :=
        { LY := T.LY.map (QuotientGroup.mk' Blk.K)
          normal := T.normal.map (QuotientGroup.mk' Blk.K) (QuotientGroup.mk'_surjective Blk.K)
          isPGroup_two := T.isPGroup_two.map _
          piY := QuotientGroup.lift Blk.K T.piY hKkerpi
          piY_surjective := fun hh => by
            obtain ⟨y, hy⟩ := T.piY_surjective hh
            exact ⟨QuotientGroup.mk' Blk.K y, by
              rwa [QuotientGroup.mk'_apply, QuotientGroup.lift_mk']⟩
          ker_piY := by rw [QuotientGroup.ker_lift, T.ker_piY]
          thetaY := QuotientGroup.lift Blk.K T.thetaY hKkerth }
      TC_head := QuotientGroup.lift_comp_mk' Blk.K T.piY hKkerpi
      TC_theta := QuotientGroup.lift_comp_mk' Blk.K T.thetaY hKkerth
      piBC := QuotientGroup.map Blk.R Blk.K (MonoidHom.id Y)
        (by rw [Subgroup.comap_id]; exact hRK)
      piBC_comp := by ext y; rfl
      MB := Blk.K.map (QuotientGroup.mk' Blk.R)
      MB_eq := rfl
      TBsub := ((Blk.K ⊓ Blk.S) ⊔ Blk.R).map (QuotientGroup.mk' Blk.R)
      TBsub_eq := rfl
      DR := {R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}
      zeroDR := ⟨Blk.R, hRn, le_refl _, by rw [Subgroup.relIndex_self]; norm_num⟩
      card_DR := rfl
      scalarCover := fun l h => by
        haveI : (l.1).Normal := l.2.1
        letI : TopologicalSpace (Y ⧸ l.1) := ⊥
        haveI : DiscreteTopology (Y ⧸ l.1) := ⟨rfl⟩
        have hlt : l.1 < Blk.R := lt_of_le_of_ne l.2.2.1 (fun heq => h (Subtype.ext heq))
        let r₀ : Y := (SetLike.exists_of_lt hlt).choose
        have hr₀ : r₀ ∈ Blk.R ∧ r₀ ∉ l.1 := (SetLike.exists_of_lt hlt).choose_spec
        -- `[R : R'] = 2`
        have hri2 : l.1.relIndex Blk.R = 2 := by
          have hne1 : l.1.relIndex Blk.R ≠ 1 := fun hcon =>
            absurd (le_antisymm l.2.2.1 (Subgroup.relIndex_eq_one.mp hcon)) (ne_of_lt hlt)
          have hne0 : l.1.relIndex Blk.R ≠ 0 :=
            Subgroup.index_ne_zero_of_finite
          have hle := l.2.2.2
          omega
        -- from index 2: two elements of `R` outside `R'` differ (right) by `R'`
        have key : ∀ b ∈ Blk.R, b ∉ l.1 → ∀ c ∈ Blk.R, c ∉ l.1 → b * c⁻¹ ∈ l.1 := by
          obtain ⟨a, _, hXor⟩ := Subgroup.relIndex_eq_two_iff.mp hri2
          intro b hbR hbR' c hcR hcR'
          have hba : b * a ∈ l.1 := by
            rcases hXor b hbR with ⟨h1, _⟩ | ⟨h2, _⟩
            · exact h1
            · exact absurd h2 hbR'
          have hca : c * a ∈ l.1 := by
            rcases hXor c hcR with ⟨h1, _⟩ | ⟨h2, _⟩
            · exact h1
            · exact absurd h2 hcR'
          have := l.1.mul_mem hba (l.1.inv_mem hca)
          rwa [show b * a * (c * a)⁻¹ = b * c⁻¹ from by group] at this
        have hr₀inv : r₀⁻¹ ∉ l.1 := fun hc => hr₀.2 (by rwa [Subgroup.inv_mem_iff] at hc)
        refine
          { cover := Y ⧸ l.1
            p := QuotientGroup.map l.1 Blk.R (MonoidHom.id Y)
              (by rw [Subgroup.comap_id]; exact l.2.2.1)
            surj := ?_
            z := QuotientGroup.mk' l.1 r₀
            z_ne := ?_
            z_sq := ?_
            central := ?_
            ker_eq := ?_ }
        · intro x
          induction x using QuotientGroup.induction_on with
          | _ y => exact ⟨QuotientGroup.mk' l.1 y, by simp⟩
        · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact hr₀.2
        · -- `z² = 1`: `r₀ * r₀ ∈ R'`
          rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          have := key r₀ hr₀.1 hr₀.2 r₀⁻¹ (Blk.R.inv_mem hr₀.1) hr₀inv
          rwa [inv_inv] at this
        · -- centrality: `[y, r₀] ∈ R'` for all `y`
          intro x
          refine QuotientGroup.induction_on x (fun y => ?_)
          have hbR : y⁻¹ * r₀⁻¹ * y ∈ Blk.R := by
            simpa using hRn.conj_mem r₀⁻¹ (Blk.R.inv_mem hr₀.1) y⁻¹
          have hbR' : y⁻¹ * r₀⁻¹ * y ∉ l.1 := fun hbmem => hr₀.2 (by
            have := l.2.1.conj_mem _ hbmem y
            rw [show y * (y⁻¹ * r₀⁻¹ * y) * y⁻¹ = r₀⁻¹ from by group] at this
            rwa [Subgroup.inv_mem_iff] at this)
          have hk := key _ hbR hbR' r₀⁻¹ (Blk.R.inv_mem hr₀.1) hr₀inv
          rw [inv_inv] at hk
          show QuotientGroup.mk' l.1 r₀ * QuotientGroup.mk' l.1 y
            = QuotientGroup.mk' l.1 y * QuotientGroup.mk' l.1 r₀
          rwa [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
            QuotientGroup.eq, show (r₀ * y)⁻¹ * (y * r₀) = y⁻¹ * r₀⁻¹ * y * r₀ from by group]
        · -- kernel: `p.ker = R.map (mk' R') = ⟨z⟩`
          have hker : (QuotientGroup.map l.1 Blk.R (MonoidHom.id Y)
              (by rw [Subgroup.comap_id]; exact l.2.2.1)).ker
              = Blk.R.map (QuotientGroup.mk' l.1) := by
            ext x
            refine QuotientGroup.induction_on x (fun y => ?_)
            rw [MonoidHom.mem_ker,
              show (QuotientGroup.map l.1 Blk.R (MonoidHom.id Y)
                (by rw [Subgroup.comap_id]; exact l.2.2.1)) (↑y) = ((y : Y) : Y ⧸ Blk.R) from rfl,
              QuotientGroup.eq_one_iff, Subgroup.mem_map]
            refine ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩
            rintro ⟨r, hrR, hr⟩
            rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hr
            rw [show y = r * (r⁻¹ * y) from by group]
            exact Blk.R.mul_mem hrR (l.2.2.1 hr)
          rw [hker]
          apply le_antisymm
          · rw [Subgroup.map_le_iff_le_comap]
            intro r hrR
            rw [Subgroup.mem_comap]
            by_cases hrR' : r ∈ l.1
            · have h1 : QuotientGroup.mk' l.1 r = 1 := by
                rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hrR'
              rw [h1]; exact one_mem _
            · have hrz : QuotientGroup.mk' l.1 r = QuotientGroup.mk' l.1 r₀ := by
                rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
                have hk := key r⁻¹ (Blk.R.inv_mem hrR)
                  (fun hh => hrR' (by rwa [Subgroup.inv_mem_iff] at hh))
                  r₀⁻¹ (Blk.R.inv_mem hr₀.1) hr₀inv
                rwa [inv_inv] at hk
              rw [hrz]; exact Subgroup.mem_zpowers _
          · rw [Subgroup.zpowers_le]
            exact Subgroup.mem_map_of_mem _ hr₀.1 }

end GQ2
