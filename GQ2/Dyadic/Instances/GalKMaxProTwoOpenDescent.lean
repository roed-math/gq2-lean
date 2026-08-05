/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageKernelFiniteLevel
import GQ2.Dyadic.Instances.GammaLDualityBoundary
import GQ2.Dyadic.LocalGauss.PairingK

/-!
# The open-neighbourhood reduction for the maximal pro-two kernel

The only classes not covered by the existing B6 inflation comparison are intrinsic classes on
`proPKernel 2 (GalK K)`.  Continuous cohomology identifies their degree-two cohomology with the
filtered colimit over open ambient overgroups.  This file isolates that standard continuity
statement and proves that it is the sole remaining input: B6 and B7 at each open local layer,
together with the already-proved intrinsic kernel `H¹` vanishing, kill every descended class.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh
open GQ2.Dyadic.LiftingDualityG
open scoped Classical Pointwise

noncomputable section

section ScalarLocalDuality

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]

/-- Coefficient naturality identifying the B6 evaluation cup with the scalar mod-two cup. -/
theorem cup11_zmodMuDualEquiv_eq_trivialCup
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (x y : H1 G (ZMod 2)) :
    cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2))
        (H1congr zmodMuDualEquiv zmodMuDualEquiv_equivariant x) y
      = H2congr LocalLiftingDuality.muNTwoEquiv.symm
          (muNTwoEquiv_symm_equivariantG htriv)
          (trivialCupPairing 2 G htriv x y) := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := G) (M := ZMod 2) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := G) (M := ZMod 2) y
  rfl

/-- B6 makes the scalar mod-two cup pairing nondegenerate in the left slot. -/
theorem exists_trivialCupPairing_ne_zero_of_tateDuality
    (D : TateDualityG G 2)
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (x : H1 G (ZMod 2)) (hx : x ≠ 0) :
    ∃ y : H1 G (ZMod 2), trivialCupPairing 2 G htriv x y ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  apply hx
  have hperf := D.perfect11 (ZMod 2) (by decide)
  set e := H1congr (G := G) zmodMuDualEquiv zmodMuDualEquiv_equivariant with he
  have h0 : D.inv.toAddMonoidHom.comp
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2))) (e x))
      = D.inv.toAddMonoidHom.comp
        ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
          (0 : H1 G (MuDual 2 (ZMod 2)))) := by
    ext y
    rw [map_zero, AddMonoidHom.comp_zero]
    show D.inv _ = _
    rw [he, cup11_zmodMuDualEquiv_eq_trivialCup htriv x y, hnone y, map_zero, map_zero]
    simp
  rw [← AddEquiv.symm_apply_apply e x, hperf.1 h0, map_zero]

/-- If scalar `H¹` is nontrivial, B6 and `#H² = 2` imply every scalar `H²` class is a
single cup product (with the zero class represented by the empty sum). -/
theorem scalarH2GeneratedByCupProducts_of_tateDuality
    (D : TateDualityG G 2)
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hH1 : Nontrivial (H1 G (ZMod 2))) :
    ScalarH2GeneratedByCupProducts (G := G) htriv := by
  letI : Nontrivial (H1 G (ZMod 2)) := hH1
  obtain ⟨x, hx⟩ := exists_ne (0 : H1 G (ZMod 2))
  obtain ⟨y, hxy⟩ := exists_trivialCupPairing_ne_zero_of_tateDuality D htriv x hx
  have hcard : Nat.card (H2 G (ZMod 2)) = 2 := card_H2_zmod2_eq_twoG D htriv
  obtain ⟨u, hu_ne, hu_unique⟩ := (Nat.card_eq_two_iff' (0 : H2 G (ZMod 2))).mp hcard
  intro z
  by_cases hz : z = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
    simpa [hz]
  · have hcup : trivialCupPairing 2 G htriv x y = u := hu_unique _ hxy
    have hzu : z = u := hu_unique z hz
    refine ⟨1, (fun _ ↦ x), (fun _ ↦ y), ?_⟩
    simpa [hzu, hcup]

end ScalarLocalDuality

section ClosedSubgroupContinuity

variable {G M : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [Finite M] [DistribMulAction G M] [ContinuousSMul G M]

/-- The continuous inclusion associated to a containment of subgroups. -/
def continuousSubgroupInclusion {N H : Subgroup G} (hNH : N ≤ H) :
    ContinuousMonoidHom N H where
  toFun n := ⟨n.1, hNH n.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact continuous_subtype_val

/-- Every continuous degree-two cocycle on a closed normal subgroup of a profinite group
extends to a cocycle on some open ambient overgroup.

This is the concrete cochain form of continuity of continuous cohomology under closed
subgroups.  First extend the finite-discrete cocycle as a continuous function on `G²`.  Its
cocycle defect is zero on the compact set `N³`; tube lemmas give one open neighbourhood `O`
of `N` on which the defect remains zero.  A sufficiently small open normal subgroup `L` has
`N L ⊆ O`, and `H = N ⊔ L` is the required open overgroup. -/
theorem exists_open_overgroup_cocycle_extension
    (N : Subgroup G) [N.Normal] [IsClosed (N : Set G)]
    [DistribMulAction N M] [ContinuousSMul N M]
    (haction : ∀ (n : N) (m : M), n.1 • m = n • m)
    (z : Z2 N M) :
    ∃ (H : Subgroup G) (hNH : N ≤ H), IsOpen (H : Set G) ∧
      ∃ w : Z2 H M,
        H2mk N M
          (Z2comap (continuousSubgroupInclusion hNH) (AddMonoidHom.id M) continuous_id
            (fun n m ↦ by
              change n.1 • m = n • m
              exact haction n m) w) = H2mk N M z := by
  let NN : Subgroup (G × G) := N.prod N
  let phi : NN → M := fun p ↦
    z.1 (⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2⟩)
  have hphi : Continuous phi := by
    have hz := (mem_Z2_iff.mp z.2).1
    apply hz.comp
    exact (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _).prodMk
      (Continuous.subtype_mk (continuous_snd.comp continuous_subtype_val) _)
  have hNNclosed : IsClosed (NN : Set (G × G)) := by
    change IsClosed ((N : Set G) ×ˢ (N : Set G))
    exact (show IsClosed (N : Set G) from inferInstance).prod
      (show IsClosed (N : Set G) from inferInstance)
  letI : IsClosed (NN : Set (G × G)) := hNNclosed
  obtain ⟨c, hc, hcN⟩ :=
    exists_continuous_extension_of_closed_subgroup NN phi hphi
  let defect : G × (G × G) → M := dTwo G M c
  have hdefect_cont : Continuous defect := by
    dsimp only [defect, dTwo]
    exact ((continuous_fst.smul
        (hc.comp ((continuous_fst.comp continuous_snd).prodMk
          (continuous_snd.comp continuous_snd)))).sub
        (hc.comp ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
          (continuous_snd.comp continuous_snd)))).add
      (hc.comp (continuous_fst.prodMk
        ((continuous_fst.comp continuous_snd).mul (continuous_snd.comp continuous_snd)))) |>.sub
      (hc.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  let Z : Set (G × (G × G)) := defect ⁻¹' {0}
  have hZopen : IsOpen Z :=
    (isOpen_discrete {0}).preimage hdefect_cont
  have hNZ : (N : Set G) ×ˢ ((N : Set G) ×ˢ (N : Set G)) ⊆ Z := by
    rintro ⟨g, ⟨h, k⟩⟩ ⟨ng, ⟨nh, nk⟩⟩
    let pgh : NN := ⟨(g, h), ⟨ng, nh⟩⟩
    let phk : NN := ⟨(h, k), ⟨nh, nk⟩⟩
    let pghk : NN := ⟨(g * h, k), ⟨N.mul_mem ng nh, nk⟩⟩
    let pgh' : NN := ⟨(g, h * k), ⟨ng, N.mul_mem nh nk⟩⟩
    have hcgh := hcN pgh
    have hchk := hcN phk
    have hcghk := hcN pghk
    have hcgh' := hcN pgh'
    change c (g, h) = z.1 (⟨g, ng⟩, ⟨h, nh⟩) at hcgh
    change c (h, k) = z.1 (⟨h, nh⟩, ⟨k, nk⟩) at hchk
    change c (g * h, k) = z.1
      (⟨g * h, N.mul_mem ng nh⟩, ⟨k, nk⟩) at hcghk
    change c (g, h * k) = z.1
      (⟨g, ng⟩, ⟨h * k, N.mul_mem nh nk⟩) at hcgh'
    have hz_coc := (mem_Z2_iff.mp z.2).2
      (⟨g, ng⟩ : N) (⟨h, nh⟩ : N) (⟨k, nk⟩ : N)
    have hz_coc' :
        (⟨g, ng⟩ : N) • z.1 ((⟨h, nh⟩ : N), (⟨k, nk⟩ : N)) +
            z.1 ((⟨g, ng⟩ : N), (⟨h * k, N.mul_mem nh nk⟩ : N)) =
          z.1 ((⟨g * h, N.mul_mem ng nh⟩ : N), (⟨k, nk⟩ : N)) +
            z.1 ((⟨g, ng⟩ : N), (⟨h, nh⟩ : N)) := by
      simpa using hz_coc
    change defect (g, (h, k)) = 0
    change g • c (h, k) - c (g * h, k) + c (g, h * k) - c (g, h) = 0
    rw [hcgh, hchk, hcghk, hcgh']
    change g • z.1 (⟨h, nh⟩, ⟨k, nk⟩) -
        z.1 (⟨g * h, N.mul_mem ng nh⟩, ⟨k, nk⟩) +
        z.1 (⟨g, ng⟩, ⟨h * k, N.mul_mem nh nk⟩) -
        z.1 (⟨g, ng⟩, ⟨h, nh⟩) = 0
    rw [haction ⟨g, ng⟩]
    calc
      _ = ((⟨g, ng⟩ : N) • z.1 (⟨h, nh⟩, ⟨k, nk⟩) +
            z.1 (⟨g, ng⟩, ⟨h * k, N.mul_mem nh nk⟩)) -
          (z.1 (⟨g * h, N.mul_mem ng nh⟩, ⟨k, nk⟩) +
            z.1 (⟨g, ng⟩, ⟨h, nh⟩)) := by abel
      _ = 0 := by rw [hz_coc', sub_self]
  have hNcompact : IsCompact (N : Set G) :=
    (show IsClosed (N : Set G) from inferInstance).isCompact
  have hNNcompact : IsCompact ((N : Set G) ×ˢ (N : Set G)) := hNcompact.prod hNcompact
  obtain ⟨O₁, O₂₃, hO₁open, hO₂₃open, hNO₁, hNNO₂₃, hprodZ⟩ :=
    generalized_tube_lemma hNcompact hNNcompact hZopen hNZ
  obtain ⟨O₂, O₃, hO₂open, hO₃open, hNO₂, hNO₃, hprodO₂₃⟩ :=
    generalized_tube_lemma hNcompact hNcompact hO₂₃open hNNO₂₃
  let O : Set G := O₁ ∩ O₂ ∩ O₃
  have hOopen : IsOpen O := (hO₁open.inter hO₂open).inter hO₃open
  have hNO : (N : Set G) ⊆ O := fun n hn ↦ ⟨⟨hNO₁ hn, hNO₂ hn⟩, hNO₃ hn⟩
  have hOOO : O ×ˢ (O ×ˢ O) ⊆ Z := by
    rintro ⟨g, ⟨h, k⟩⟩ ⟨hg, ⟨hh, hk⟩⟩
    exact hprodZ ⟨hg.1.1, hprodO₂₃ ⟨hh.1.2, hk.2⟩⟩
  let S : Set (G × G) := (fun p : G × G ↦ p.1 * p.2) ⁻¹' O
  have hSopen : IsOpen S := hOopen.preimage (continuous_fst.mul continuous_snd)
  have hNOneS : (N : Set G) ×ˢ ({1} : Set G) ⊆ S := by
    rintro ⟨n, _⟩ ⟨hn, rfl⟩
    simpa [S] using hNO hn
  obtain ⟨U, V, hUopen, hVopen, hNU, hOneV, hUV⟩ :=
    generalized_tube_lemma hNcompact isCompact_singleton hSopen hNOneS
  obtain ⟨L, hL⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    hVopen (hOneV rfl)
  let H : Subgroup G := N ⊔ (L : Subgroup G)
  have hNH : N ≤ H := le_sup_left
  have hHopen : IsOpen (H : Set G) :=
    Subgroup.isOpen_mono (show (L : Subgroup G) ≤ H from le_sup_right) L.isOpen
  have hHO : (H : Set G) ⊆ O := by
    intro x hx
    have hmul : (H : Set G) =
        (N : Set G) * ((L : Subgroup G) : Set G) := by
      exact Subgroup.normal_mul N (L : Subgroup G)
    have hx' : x ∈ (N : Set G) * ((L : Subgroup G) : Set G) := by
      rw [← hmul]
      exact hx
    rcases Set.mem_mul.mp hx' with ⟨n, hn, l, hl, hnl⟩
    rw [← hnl]
    have hlV : l ∈ V := hL hl
    have hpair : (n, l) ∈ S := hUV (a := (n, l)) ⟨hNU hn, hlV⟩
    simpa [S] using hpair
  let w : Z2 H M := ⟨(fun p ↦ c (p.1.1, p.2.1)), by
    refine AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact hc.comp ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
    · rw [AddMonoidHom.mem_ker]
      funext t
      have hd : defect (t.1.1, (t.2.1.1, t.2.2.1)) = 0 :=
        hOOO ⟨hHO t.1.property, hHO t.2.1.property, hHO t.2.2.property⟩
      exact hd
    ⟩
  refine ⟨H, hNH, hHopen, w, ?_⟩
  congr 1
  apply Subtype.ext
  funext p
  let pp : NN := ⟨(p.1.1, p.2.1), ⟨p.1.2, p.2.2⟩⟩
  exact hcN pp

end ClosedSubgroupContinuity

section OpenLocalLayers

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- Every open subgroup of `G_ℚ₂` has scalar degree-two cohomology generated by cups.

This is not a new norm-residue input.  B6 makes the scalar cup pairing nondegenerate and gives
`#H² = 2`; B7 gives `#H¹ ≥ 4`, so there is a nonzero cup, which is necessarily the unique
nonzero degree-two class. -/
theorem openSubgroupAbsGalQ2_scalarH2CupGenerated
    (W : Subgroup AbsGalQ2) (hW : IsOpen (W : Set AbsGalQ2)) :
    ScalarH2GeneratedByCupProducts (G := W)
      (fun g m ↦ smul_zmodTwo g m) := by
  letI : Finite (AbsGalQ2 ⧸ W) := finite_quotient_of_isOpen W hW
  letI : W.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _ inferInstance
  let D : TateDualityG W 2 :=
    tateDualityAt W 2 (subgroup_isLocalDualizingGroup 2 W hW)
  let hE : LocalEulerChar W W.index := fun M _ _ _ _ _ _ ↦
    localEulerCharacteristic_open W hW M
  have htriv : ∀ (g : W) (m : ZMod 2), g • m = m := fun g m ↦ smul_zmodTwo g m
  have hH0 : Nat.card (H0 W (ZMod 2)) = 2 := by
    rw [show H0 W (ZMod 2) = ⊤ from eq_top_iff.mpr (fun m _ g ↦ htriv g m),
      Nat.card_congr (AddSubgroup.topEquiv (G := ZMod 2)).toEquiv, Nat.card_zmod]
  have hH2 : Nat.card (H2 W (ZMod 2)) = 2 := card_H2_zmod2_eq_twoG D htriv
  letI : Finite (H1 W (ZMod 2)) := (hE (ZMod 2)).2.1
  have hH1card := (hE (ZMod 2)).2.2.2
  rw [hH0, hH2, Nat.card_zmod,
    show padicValNat 2 2 = 1 from padicValNat.self one_lt_two, mul_one] at hH1card
  have hH1large : 1 < Nat.card (H1 W (ZMod 2)) := by
    rw [hH1card]
    have hp : 0 < 2 ^ W.index := by positivity
    omega
  exact scalarH2GeneratedByCupProducts_of_tateDuality D htriv
    (Finite.one_lt_card_iff_nontrivial.mp hH1large)

/-- B6 and B7 give scalar cup-generation on every group carrying a local-field realization. -/
theorem localFieldRealization_scalarH2CupGenerated
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    [DistribMulAction G (MuN 2)] [ContinuousSMul G (MuN 2)]
    {d : ℕ} (R : LSquare.LocalFieldRealization G d) :
    ScalarH2GeneratedByCupProducts (G := G)
      (fun g m ↦ smul_zmodTwo g m) := by
  let D : TateDualityG G 2 := R.tateDualityG
  let hE : LocalEulerChar G d := R.localEulerChar
  have htriv : ∀ (g : G) (m : ZMod 2), g • m = m := fun g m ↦ smul_zmodTwo g m
  have hH0 : Nat.card (H0 G (ZMod 2)) = 2 := by
    rw [show H0 G (ZMod 2) = ⊤ from eq_top_iff.mpr (fun m _ g ↦ htriv g m),
      Nat.card_congr (AddSubgroup.topEquiv (G := ZMod 2)).toEquiv, Nat.card_zmod]
  have hH2 : Nat.card (H2 G (ZMod 2)) = 2 := card_H2_zmod2_eq_twoG D htriv
  letI : Finite (H1 G (ZMod 2)) := (hE (ZMod 2)).2.1
  have hH1card := (hE (ZMod 2)).2.2.2
  rw [hH0, hH2, Nat.card_zmod,
    show padicValNat 2 2 = 1 from padicValNat.self one_lt_two, mul_one] at hH1card
  have hH1large : 1 < Nat.card (H1 G (ZMod 2)) := by
    rw [hH1card]
    have hp : 0 < 2 ^ d := by positivity
    omega
  exact scalarH2GeneratedByCupProducts_of_tateDuality D htriv
    (Finite.one_lt_card_iff_nontrivial.mp hH1large)

/-- An open subgroup of `G_K` is itself realized by its open ambient image in `G_ℚ₂`. -/
def openSubgroupGalK_localFieldRealization
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (H : Subgroup (GalK K)) (hH : IsOpen (H : Set (GalK K))) :
    LSquare.LocalFieldRealization H
      ((H.map (GalKsub K).subtype).index) where
  subgroup := H.map (GalKsub K).subtype
  isOpen_subgroup := by
    change IsOpen (((fun x : GalK K ↦ (x : AbsGalQ2)) '' (H : Set (GalK K))))
    exact (isOpen_fixingSubgroup K).isOpenMap_subtype_val _ hH
  equiv := anchorEquiv (GalKsub K) H
  index_eq := rfl

/-- Hence every open subgroup of `G_K` has scalar degree-two cup-generation. -/
theorem openSubgroupGalK_scalarH2CupGenerated
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    (H : Subgroup (GalK K)) (hH : IsOpen (H : Set (GalK K))) :
    ScalarH2GeneratedByCupProducts (G := H)
      (fun g m ↦ smul_zmodTwo g m) :=
  localFieldRealization_scalarH2CupGenerated
    (openSubgroupGalK_localFieldRealization H hH)

end OpenLocalLayers

section CupRestriction

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
  [DistribMulAction H (ZMod 2)] [ContinuousSMul H (ZMod 2)]

/-- Pullback along a continuous group map commutes with the scalar cup product. -/
theorem H2comap_trivialCupPairing
    (f : ContinuousMonoidHom G H)
    (htrivG : ∀ (g : G) (m : ZMod 2), g • m = m)
    (htrivH : ∀ (h : H) (m : ZMod 2), h • m = m)
    (hcompat : ∀ (g : G) (m : ZMod 2), f g • m = g • m)
    (x y : H1 H (ZMod 2)) :
    H2comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat
        (trivialCupPairing 2 H htrivH x y) =
      trivialCupPairing 2 G htrivG
        (H1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat x)
        (H1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat y) := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := H) (M := ZMod 2) y
  -- The pairing-equivariance witnesses behind `trivialCupPairing` on each side.
  have hμG : ∀ (g : G) (m n : ZMod 2),
      (AddMonoidHom.mul (g • m)) (g • n) = g • (AddMonoidHom.mul m) n :=
    fun g m n ↦ by rw [htrivG, htrivG, htrivG]
  have hμH : ∀ (h : H) (m n : ZMod 2),
      (AddMonoidHom.mul (h • m)) (h • n) = h • (AddMonoidHom.mul m) n :=
    fun h m n ↦ by rw [htrivH, htrivH, htrivH]
  -- Both sides are `H2mk` of an explicit cocycle: `cup11_mk_mk` and the `Hicomap`-on-classes
  -- computations are all definitional.
  show H2mk G (ZMod 2)
      (Z2comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat
        ⟨cup11Fun AddMonoidHom.mul a.1 b.1, cup11_mem_Z2 AddMonoidHom.mul hμH a b⟩) =
    H2mk G (ZMod 2)
      ⟨cup11Fun AddMonoidHom.mul
          (Z1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat a).1
          (Z1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat b).1,
        cup11_mem_Z2 AddMonoidHom.mul hμG
          (Z1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat a)
          (Z1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat b)⟩
  refine congrArg (H2mk G (ZMod 2)) (Subtype.ext (funext fun p ↦ ?_))
  show a.1 (f p.1) * (f p.1 • b.1 (f p.2)) = a.1 (f p.1) * (p.1 • b.1 (f p.2))
  rw [hcompat]

/-- A cup-generated class restricts to zero whenever all degree-one classes on the source of
the restriction vanish. -/
theorem H2comap_eq_zero_of_cupGenerated_of_h1Vanishes
    (f : ContinuousMonoidHom G H)
    (htrivG : ∀ (g : G) (m : ZMod 2), g • m = m)
    (htrivH : ∀ (h : H) (m : ZMod 2), h • m = m)
    (hcompat : ∀ (g : G) (m : ZMod 2), f g • m = g • m)
    (hH1 : ∀ x : H1 G (ZMod 2), x = 0)
    (hgen : ScalarH2GeneratedByCupProducts (G := H) htrivH)
    (z : H2 H (ZMod 2)) :
    H2comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat z = 0 := by
  obtain ⟨n, x, y, hz⟩ := hgen z
  rw [hz, map_sum]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [H2comap_trivialCupPairing f htrivG htrivH hcompat,
    hH1 (H1comap f (AddMonoidHom.id (ZMod 2)) continuous_id hcompat (x i)), map_zero]
  rfl

end CupRestriction

section GalKConclusion

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- Scalar `H²` of the maximal-pro-two kernel of `G_K` vanishes.

Every intrinsic cocycle extends to an open subgroup `H ≤ G_K`.  At `H`, B6 and B7 express
its class as a sum of cups; restriction kills every cup because intrinsic scalar `H¹` of the
maximal-pro-two kernel is already known to vanish. -/
theorem galKMaxProTwoKernelScalarH2Vanishes :
    MaxProTwoKernelScalarH2Vanishes (G := GalK K) := by
  let N : Subgroup (GalK K) := proPKernel 2 (GalK K)
  letI : DistribMulAction N (ZMod 2) := trivialAddAction (M := ZMod 2) N
  letI : ContinuousSMul N (ZMod 2) :=
    continuousSMul_trivialAddAction (M := ZMod 2) N
  intro x
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := N) (M := ZMod 2) x
  have haction : ∀ (n : N) (m : ZMod 2), n.1 • m = n • m := by
    intro n m
    rw [htriv_galK K]
    rfl
  letI : IsClosed (N : Set (GalK K)) := proPKernel_isClosed 2 (GalK K)
  obtain ⟨H, hNH, hHopen, w, hw⟩ :=
    exists_open_overgroup_cocycle_extension N haction z
  have htrivN : ∀ (n : N) (m : ZMod 2), n • m = m := fun _ _ ↦ rfl
  have htrivH : ∀ (h : H) (m : ZMod 2), h • m = m := fun h m ↦ smul_zmodTwo h m
  have hcompat : ∀ (n : N) (m : ZMod 2),
      continuousSubgroupInclusion hNH n • m = n • m := by
    intro n m
    rw [htrivH, htrivN]
  have hH1 : ∀ a : H1 N (ZMod 2), a = 0 := by
    intro a
    obtain ⟨c, rfl⟩ := H1mk_surjective (G := N) (M := ZMod 2) a
    letI : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
      trivialAddAction (M := ZMod 2) (maxProPQuotient 2 (GalK K))
    letI : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
      continuousSMul_trivialAddAction (M := ZMod 2) (maxProPQuotient 2 (GalK K))
    have hqcompat : ∀ (g : GalK K) (m : ZMod 2),
        maxProPMk 2 (GalK K) g • m = g • m := by
      intro g m
      rw [show maxProPMk 2 (GalK K) g • m = m from rfl, htriv_galK K]
    have hc0 := congrArg (H1mk N (ZMod 2))
      (maxProTwoKernel_intrinsicH1CocyclesVanish
        (G := GalK K) (M := ZMod 2) (by decide) hqcompat c)
    exact hc0.trans (map_zero (H1mk N (ZMod 2)))
  have hzero := H2comap_eq_zero_of_cupGenerated_of_h1Vanishes
    (continuousSubgroupInclusion hNH) htrivN htrivH hcompat hH1
    (openSubgroupGalK_scalarH2CupGenerated H hHopen) (H2mk H (ZMod 2) w)
  change H2mk N (ZMod 2)
    (Z2comap (continuousSubgroupInclusion hNH)
      (AddMonoidHom.id (ZMod 2)) continuous_id hcompat w) = 0 at hzero
  exact hw.symm.trans hzero

/-- The scalar theorem supplies the uniform finite-elementary kernel boundary. -/
theorem galKFiniteElementaryMaxProTwoKernelH2VanishesSupply :
    FiniteElementaryMaxProTwoKernelH2VanishesSupply (G := GalK K) :=
  finiteElementaryMaxProTwoKernelH2VanishesSupply_of_scalar
    (galKMaxProTwoKernelScalarH2Vanishes (K := K))

/-- B6/B7 plus cochain continuity prove the previously residual source-surjectivity theorem. -/
theorem galKMaxProTwoFiniteElementaryH2InflationSurjective :
    FiniteElementaryH2InflationSurjective (maxProPMk 2 (GalK K)) :=
  finiteElementaryH2InflationSurjective_of_kernelH2Vanishes
    (galKFiniteElementaryMaxProTwoKernelH2VanishesSupply (K := K))

end GalKConclusion

end

end GQ2.Dyadic
