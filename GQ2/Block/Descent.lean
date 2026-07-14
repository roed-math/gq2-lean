import GQ2.SectionSeven
import Mathlib.GroupTheory.IsPerfect

namespace GQ2

open SectionSeven

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

/-- **Linchpin of the block descent (P-17d1)**: the layer top `P` is abelian mod the scalar
socle `S` — `⁅P, P⁆ ≤ S`.  `⁅P,P⁆ ⊔ S` is `Y`-normal between `S` and `P`, so by the chief
condition it is `S` or `P`; if `P`, then `P̄ = P/S` would be a **perfect** nontrivial finite
2-group, impossible (2-groups are nilpotent, `IsPerfect.not_isNilpotent`). -/
theorem commutator_P_le_S (B : MinimalBlock L) : ⁅B.P, B.P⁆ ≤ B.S := by
  haveI := B.hP
  haveI := B.hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcommN : (⁅B.P, B.P⁆).Normal := Subgroup.commutator_normal B.P B.P
  have hcommleP : ⁅B.P, B.P⁆ ≤ B.P := Subgroup.commutator_le_right B.P B.P
  set D := ⁅B.P, B.P⁆ ⊔ B.S with hD
  haveI hDN : D.Normal := Subgroup.sup_normal _ _
  rcases B.chief D hDN le_sup_right (sup_le hcommleP B.hSP.le) with hDS | hDP
  · exact le_sup_left.trans hDS.le
  · exfalso
    set f := QuotientGroup.mk' B.S with hf
    set Pbar := B.P.map f with hPbar
    -- perfect: ⁅P̄, P̄⁆ = P̄
    have hSmap : B.S.map f = ⊥ := by
      rw [hf, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hperf : ⁅Pbar, Pbar⁆ = Pbar := by
      have hmap := congrArg (Subgroup.map f) hDP
      rwa [hD, Subgroup.map_sup, Subgroup.map_commutator, hSmap, sup_bot_eq] at hmap
    haveI : Group.IsPerfect Pbar := Subgroup.isPerfect_iff.mpr hperf
    -- P̄ is a nontrivial finite 2-group
    haveI : Nontrivial Pbar := by
      obtain ⟨p₀, hp₀P, hp₀S⟩ := SetLike.exists_of_lt B.hSP
      refine ⟨⟨f p₀, Subgroup.mem_map_of_mem f hp₀P⟩, 1, fun heq => hp₀S ?_⟩
      have hval : f p₀ = 1 := congrArg Subtype.val heq
      rwa [hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hval
    haveI hP2 : IsPGroup 2 B.P := by
      intro g
      obtain ⟨n, hn⟩ := B.h2L ⟨g.1, B.hPL g.2⟩
      exact ⟨n, by ext; simpa using congrArg Subtype.val hn⟩
    haveI : IsPGroup 2 Pbar := hP2.map f
    haveI : Group.IsNilpotent Pbar := IsPGroup.isNilpotent ‹IsPGroup 2 Pbar›
    exact absurd ‹Group.IsNilpotent Pbar› (Group.IsPerfect.not_isNilpotent (G := Pbar))

/-- `V = P/S` is **abelian** (`CommGroup`), from `⁅P,P⁆ ≤ S` (`commutator_P_le_S`). -/
@[reducible] noncomputable def blockPS_commGroup (B : MinimalBlock L) :
    CommGroup (↥B.P ⧸ B.S.subgroupOf B.P) :=
  haveI := B.hS
  haveI := B.hP
  { (inferInstance : Group (↥B.P ⧸ B.S.subgroupOf B.P)) with
    mul_comm := by
      intro x y
      induction x using QuotientGroup.induction_on with | _ a =>
      induction y using QuotientGroup.induction_on with | _ b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hc : (((a * b)⁻¹ * (b * a) : ↥B.P) : Y)
          = (b : Y)⁻¹ * (a : Y)⁻¹ * ((b : Y)⁻¹)⁻¹ * ((a : Y)⁻¹)⁻¹ := by push_cast; group
      rw [hc]
      exact commutator_P_le_S B
        (Subgroup.commutator_mem_commutator (inv_mem b.2) (inv_mem a.2)) }

/-- The `Y`-conjugation action on `Additive(P/S)` as a `DistribMulAction` (the conjugation
`blockAction` is by group automorphisms — `QuotientGroup.map` of `conjHom` — so it distributes
over `+`). -/
@[reducible] noncomputable def blockActVY (B : MinimalBlock L) :
    letI := blockPS_commGroup B
    DistribMulAction Y (Additive (↥B.P ⧸ B.S.subgroupOf B.P)) :=
  haveI := B.hS
  haveI := B.hP
  letI := blockPS_commGroup B
  { blockAction B.S B.P B.hS B.hP with
    smul_zero := fun y =>
      (QuotientGroup.map (B.S.subgroupOf B.P) (B.S.subgroupOf B.P) (conjHom B.P B.hP y)
        (conjHom_compat B.S B.P B.hS B.hP y)).map_one
    smul_add := fun y _ _ =>
      (QuotientGroup.map (B.S.subgroupOf B.P) (B.S.subgroupOf B.P) (conjHom B.P B.hP y)
        (conjHom_compat B.S B.P B.hS B.hP y)).map_mul _ _ }

/-- **`K` acts trivially on `V = P/S`** (`[K,P] ≤ ⁅P,P⁆ ≤ S`): the key fact that lets the
`Y`-conjugation action descend to `Y/K`. -/
theorem blockK_smul_eq (B : MinimalBlock L) {k : Y} (hk : k ∈ B.K)
    (q : ↥B.P ⧸ B.S.subgroupOf B.P) :
    letI := blockAction B.S B.P B.hS B.hP
    k • q = q := by
  haveI := B.hS
  haveI := B.hP
  haveI hn : (B.S.subgroupOf B.P).Normal := B.hS.subgroupOf B.P
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
  rw [blockAction_smul_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hval : (((conjHom B.P B.hP k p)⁻¹ * p : ↥B.P) : Y)
      = k * (p : Y)⁻¹ * k⁻¹ * ((p : Y)⁻¹)⁻¹ := by
    show (k * (p : Y) * k⁻¹)⁻¹ * (p : Y) = k * (p : Y)⁻¹ * k⁻¹ * ((p : Y)⁻¹)⁻¹
    group
  rw [hval]
  exact commutator_P_le_S B (Subgroup.commutator_mem_commutator (B.hKP hk) (inv_mem p.2))

/-- **The descended `Y/K`-action on `V = P/S`** — `actV`.  The `Y`-conjugation action
(`blockActVY`) descends because `K` acts trivially (`blockK_smul_eq`). -/
@[reducible] noncomputable def blockActV (B : MinimalBlock L) :
    haveI := B.hK
    letI := blockPS_commGroup B
    DistribMulAction (Y ⧸ B.K) (Additive (↥B.P ⧸ B.S.subgroupOf B.P)) :=
  haveI := B.hS
  haveI := B.hP
  haveI := B.hK
  letI := blockPS_commGroup B
  letI := blockActVY B
  { smul := fun yb v => Quotient.liftOn' yb (fun y => (y : Y) • v) (by
      intro y₁ y₂ h
      have hmem : y₁⁻¹ * y₂ ∈ B.K := QuotientGroup.leftRel_apply.mp h
      have htriv : (y₁⁻¹ * y₂) • v = v := blockK_smul_eq B hmem v
      calc (y₁ : Y) • v = y₁ • ((y₁⁻¹ * y₂) • v) := by rw [htriv]
        _ = (y₁ * (y₁⁻¹ * y₂)) • v := (mul_smul _ _ _).symm
        _ = y₂ • v := by rw [mul_inv_cancel_left])
    one_smul := fun v => one_smul Y v
    mul_smul := fun yb1 yb2 v => by
      induction yb1 using QuotientGroup.induction_on with | _ y₁ =>
      induction yb2 using QuotientGroup.induction_on with | _ y₂ =>
      exact mul_smul y₁ y₂ v
    smul_zero := fun yb => by
      induction yb using QuotientGroup.induction_on with | _ y =>
      exact smul_zero y
    smul_add := fun yb a b => by
      induction yb using QuotientGroup.induction_on with | _ y =>
      exact smul_add y a b }

/-! ## The descent surjection `M_B ↠ V = P/S` (P-17d1, piece ⑥) -/

section Descend

variable (B : MinimalBlock L) [(B.frattiniK).Normal] [(B.S.subgroupOf B.P).Normal] [(B.K).Normal]

/-- `M_B` = image of `K` in `Y/R`. -/
noncomputable def blockMB : Subgroup (Y ⧸ B.frattiniK) := B.K.map (QuotientGroup.mk' B.frattiniK)

/-- The corestricted surjection `κ' : K ↠ M_B`, `k ↦ [k]_R`. -/
noncomputable def blockKappa : ↥B.K →* ↥(blockMB B) :=
  ((QuotientGroup.mk' B.frattiniK).comp B.K.subtype).codRestrict (blockMB B)
    (fun k => Subgroup.mem_map_of_mem _ k.2)

omit [Finite Y] [(B.S.subgroupOf B.P).Normal] [B.K.Normal] in
theorem blockKappa_coe (k : ↥B.K) : ((blockKappa B k : ↥(blockMB B)) : Y ⧸ B.frattiniK)
    = QuotientGroup.mk' B.frattiniK (k : Y) := rfl

omit [Finite Y] [(B.S.subgroupOf B.P).Normal] [B.K.Normal] in
theorem blockKappa_surjective : Function.Surjective (blockKappa B) := by
  rintro ⟨m, hm⟩
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
  exact ⟨⟨k, hk⟩, Subtype.ext rfl⟩

/-- `α : K →* P/S`, `k ↦ [k]_S` (via `K ≤ P`). -/
noncomputable def blockAlpha : ↥B.K →* (↥B.P ⧸ B.S.subgroupOf B.P) :=
  (QuotientGroup.mk' (B.S.subgroupOf B.P)).comp (Subgroup.inclusion B.hKP)

omit [Finite Y] [B.frattiniK.Normal] [B.K.Normal] in
theorem blockAlpha_apply (k : ↥B.K) :
    blockAlpha B k = QuotientGroup.mk (Subgroup.inclusion B.hKP k) := rfl

omit [Finite Y] [B.frattiniK.Normal] [B.K.Normal] in
theorem blockAlpha_eq_one_iff (k : ↥B.K) :
    blockAlpha B k = 1 ↔ (k : Y) ∈ B.S := by
  rw [blockAlpha, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]

omit [B.K.Normal] in
/-- `ker κ' ≤ ker α`: if `[k]_R = 1` then `k ∈ R ≤ S`, so `[k]_S = 1`. -/
theorem blockKappa_ker_le_alpha :
    (blockKappa B).ker ≤ (blockAlpha B).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker, blockAlpha_eq_one_iff]
  have hxR : (x : Y) ∈ B.frattiniK := by
    have hval : QuotientGroup.mk' B.frattiniK (x : Y) = 1 := by rw [← blockKappa_coe, hx]; rfl
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hval
  exact ((lemma_7_1_head B).trans inf_le_right) hxR

/-- The descent surjection `M_B ↠ P/S`. -/
noncomputable def blockDescend : ↥(blockMB B) →* (↥B.P ⧸ B.S.subgroupOf B.P) :=
  (QuotientGroup.lift (blockKappa B).ker (blockAlpha B)
    (fun _ hx => MonoidHom.mem_ker.mp (blockKappa_ker_le_alpha B hx))).comp
    (QuotientGroup.quotientKerEquivOfSurjective (blockKappa B)
      (blockKappa_surjective B)).symm.toMonoidHom

omit [B.K.Normal] in
/-- **The characterizing identity**: `descend ∘ κ' = α`. -/
theorem blockDescend_kappa (k : ↥B.K) :
    blockDescend B (blockKappa B k) = blockAlpha B k := by
  have hmk : blockKappa B k
      = QuotientGroup.quotientKerEquivOfSurjective (blockKappa B) (blockKappa_surjective B)
        (QuotientGroup.mk k) := rfl
  rw [blockDescend, MonoidHom.comp_apply, hmk, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, QuotientGroup.lift_mk]

omit [B.K.Normal] in
/-- **`descend` is surjective** onto `P/S`: every `[p]_S` is hit, because `KS = P` (`B.gen`)
lets us replace `p` by a `K`-representative. -/
theorem blockDescend_surjective : Function.Surjective (blockDescend B) := by
  haveI := B.hS
  intro v
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective v
  have hp : (p : Y) ∈ (B.K : Set Y) * (B.S : Set Y) := by
    rw [← Subgroup.mul_normal B.K B.S, B.gen]; exact p.2
  obtain ⟨a, ha, b, hb, hab⟩ := hp
  refine ⟨blockKappa B ⟨a, ha⟩, ?_⟩
  rw [blockDescend_kappa, blockAlpha, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_inclusion]
  have hb' : a⁻¹ * (p : Y) = b := by rw [← hab]; group
  rw [show ((⟨a, ha⟩ : ↥B.K) : Y) = a from rfl, hb']
  exact hb

/-- `T_B = image of `K ⊓ S ⊔ R` in `Y/R` (the `BlockFrameImpl` definition). -/
noncomputable def blockTBsub : Subgroup (Y ⧸ B.frattiniK) :=
  ((B.K ⊓ B.S) ⊔ B.frattiniK).map (QuotientGroup.mk' B.frattiniK)

omit [B.K.Normal] in
/-- **`ker descend = T_B`**: `descend m = 1 ↔ m ∈ T_B`.  Both sides reduce to `k ∈ S` for a
`K`-representative `k` of `m`, using `R ≤ K ⊓ S` (`lemma_7_1_head`) to collapse `T_B` to the
image of `K ⊓ S`. -/
theorem blockDescend_ker (m : ↥(blockMB B)) :
    blockDescend B m = 1 ↔ (m : Y ⧸ B.frattiniK) ∈ blockTBsub B := by
  obtain ⟨k, rfl⟩ := blockKappa_surjective B m
  rw [blockDescend_kappa, blockAlpha_eq_one_iff, blockKappa_coe, blockTBsub,
    sup_eq_left.mpr (lemma_7_1_head B)]
  constructor
  · intro hkS
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mpr ⟨k.2, hkS⟩)
  · intro hmem
    rw [← Subgroup.mem_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
      sup_eq_left.mpr (lemma_7_1_head B)] at hmem
    exact (Subgroup.mem_inf.mp hmem).2

/-- The `C`-stage projection `π_{BC} : Y/R ↠ Y/K` (the `BlockFrameImpl` definition). -/
noncomputable def blockPiBC : (Y ⧸ B.frattiniK) →* (Y ⧸ B.K) :=
  QuotientGroup.map B.frattiniK B.K (MonoidHom.id Y)
    (by rw [Subgroup.comap_id]; exact frattiniLike_le B.K)

omit [Finite Y] [(B.S.subgroupOf B.P).Normal] in
theorem blockPiBC_mk' (y : Y) :
    blockPiBC B (QuotientGroup.mk' B.frattiniK y) = QuotientGroup.mk' B.K y :=
  QuotientGroup.map_mk' _ _ _ _ _

omit [B.frattiniK.Normal] [B.K.Normal] in
/-- `Y/K`-action on `mk' K y` reduces to the `Y`-action of `y`. -/
theorem blockActV_mk' (y : Y) (v : Additive (↥B.P ⧸ B.S.subgroupOf B.P)) :
    haveI := B.hK
    letI := blockActV B; letI := blockActVY B
    (QuotientGroup.mk' B.K y) • v = y • v := rfl

omit [B.frattiniK.Normal] [B.K.Normal] in
/-- The `Y`-action of `y` on `⟦p⟧` computes as `⟦y p y⁻¹⟧`. -/
theorem blockActVY_mk (y : Y) (p : ↥B.P) :
    letI := blockActVY B
    (y • Additive.ofMul (QuotientGroup.mk p) : Additive (↥B.P ⧸ B.S.subgroupOf B.P))
      = Additive.ofMul (QuotientGroup.mk (conjHom B.P B.hP y p)) :=
  congrArg Additive.ofMul (blockAction_smul_mk B.S B.P B.hS B.hP y p)

omit [B.K.Normal] in
/-- **`descend` intertwines `B`-conjugation with the `C`-stage action** (`descend_conj`): for the
`Y/K`-action on `V = P/S`, `descend(b·m·b⁻¹) = π_{BC}(b) • descend(m)`.  Proved by lifting `m` and
`b` to `K`- and `Y`-representatives and reducing both sides to `⟦y k y⁻¹⟧_S`. -/
theorem blockDescend_conj (bb : Y ⧸ B.frattiniK) (m : ↥(blockMB B))
    (hm : bb * (m : Y ⧸ B.frattiniK) * bb⁻¹ ∈ blockMB B) :
    haveI := B.hK
    letI := blockActV B
    blockPiBC B bb • Additive.ofMul (blockDescend B m)
      = Additive.ofMul (blockDescend B ⟨bb * (m : Y ⧸ B.frattiniK) * bb⁻¹, hm⟩) := by
  haveI := B.hK
  letI := blockActV B
  obtain ⟨k, rfl⟩ := blockKappa_surjective B m
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective B.frattiniK bb
  have hyk : y * (k : Y) * y⁻¹ ∈ B.K := B.hK.conj_mem (k : Y) k.2 y
  have hconjeq : (⟨QuotientGroup.mk' B.frattiniK y * (blockKappa B k : Y ⧸ B.frattiniK)
      * (QuotientGroup.mk' B.frattiniK y)⁻¹, hm⟩ : ↥(blockMB B))
      = blockKappa B ⟨y * (k : Y) * y⁻¹, hyk⟩ := by
    apply Subtype.ext
    show QuotientGroup.mk' B.frattiniK y * ((blockKappa B k : ↥(blockMB B)) : Y ⧸ B.frattiniK)
        * (QuotientGroup.mk' B.frattiniK y)⁻¹
      = ((blockKappa B ⟨y * (k : Y) * y⁻¹, hyk⟩ : ↥(blockMB B)) : Y ⧸ B.frattiniK)
    rw [blockKappa_coe, blockKappa_coe, ← map_inv, ← map_mul, ← map_mul]
  rw [hconjeq, blockDescend_kappa, blockDescend_kappa, blockPiBC_mk', blockActV_mk',
    blockAlpha_apply, blockAlpha_apply, blockActVY_mk]
  congr 2

end Descend

end GQ2
