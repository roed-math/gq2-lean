import Mathlib

/-!
# Block-module infrastructure for §7  (ticket P-15g)

Reusable finite-group-theory layer for `GQ2.SectionSeven.lemma_7_2` (and, later, §§8–9's
scalar-regime arguments).  Block-agnostic: everything is phrased for subgroups `S ≤ P ≤ Y`
with the chief-factor / nontriviality hypotheses as explicit arguments, so `MinimalBlock`
(in `SectionSeven.lean`) applies it without a dependency cycle.

Contents:

* `comm_bot_of_scalarChain` — a coprime odd group acting on a `Y`-central series is trivial
  (`⁅Ñ, c n⁆ = ⊥`).  Mathlib lacks the coprime-action commutator theory; this is the special
  case §7 needs, proved by central-series induction.  (Relocated from `SectionSeven.lean`,
  made public.)
* `blockAction` — the `Y`-conjugation `MulAction` on `V = P/S = ↥P ⧸ (S.subgroupOf P)`.
* `exists_odd_moving_general` — since `V` is a nontrivial simple `𝔽₂[Y]`-module (chief factor),
  the image `Ȳ = Y/C_Y(V)` is not a 2-group (a 2-group fixes a nonzero vector, contradicting
  the chief condition), so `Y` contains an **odd-order** element moving `V`.  This replaces the
  paper's odd Hall lift — no Hall's theorem / Schur–Zassenhaus needed.
-/

namespace GQ2

open scoped Pointwise

/-! ## Coprime odd action on a central series -/

theorem comm_bot_of_scalarChain :
    ∀ (n : ℕ) {G : Type} [Group G] [Finite G] (Nt : Subgroup G) (c : ℕ → Subgroup G),
      c 0 = ⊥ → (∀ i, c i ≤ c (i + 1)) →
      (∀ i, ∀ g : G, ∀ x ∈ c (i + 1), g * x * g⁻¹ * x⁻¹ ∈ c i) →
      Nat.Coprime (Nat.card Nt) (Nat.card (c n)) →
      ⁅Nt, c n⁆ = ⊥ := by
  intro n
  induction n with
  | zero =>
    intro G _ _ Nt c hc0 _ _ _
    rw [hc0]
    exact Subgroup.commutator_bot_right Nt
  | succ n ih =>
    intro G _ _ Nt c hc0 hmono hcomm hcop
    -- the bottom layer is central: `⁅g, x⁆ = 1` for `x ∈ c 1`
    have hc1triv : ∀ x ∈ c 1, ∀ g : G, g * x * g⁻¹ * x⁻¹ = 1 := by
      intro x hx g
      have h := hcomm 0 g x hx
      rwa [hc0, Subgroup.mem_bot] at h
    have hZcomm : ∀ x ∈ c 1, ∀ g : G, g * x = x * g := by
      intro x hx g
      have h2 : g * x * g⁻¹ = x := mul_inv_eq_one.mp (hc1triv x hx g)
      calc g * x = g * x * g⁻¹ * g := by group
        _ = x * g := by rw [h2]
    haveI hc1n : (c 1).Normal :=
      ⟨fun x hx g => by
        have he : g * x * g⁻¹ = x := mul_inv_eq_one.mp (hc1triv x hx g)
        rw [he]; exact hx⟩
    set φ : G →* G ⧸ c 1 := QuotientGroup.mk' (c 1) with hφ
    have hφsurj : Function.Surjective φ := QuotientGroup.mk'_surjective (c 1)
    -- push the chain to `G ⧸ c 1`
    have hd0 : (c 1).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk']
    have hdcomm : ∀ i, ∀ gq : G ⧸ c 1, ∀ xq ∈ (c (i + 1 + 1)).map φ,
        gq * xq * gq⁻¹ * xq⁻¹ ∈ (c (i + 1)).map φ := by
      intro i gq xq hxq
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hxq
      obtain ⟨g, rfl⟩ := hφsurj gq
      have hrw : φ g * φ x * (φ g)⁻¹ * (φ x)⁻¹ = φ (g * x * g⁻¹ * x⁻¹) := by
        simp only [map_mul, map_inv]
      rw [hrw]
      exact Subgroup.mem_map_of_mem φ (hcomm (i + 1) g x hx)
    have hd1 : Nat.card ((c (n + 1)).map φ) ∣ Nat.card (c (n + 1)) :=
      Subgroup.card_map_dvd (H := c (n + 1)) φ
    have hd2 : Nat.card (Nt.map φ) ∣ Nat.card Nt := Subgroup.card_map_dvd (H := Nt) φ
    have hcop' : Nat.Coprime (Nat.card (Nt.map φ)) (Nat.card ((c (n + 1)).map φ)) :=
      (hcop.coprime_dvd_left hd2).coprime_dvd_right hd1
    have key : ⁅Nt.map φ, (c (n + 1)).map φ⁆ = ⊥ :=
      ih (Nt.map φ) (fun i => (c (i + 1)).map φ) hd0
        (fun i => Subgroup.map_mono (hmono (i + 1))) (fun i => hdcomm i) hcop'
    -- so `⁅Nt, c (n+1)⁆ ≤ c 1`
    have hsub : ⁅Nt, c (n + 1)⁆ ≤ c 1 := by
      have hmapbot : (⁅Nt, c (n + 1)⁆).map φ = ⊥ := by
        rw [Subgroup.map_commutator]; exact key
      rwa [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk'] at hmapbot
    -- `|c 1|` divides `|c (n+1)|`, so it is coprime to `|Nt|`
    have hc1le : c 1 ≤ c (n + 1) := monotone_nat_of_le_succ hmono (by omega)
    have hcop1 : Nat.Coprime (Nat.card Nt) (Nat.card (c 1)) :=
      hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hc1le)
    -- the displacement homomorphism kills each `x ∈ c (n+1)`
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro g hg x hx
    rw [Subgroup.mem_bot, commutatorElement_def]
    -- the displacement map `a ↦ a x a⁻¹ x⁻¹` lands in the central layer `c 1`
    have hmemc1 : ∀ a : G, a ∈ Nt → a * x * a⁻¹ * x⁻¹ ∈ c 1 := by
      intro a ha
      have h := hsub (Subgroup.commutator_mem_commutator ha hx)
      rwa [commutatorElement_def] at h
    have hmuleq : ∀ a b : G, a ∈ Nt → b ∈ Nt →
        (a * b) * x * (a * b)⁻¹ * x⁻¹ = (a * x * a⁻¹ * x⁻¹) * (b * x * b⁻¹ * x⁻¹) := by
      intro a b _ hb
      have hbx : b * x * b⁻¹ * x⁻¹ ∈ c 1 := hmemc1 b hb
      have e1 : (a * b) * x * (a * b)⁻¹ * x⁻¹
          = a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ * (a * x * a⁻¹ * x⁻¹) := by group
      rw [e1]
      have e2 : a * (b * x * b⁻¹ * x⁻¹) * a⁻¹ = b * x * b⁻¹ * x⁻¹ := by
        rw [hZcomm _ hbx a]; group
      rw [e2, hZcomm _ hbx (a * x * a⁻¹ * x⁻¹)]
    let ψ : Nt →* G := MonoidHom.mk' (fun a => (a : G) * x * (a : G)⁻¹ * x⁻¹) (by
      intro a b
      rw [Subgroup.coe_mul]
      exact hmuleq _ _ a.2 b.2)
    have hψrange : ψ.range ≤ c 1 := by
      rintro _ ⟨a, rfl⟩
      exact hmemc1 (a : G) a.2
    have hone : Nat.card ψ.range = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop1 (Subgroup.card_range_dvd ψ)
        (Subgroup.card_dvd_of_le hψrange)
    have hbot : ψ.range = ⊥ := Subgroup.card_eq_one.mp hone
    have hgx : ψ ⟨g, hg⟩ = 1 := by
      have hmem : ψ ⟨g, hg⟩ ∈ ψ.range := ⟨⟨g, hg⟩, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    exact hgx

/-! ## The `Y`-conjugation action on `V = P/S` -/

variable {Y : Type} [Group Y] [Finite Y]

/-- Conjugation by `y ∈ Y` as an endomorphism of the normal subgroup `P`. -/
noncomputable def conjHom (P : Subgroup Y) (hP : P.Normal) (y : Y) : ↥P →* ↥P where
  toFun p := ⟨y * (p : Y) * y⁻¹, hP.conj_mem (p : Y) p.2 y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by push_cast; group)

theorem conjHom_compat (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal) (y : Y) :
    S.subgroupOf P ≤ (S.subgroupOf P).comap (conjHom P hP y) := by
  intro p hp
  rw [Subgroup.mem_comap]
  exact Subgroup.mem_subgroupOf.mpr (hS.conj_mem (p : Y) (Subgroup.mem_subgroupOf.mp hp) y)

/-- The conjugation `MulAction` of `Y` on `V = ↥P ⧸ (S.subgroupOf P)`.  Marked `reducible` so
`y • ⟦p⟧` unfolds definitionally to `QuotientGroup.map … ⟦p⟧` at the users. -/
@[reducible] noncomputable def blockAction (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal) :
    MulAction Y (↥P ⧸ S.subgroupOf P) :=
  letI : (S.subgroupOf P).Normal := hS.subgroupOf P
  { smul := fun y => QuotientGroup.map _ _ (conjHom P hP y) (conjHom_compat S P hS hP y)
    one_smul := fun q => by
      refine QuotientGroup.induction_on q fun p => ?_
      show (QuotientGroup.mk (conjHom P hP 1 p) : ↥P ⧸ S.subgroupOf P) = QuotientGroup.mk p
      congr 1
      refine Subtype.ext ?_
      show (1 : Y) * (p : Y) * 1⁻¹ = (p : Y)
      group
    mul_smul := fun y₁ y₂ q => by
      refine QuotientGroup.induction_on q fun p => ?_
      show (QuotientGroup.mk (conjHom P hP (y₁ * y₂) p) : ↥P ⧸ S.subgroupOf P)
          = QuotientGroup.mk (conjHom P hP y₁ (conjHom P hP y₂ p))
      congr 1
      refine Subtype.ext ?_
      show (y₁ * y₂) * (p : Y) * (y₁ * y₂)⁻¹ = y₁ * (y₂ * (p : Y) * y₂⁻¹) * y₁⁻¹
      group }

theorem blockAction_smul_mk (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal)
    (y : Y) (p : ↥P) :
    letI := blockAction S P hS hP
    y • (QuotientGroup.mk p : ↥P ⧸ S.subgroupOf P) = QuotientGroup.mk (conjHom P hP y p) := by
  letI : (S.subgroupOf P).Normal := hS.subgroupOf P
  exact QuotientGroup.map_mk' _ _ _ _ _

/-- The `Y`-conjugation action **as a permutation representation** `Y →* Perm (P/S)`, built
directly from `QuotientGroup.map` (so `φ y ⟦p⟧` reduces to `⟦conjHom y p⟧` with no `MulAction`
instance diamond — the form the p-group fixed-point count needs). -/
noncomputable def blockPerm (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal) :
    Y →* Equiv.Perm (↥P ⧸ S.subgroupOf P) :=
  letI : (S.subgroupOf P).Normal := hS.subgroupOf P
  { toFun := fun y =>
      { toFun := QuotientGroup.map _ _ (conjHom P hP y) (conjHom_compat S P hS hP y)
        invFun := QuotientGroup.map _ _ (conjHom P hP y⁻¹) (conjHom_compat S P hS hP y⁻¹)
        left_inv := fun q => by
          refine QuotientGroup.induction_on q fun p => ?_
          show (QuotientGroup.mk (conjHom P hP y⁻¹ (conjHom P hP y p)) : ↥P ⧸ S.subgroupOf P)
              = QuotientGroup.mk p
          congr 1
          exact Subtype.ext (by show y⁻¹ * (y * (p : Y) * y⁻¹) * y⁻¹⁻¹ = (p : Y); group)
        right_inv := fun q => by
          refine QuotientGroup.induction_on q fun p => ?_
          show (QuotientGroup.mk (conjHom P hP y (conjHom P hP y⁻¹ p)) : ↥P ⧸ S.subgroupOf P)
              = QuotientGroup.mk p
          congr 1
          exact Subtype.ext (by show y * (y⁻¹ * (p : Y) * y⁻¹⁻¹) * y⁻¹ = (p : Y); group) }
    map_one' := by
      refine Equiv.ext fun q => ?_
      refine QuotientGroup.induction_on q fun p => ?_
      show (QuotientGroup.mk (conjHom P hP 1 p) : ↥P ⧸ S.subgroupOf P) = QuotientGroup.mk p
      congr 1
      exact Subtype.ext (by show (1 : Y) * (p : Y) * 1⁻¹ = (p : Y); group)
    map_mul' := fun y₁ y₂ => by
      refine Equiv.ext fun q => ?_
      refine QuotientGroup.induction_on q fun p => ?_
      show (QuotientGroup.mk (conjHom P hP (y₁ * y₂) p) : ↥P ⧸ S.subgroupOf P)
          = QuotientGroup.mk (conjHom P hP y₁ (conjHom P hP y₂ p))
      congr 1
      exact Subtype.ext (by
        show (y₁ * y₂) * (p : Y) * (y₁ * y₂)⁻¹ = y₁ * (y₂ * (p : Y) * y₂⁻¹) * y₁⁻¹; group) }

@[simp] theorem blockPerm_apply_mk (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal)
    (y : Y) (p : ↥P) :
    blockPerm S P hS hP y (QuotientGroup.mk p) = QuotientGroup.mk (conjHom P hP y p) := by
  letI : (S.subgroupOf P).Normal := hS.subgroupOf P
  show QuotientGroup.map (S.subgroupOf P) (S.subgroupOf P) (conjHom P hP y)
      (conjHom_compat S P hS hP y) (QuotientGroup.mk p) = QuotientGroup.mk (conjHom P hP y p)
  exact QuotientGroup.map_mk' _ _ _ _ _

/-! ## Existence of an odd-order element moving the chief factor -/

/-- **An odd-order element moves the simple head `V = P/S`.**  Given the chief condition and a
nontrivial `Y`-action, there is an odd-order `y ∈ Y` and a `p ∈ P` with `[y, p] ∉ S`.  The
paper's odd Hall lift is replaced by this p-group/Cauchy argument (no Hall / Schur–Zassenhaus).
[P-15g.] -/
theorem exists_odd_moving_general
    (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal) (hSP : S < P)
    (hP2 : IsPGroup 2 P)
    (chief : ∀ X : Subgroup Y, X.Normal → S ≤ X → X ≤ P → X = S ∨ X = P)
    (hnt : ∃ (y : Y) (p : Y), p ∈ P ∧ y * p * y⁻¹ * p⁻¹ ∉ S) :
    ∃ y : Y, Odd (orderOf y) ∧ ∃ p ∈ P, y * p * y⁻¹ * p⁻¹ ∉ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hSPn : (S.subgroupOf P).Normal := hS.subgroupOf P
  by_contra hcon
  simp only [not_exists, not_and, not_forall, not_not] at hcon
  have hodd_triv : ∀ y : Y, Odd (orderOf y) → ∀ p ∈ P, y * p * y⁻¹ * p⁻¹ ∈ S := fun y hy p hp =>
    hcon y hy p hp
  set Q := ↥P ⧸ S.subgroupOf P with hQdef
  set φ : Y →* Equiv.Perm Q := blockPerm S P hS hP with hφ
  -- the coset `mk p` is `φ y`-fixed iff `[y, ↑p⁻¹] ∈ S`
  have hval : ∀ (y : Y) (p : ↥P),
      (((conjHom P hP y p)⁻¹ * p : ↥P) : Y) = y * (p : Y)⁻¹ * y⁻¹ * (p : Y) := by
    intro y p
    show (y * (p : Y) * y⁻¹)⁻¹ * (p : Y) = y * (p : Y)⁻¹ * y⁻¹ * (p : Y)
    group
  have hfix_iff : ∀ (y : Y) (p : ↥P),
      φ y (QuotientGroup.mk p) = QuotientGroup.mk p ↔ y * (p : Y)⁻¹ * y⁻¹ * (p : Y) ∈ S := by
    intro y p
    rw [hφ, blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact Iff.of_eq (congrArg (· ∈ S) (hval y p))
  have hφ1 : ∀ z : Y, (∀ p ∈ P, z * p * z⁻¹ * p⁻¹ ∈ S) → φ z = 1 := by
    intro z hz
    refine Equiv.Perm.ext fun q => ?_
    refine QuotientGroup.induction_on q fun p => ?_
    show φ z (QuotientGroup.mk p) = QuotientGroup.mk p
    rw [hfix_iff]
    have := hz (p : Y)⁻¹ (P.inv_mem p.2)
    simpa using this
  -- `φ.range` is a 2-group: the odd part of every `y` acts trivially
  have hrange2 : IsPGroup 2 (φ.range) := by
    rintro ⟨g, y, rfl⟩
    refine ⟨(orderOf y).factorization 2, ?_⟩
    have hn0 : orderOf y ≠ 0 := (orderOf_pos y).ne'
    have hoddord : Odd (orderOf (y ^ (2 ^ (orderOf y).factorization 2))) := by
      rw [orderOf_pow' _ (pow_ne_zero _ two_ne_zero),
        Nat.gcd_eq_right (Nat.ordProj_dvd (orderOf y) 2)]
      exact Nat.not_even_iff_odd.mp fun he =>
        Nat.not_dvd_ordCompl Nat.prime_two hn0 (even_iff_two_dvd.mp he)
    have hz : φ (y ^ (2 ^ (orderOf y).factorization 2)) = 1 :=
      hφ1 _ (hodd_triv _ hoddord)
    refine Subtype.ext ?_
    rw [SubmonoidClass.coe_pow]
    show (φ y) ^ (2 ^ (orderOf y).factorization 2) = 1
    rw [← map_pow]; exact hz
  -- `V = P/S` is a nontrivial finite 2-group
  haveI hQ2 : IsPGroup 2 Q := hP2.to_quotient (S.subgroupOf P)
  obtain ⟨p₀, hp₀P, hp₀S⟩ := SetLike.exists_of_lt hSP
  haveI hQnt : Nontrivial Q := by
    refine ⟨QuotientGroup.mk ⟨p₀, hp₀P⟩, 1, ?_⟩
    rw [ne_eq, QuotientGroup.eq_one_iff]
    exact fun hmem => hp₀S (Subgroup.mem_subgroupOf.mp hmem)
  have hcardQ : 2 ∣ Nat.card Q := by
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨k, hk⟩ := hQ2 q
    have hdvd : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hne1 : orderOf q ≠ 1 := fun h => hq (orderOf_eq_one_iff.mp h)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j ≠ 0 := fun h0 => hne1 (by rw [hj, h0, pow_zero])
    exact (hj ▸ dvd_pow_self 2 hj0).trans (orderOf_dvd_natCard q)
  -- fixed-point count of the 2-group `φ.range` acting on `Q`
  letI : MulAction ↥φ.range Q := MulAction.compHom Q φ.range.subtype
  have hmod := hrange2.card_modEq_card_fixedPoints (α := Q)
  have hFPeven : 2 ∣ Nat.card (MulAction.fixedPoints ↥φ.range Q) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hcardQ))
  -- `mk 1` is fixed
  have hFP1 : (QuotientGroup.mk 1 : Q) ∈ MulAction.fixedPoints ↥φ.range Q := by
    rintro ⟨g, y, rfl⟩
    show φ y (QuotientGroup.mk (1 : ↥P)) = QuotientGroup.mk 1
    rw [hfix_iff]
    simpa using hS.conj_mem 1 (one_mem S) y
  -- so there is a nonzero fixed coset
  have hFP2 : 2 ≤ Nat.card (MulAction.fixedPoints ↥φ.range Q) :=
    Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨⟨_, hFP1⟩, inferInstance⟩) hFPeven
  haveI : Nontrivial (MulAction.fixedPoints ↥φ.range Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hxne⟩ := exists_ne (⟨QuotientGroup.mk 1, hFP1⟩ : MulAction.fixedPoints ↥φ.range Q)
  -- the fixed coset `↑x = mk p₁`, `p₁ ∉ S`, with every `Y`-commutator of `↑p₁⁻¹` in `S`
  obtain ⟨p₁, hp₁⟩ := QuotientGroup.mk_surjective (x : Q)
  have hxfix : ∀ y : Y, y * (p₁ : Y)⁻¹ * y⁻¹ * (p₁ : Y) ∈ S := by
    intro y
    have := x.2 (⟨φ y, y, rfl⟩ : ↥φ.range)
    rw [← hp₁] at this
    exact (hfix_iff y p₁).mp this
  have hp₁S : (p₁ : Y) ∉ S := by
    intro hmem
    apply hxne
    apply Subtype.ext
    show (x : Q) = QuotientGroup.mk 1
    rw [← hp₁]
    refine QuotientGroup.eq.mpr ?_
    rw [mul_one, Subgroup.mem_subgroupOf]
    simpa using inv_mem hmem
  -- the fixed subgroup `W = {p ∈ P | ∀ y, [y,p] ∈ S}` is `Y`-normal, `S < W ≤ P`
  let W : Subgroup Y :=
    { carrier := {p | p ∈ P ∧ ∀ y : Y, y * p * y⁻¹ * p⁻¹ ∈ S}
      one_mem' := ⟨one_mem P, fun y => by simpa using hS.conj_mem 1 (one_mem S) y⟩
      mul_mem' := by
        rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
        refine ⟨mul_mem haP hbP, fun y => ?_⟩
        have e : y * (a * b) * y⁻¹ * (a * b)⁻¹
            = (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact mul_mem (ha y) (hS.conj_mem _ (hb y) a)
      inv_mem' := by
        rintro a ⟨haP, ha⟩
        refine ⟨inv_mem haP, fun y => ?_⟩
        have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
        rw [e]
        have := hS.conj_mem _ (inv_mem (ha y)) a⁻¹
        simpa using this }
  have hWnormal : W.Normal := by
    constructor
    intro a ha g
    refine ⟨hP.conj_mem a ha.1 g, fun y => ?_⟩
    have e : y * (g * a * g⁻¹) * y⁻¹ * (g * a * g⁻¹)⁻¹
        = g * ((g⁻¹ * y * g) * a * (g⁻¹ * y * g)⁻¹ * a⁻¹) * g⁻¹ := by group
    rw [e]
    exact hS.conj_mem _ (ha.2 (g⁻¹ * y * g)) g
  have hSW : S ≤ W := fun s hs => ⟨hSP.le hs, fun y => mul_mem (hS.conj_mem s hs y) (inv_mem hs)⟩
  have hWP : W ≤ P := fun p hp => hp.1
  have hq₁W : (p₁ : Y)⁻¹ ∈ W := by
    refine ⟨inv_mem p₁.2, fun y => ?_⟩
    simpa using hxfix y
  have hSltW : S < W := hSW.lt_of_ne fun hEq => hp₁S (by
    have : (p₁ : Y)⁻¹ ∈ S := hEq ▸ hq₁W
    simpa using inv_mem this)
  rcases chief W hWnormal hSW hWP with hWS | hWP'
  · exact absurd hWS.symm hSltW.ne
  · obtain ⟨y, p, hpP, hcomm⟩ := hnt
    exact hcomm (((hWP'.symm ▸ hpP : p ∈ W)).2 y)

end GQ2
