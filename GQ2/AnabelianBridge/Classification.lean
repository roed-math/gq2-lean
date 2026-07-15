/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.AnabelianBridge.Construction

/-!
# Classification half of Proposition 3.8

The kernel and conjugacy analysis completing the lifting result.

See `GQ2.AnabelianBridge` for the paper-facing overview, source citations, and deviations.
-/

open scoped Classical

namespace GQ2

open Multiplicative

/-! ## Proposition 3.8, classification half

Every χ₀-preserving continuous automorphism of `B = D₀^{ab}` is `α_{u,b}` for a unique
`(u, b) ∈ ℤ₂ˣ × ℤ₂` (paper (18)).  Engine: the Lemmas 3.4–3.5 proof's coordinate surjectivity `D0ab_coord`,
the torsion analysis of `t`, and the ℤ₂-powering development's `η`-injectivity; the `(−1)^ε`-component is killed by
the mod-4 argument (`η`-powers are `≡ 1 (mod 4)`, `−1` is not). -/

section ClassificationHalf

open SectionThree

-- The `topAbelianization` instances beyond the §3 statement layer globals are file-local (as in
-- `GQ2/SectionThree.lean`, and for the same reason: a generic global instance perturbs
-- unrelated quotient instance resolution).
noncomputable local instance instCommGroupTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine (QuotientGroup.eq).mpr ?_
    have hcomm : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a := by group
    rw [hcomm]
    apply Subgroup.le_topologicalClosure
    have hmem := Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
    rw [commutator_def]
    simpa [commutatorElement_def] using hmem

local instance instCompactSpaceTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

local instance instT2SpaceTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  have : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

local instance instTotallyDisconnectedSpaceTopAbBridge {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  have : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

variable (B : SectionThree.BDecomposition)

/-- Shorthand: `S̄`-powers in `D₀^{ab}`. -/
noncomputable def sBar (c : ℤ_[2]) : topAbelianization (D0 : Type) :=
  zpowZtwo isProP_two_topAb_D0 (abMk d0S) c

/-- `B.e` reads `S̄`-powers in the second coordinate. -/
lemma bE_sBar (c : ℤ_[2]) :
    B.e (sBar c) = ofAdd ((0 : ZMod 2), c, (0 : ℤ_[2])) := by
  have hnat : B.e (sBar c)
      = zpowZtwo (isProP_two_bcoord B) (B.e (abMk d0S)) c := by
    rw [sBar]
    exact map_zpowZtwo isProP_two_topAb_D0 (isProP_two_bcoord B)
      ⟨B.e.toMulEquiv.toMonoidHom, B.e.continuous_toFun⟩ _ c
  rw [hnat, B.map_S, zpowZtwo_bcoord_S, one_mul]

include B in
/-- `S̄`-powers are injective in the exponent. -/
lemma sBar_injective : Function.Injective sBar := by
  intro c₁ c₂ h
  have hBe : B.e (sBar c₁) = B.e (sBar c₂) := congrArg (⇑B.e) h
  rw [bE_sBar B, bE_sBar B] at hBe
  exact congrArg (fun z => (Multiplicative.toAdd z).2.1) hBe

include B in
/-- The 2-torsion of `D₀^{ab}` is `{1, t}`, `t = abMk (A·S²)` (read off the coordinates:
the `ℤ₂`-components of a square-trivial element vanish). -/
lemma sq_eq_one_iff (z : topAbelianization (D0 : Type)) :
    z ^ 2 = 1 ↔ z = 1 ∨ z = abMk (d0A * d0S ^ 2) := by
  constructor
  · intro h
    have hBe : (B.e z) ^ 2 = 1 := by rw [← map_pow, h, map_one]
    have hcomp : (2 : ℕ) • (Multiplicative.toAdd (B.e z)) = 0 := by
      have h' := congrArg Multiplicative.toAdd hBe
      rwa [show Multiplicative.toAdd ((B.e z) ^ 2)
        = (2 : ℕ) • (Multiplicative.toAdd (B.e z)) from rfl] at h'
    have hx : (Multiplicative.toAdd (B.e z)).2.1 = 0 := by
      have h21 := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] => p.2.1) hcomp
      simp only [Prod.smul_snd, Prod.smul_fst, Prod.snd_zero, Prod.fst_zero] at h21
      have h21' : (2 : ℤ_[2]) * (Multiplicative.toAdd (B.e z)).2.1 = 0 := by
        rw [← h21, nsmul_eq_mul]
        norm_num
      exact (mul_eq_zero.mp h21').resolve_left (by norm_num)
    have hy : (Multiplicative.toAdd (B.e z)).2.2 = 0 := by
      have h22 := congrArg (fun p : ZMod 2 × ℤ_[2] × ℤ_[2] => p.2.2) hcomp
      simp only [Prod.smul_snd, Prod.snd_zero] at h22
      have h22' : (2 : ℤ_[2]) * (Multiplicative.toAdd (B.e z)).2.2 = 0 := by
        rw [← h22, nsmul_eq_mul]
        norm_num
      exact (mul_eq_zero.mp h22').resolve_left (by norm_num)
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (Multiplicative.toAdd (B.e z)).1
      with hε | hε
    · left
      have hz1 : B.e z = B.e 1 := by
        rw [map_one]
        exact bcoord_ext hε hx hy
      exact EquivLike.injective B.e hz1
    · right
      have hzt : B.e z = B.e (abMk (d0A * d0S ^ 2)) := by
        rw [B.map_t]
        exact bcoord_ext hε hx hy
      exact EquivLike.injective B.e hzt
  · rintro (rfl | rfl)
    · exact one_pow 2
    · have hsq : (B.e (abMk (d0A * d0S ^ 2))) ^ 2 = B.e 1 := by
        rw [B.map_t, map_one, pow_two, ← ofAdd_add]
        refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
        · show (1 : ZMod 2) + 1 = 0
          decide
        · show (0 : ℤ_[2]) + 0 = 0
          norm_num
        · show (0 : ℤ_[2]) + 0 = 0
          norm_num
      have hpow : B.e ((abMk (d0A * d0S ^ 2) : topAbelianization (D0 : Type)) ^ 2) = B.e 1 := by
        rw [map_pow]
        exact hsq
      exact EquivLike.injective B.e hpow

variable (ξ : ContinuousMulEquiv (topAbelianization (D0 : Type)) (topAbelianization (D0 : Type)))

/-- `ξ`-naturality of 2-adic powers. -/
lemma xi_zpow (x : topAbelianization (D0 : Type)) (c : ℤ_[2]) :
    ξ (zpowZtwo isProP_two_topAb_D0 x c) = zpowZtwo isProP_two_topAb_D0 (ξ x) c :=
  map_zpowZtwo isProP_two_topAb_D0 isProP_two_topAb_D0
    ⟨ξ.toMulEquiv.toMonoidHom, ξ.continuous_toFun⟩ x c

include B in
/-- Any continuous automorphism fixes `t` (the unique nontrivial 2-torsion element). -/
lemma xi_fixes_t : ξ (abMk (d0A * d0S ^ 2)) = abMk (d0A * d0S ^ 2) := by
  have ht2 : (abMk (d0A * d0S ^ 2) : topAbelianization (D0 : Type)) ^ 2 = 1 :=
    (sq_eq_one_iff B _).mpr (Or.inr rfl)
  have hξ2 : (ξ (abMk (d0A * d0S ^ 2))) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  rcases (sq_eq_one_iff B _).mp hξ2 with h1 | ht
  · exfalso
    have hteq : (abMk (d0A * d0S ^ 2) : topAbelianization (D0 : Type)) = 1 := by
      have := congrArg ξ.symm h1
      rwa [ContinuousMulEquiv.symm_apply_apply, map_one] at this
    have hBet := congrArg B.e hteq
    rw [B.map_t, map_one] at hBet
    have hcomp := congrArg (fun z => (Multiplicative.toAdd z).1) hBet
    exact absurd hcomp (by decide)
  · exact ht

/-- The paper's `η ^ w ≡ 1 (mod 4)` (the image of `zpowZtwo η` lies in `1 + 4ℤ₂`). -/
lemma eta_pow_mod4 (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3) (w : ℤ_[2]) :
    (PadicInt.toZModPow (p := 2) 2
      ((zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ w : ℤ_[2]ˣ) : ℤ_[2]) : ZMod 4) = 1 := by
  letI : TopologicalSpace (ZMod 4) := ⊥
  letI : DiscreteTopology (ZMod 4) := ⟨rfl⟩
  have hcont_toZMod : Continuous (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] → ZMod 4) := by
    rw [continuous_def]
    intro T _
    exact isOpen_preimage_toZModPow 2 T
  have hy0mod : (PadicInt.toZModPow (p := 2) 2 ((y₀ : ℤ_[2])) : ZMod 4) = 1 := by
    rw [hy₀, show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]
    decide
  have hinv_mod : (PadicInt.toZModPow (p := 2) 2 ((y₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) : ZMod 4) = 1 := by
    have hmul : ((y₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((y₀ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h := congrArg (PadicInt.toZModPow (p := 2) 2) hmul
    rwa [map_mul, map_one, hy0mod, mul_one] at h
  set f : Multiplicative ℤ_[2] →* ZMod 4 :=
    (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] →+* ZMod 4).toMonoidHom.comp
      ((Units.coeHom ℤ_[2]).comp
        (zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹).toMonoidHom) with hfdef
  have hfcont : Continuous f :=
    hcont_toZMod.comp (Units.continuous_val.comp
      (zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹).continuous_toFun)
  have hf1 : f = (1 : Multiplicative ℤ_[2] →* ZMod 4) := by
    refine multPadicIntHom_ext hfcont continuous_const ?_
    show (PadicInt.toZModPow (p := 2) 2)
      ((zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹ (ofAdd (1 : ℤ_[2])) : ℤ_[2]ˣ) : ℤ_[2]) = 1
    rw [zpowZtwoHom_ofAdd_one]
    exact hinv_mod
  have hw := DFunLike.congr_fun hf1 (ofAdd w)
  rw [MonoidHom.one_apply] at hw
  exact hw

/-- **The χ-row extraction**: from `(−1)^r · η^y = η^w` conclude `2 ∣ a` (`r = a mod 2 = 0`,
by the mod-4 elimination) and `y = w` (`η`-injectivity, the ℤ₂-powering development (iii)). -/
lemma chi_row_extract (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3) (a y w : ℤ_[2])
    (h : (-1 : ℤ_[2]ˣ) ^ (PadicInt.toZModPow (p := 2) 1 a).val
        * zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y
      = zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ w) :
    (2 : ℤ_[2]) ∣ a ∧ y = w := by
  have hrlt : (PadicInt.toZModPow (p := 2) 1 a).val < 2 := by
    have hlt := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 a)
    simpa using hlt
  rcases (by lia : (PadicInt.toZModPow (p := 2) 1 a).val = 0
      ∨ (PadicInt.toZModPow (p := 2) 1 a).val = 1) with hr0 | hr1
  · rw [hr0, pow_zero, one_mul] at h
    constructor
    · have hval0 : (PadicInt.toZModPow (p := 2) 1 a) = 0 := by
        have : NeZero (2 ^ 1) := ⟨by norm_num⟩
        exact (ZMod.val_eq_zero _).mp hr0
      have hker : a ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := hval0
      rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hker
      exact hker
    · exact zpowZtwo_injective_neg_three_inv y₀ hy₀ h
  · exfalso
    rw [hr1, pow_one] at h
    have hL := congrArg (fun v : ℤ_[2]ˣ => (PadicInt.toZModPow (p := 2) 2 ((v : ℤ_[2])) : ZMod 4)) h
    rw [show (((-1 : ℤ_[2]ˣ) * zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y : ℤ_[2]ˣ) : ℤ_[2])
        = -(((zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y : ℤ_[2]ˣ)) : ℤ_[2]) by push_cast; ring,
      map_neg, eta_pow_mod4 y₀ hy₀, eta_pow_mod4 y₀ hy₀] at hL
    exact absurd hL (by decide)

/-- Abelianized relation: `Ā² S̄⁴ = 1` in `D₀^{ab}`. -/
lemma abMk_relation :
    ((abMk d0A : topAbelianization (D0 : Type))) ^ 2 * (abMk d0S) ^ 4 = 1 := by
  have hcommP : abMk (commP d0S d0Y) = (1 : topAbelianization (D0 : Type)) := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm ((abMk d0S)⁻¹ : topAbelianization (D0 : Type)) ((abMk d0Y)⁻¹)]
    group
  have h2 : abMk (d0A ^ 2 * d0S ^ 4 * commP d0S d0Y) = (1 : topAbelianization (D0 : Type)) := by
    rw [d0_relation]
    exact map_one abMk
  rw [map_mul, map_mul, map_pow, map_pow, hcommP, mul_one] at h2
  exact h2

/-- Even `Ā`-powers are `S̄`-powers: `Ā^{2a₁} = S̄^{−4a₁}`. -/
lemma aPow_even (a : ℤ_[2]) (h2 : (2 : ℤ_[2]) ∣ a) :
    zpowZtwo isProP_two_topAb_D0 (abMk d0A) a = sBar (-2 * a) := by
  obtain ⟨a₁, rfl⟩ := h2
  have hstep1 : zpowZtwo isProP_two_topAb_D0 (abMk d0A) (2 * a₁)
      = zpowZtwo isProP_two_topAb_D0 (zpowZtwo isProP_two_topAb_D0 (abMk d0A) 2) a₁ :=
    (zpowZtwo_zpowZtwo _ _ _ _).symm
  have hstep2 : zpowZtwo isProP_two_topAb_D0 (abMk d0A) (2 : ℤ_[2]) = (abMk d0A) ^ (2 : ℕ) := by
    have hcast : ((2 : ℤ_[2])) = (((2 : ℕ)) : ℤ_[2]) := by norm_num
    rw [hcast, zpowZtwo_natCast]
  have hstep3 : ((abMk d0A : topAbelianization (D0 : Type))) ^ (2 : ℕ)
      = zpowZtwo isProP_two_topAb_D0 (abMk d0S) (-4 : ℤ_[2]) := by
    have hrel := abMk_relation
    have hA2 : ((abMk d0A : topAbelianization (D0 : Type))) ^ (2 : ℕ)
        = (((abMk d0S : topAbelianization (D0 : Type))) ^ (4 : ℕ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      exact hrel
    have hS4 : (((abMk d0S : topAbelianization (D0 : Type))) ^ (4 : ℕ))⁻¹
        = zpowZtwo isProP_two_topAb_D0 (abMk d0S) (-4 : ℤ_[2]) := by
      have hcast : ((-4 : ℤ_[2])) = (((-4 : ℤ)) : ℤ_[2]) := by push_cast; ring
      rw [hcast, zpowZtwo_intCast]
      rw [show ((-4 : ℤ)) = -((4 : ℕ) : ℤ) by norm_num, zpow_neg, zpow_natCast]
    rw [hA2, hS4]
  rw [hstep1, hstep2, hstep3, sBar, zpowZtwo_zpowZtwo]
  congr 1
  ring

/-- The `χ`-value on coordinates: `χ(Ā^a S̄^s Ȳ^y) = (−1)^{a mod 2} η^y`. -/
lemma chi_coord (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (y₀ : ℤ_[2]ˣ)
    (hχA : χ (abMk d0A) = -1) (hχS : χ (abMk d0S) = 1) (hχY' : χ (abMk d0Y) = y₀⁻¹)
    (a s y : ℤ_[2]) :
    χ (zpowZtwo isProP_two_topAb_D0 (abMk d0A) a
        * zpowZtwo isProP_two_topAb_D0 (abMk d0S) s
        * zpowZtwo isProP_two_topAb_D0 (abMk d0Y) y)
      = (-1 : ℤ_[2]ˣ) ^ (PadicInt.toZModPow (p := 2) 1 a).val
        * zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y := by
  have hχnat : ∀ (x : topAbelianization (D0 : Type)) (u : ℤ_[2]),
      χ (zpowZtwo isProP_two_topAb_D0 x u)
        = zpowZtwo isProP_two_unitsPadicInt (χ x) u := fun x u =>
    map_zpowZtwo isProP_two_topAb_D0 isProP_two_unitsPadicInt
      (⟨χ, hχ⟩ : ContinuousMonoidHom (topAbelianization (D0 : Type)) ℤ_[2]ˣ) x u
  have hsq : (-1 : ℤ_[2]ˣ) ^ 2 = 1 := by
    rw [pow_two, ← Units.val_eq_one]
    push_cast
    ring
  rw [map_mul, map_mul, hχnat, hχnat, hχnat, hχA, hχS, hχY',
    zpowZtwo_one_base, mul_one,
    zpowZtwo_of_sq_eq_one isProP_two_unitsPadicInt (-1) hsq a]

/-- The `S̄`-row of a χ-preserving automorphism is a pure `S̄`-power. -/
lemma xi_S_row (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3)
    (hχA : χ (abMk d0A) = -1) (hχS : χ (abMk d0S) = 1) (hχY' : χ (abMk d0Y) = y₀⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃ u : ℤ_[2], ξ (abMk d0S) = sBar u := by
  obtain ⟨a, s, y, hzeq⟩ := D0ab_coord (ξ (abMk d0S))
  have hχval : χ (ξ (abMk d0S)) = 1 := by rw [hpres, hχS]
  rw [hzeq, chi_coord χ hχ y₀ hχA hχS hχY'] at hχval
  obtain ⟨h2a, hy0⟩ := chi_row_extract y₀ hy₀ a y 0
    (by rw [hχval, SectionThree.zpowZtwo_zero])
  refine ⟨-2 * a + s, ?_⟩
  rw [hzeq, hy0, SectionThree.zpowZtwo_zero, mul_one, aPow_even a h2a, sBar, sBar,
    ← zpowZtwo_add]

/-- The `Ȳ`-row of a χ-preserving automorphism is `S̄`-power times `Ȳ`. -/
lemma xi_Y_row (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (y₀ : ℤ_[2]ˣ) (hy₀ : (y₀ : ℤ_[2]) = -3)
    (hχA : χ (abMk d0A) = -1) (hχS : χ (abMk d0S) = 1) (hχY' : χ (abMk d0Y) = y₀⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃ b : ℤ_[2], ξ (abMk d0Y) = sBar b * abMk d0Y := by
  obtain ⟨a, s, y, hzeq⟩ := D0ab_coord (ξ (abMk d0Y))
  have hχval : χ (ξ (abMk d0Y)) = y₀⁻¹ := by rw [hpres, hχY']
  rw [hzeq, chi_coord χ hχ y₀ hχA hχS hχY'] at hχval
  obtain ⟨h2a, hy1⟩ := chi_row_extract y₀ hy₀ a y 1
    (by rw [hχval, zpowZtwo_one_exp])
  refine ⟨-2 * a + s, ?_⟩
  rw [hzeq, hy1, zpowZtwo_one_exp, aPow_even a h2a, sBar, sBar, ← zpowZtwo_add]

namespace SectionThree

/-- **Proposition 3.8, classification half** (paper (18); statement moved from
`GQ2/SectionThree.lean`, see the pointer there).  Every continuous `χ₀`-preserving automorphism
`ξ` of `B = D₀^{ab}` is `α_{u,b}` for a **unique** `(u, b) ∈ ℤ₂ˣ × ℤ₂`: in the coordinates of
the `B`-decomposition it sends `S̄ ↦ S̄^u`, `Ȳ ↦ S̄^b Ȳ`, and (forced by preservation of the
torsion element `t = Ā S̄²` and the relation `Ā² S̄⁴ = 1`) `Ā ↦ t S̄^{-2u}`.  The `S̄`-exponent
`u` is a unit because the same row analysis applies to `ξ⁻¹`.  Axiom-free: the abelianized `D₀`
and its coordinate frame are concrete. -/
theorem prop_3_8_classification
    (χ : topAbelianization (D0 : Type) →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (hχA : χ (abMk d0A) = -1)
    (hχS : χ (abMk d0S) = 1)
    (hχY : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → χ (abMk d0Y) = y⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃! p : ℤ_[2]ˣ × ℤ_[2],
      B.e (ξ (abMk d0A)) = Multiplicative.ofAdd (1, -2 * (p.1 : ℤ_[2]), 0) ∧
      B.e (ξ (abMk d0S)) = Multiplicative.ofAdd (0, (p.1 : ℤ_[2]), 0) ∧
      B.e (ξ (abMk d0Y)) = Multiplicative.ofAdd (0, p.2, 1) := by
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℤ_[2]ˣ, (y₀ : ℤ_[2]) = -3 :=
    ⟨(isUnit_intCast_of_odd (⟨-2, by ring⟩ : Odd (-3 : ℤ))).unit, by
      rw [IsUnit.unit_spec]
      push_cast
      ring⟩
  have hχY' : χ (abMk d0Y) = y₀⁻¹ := hχY y₀ hy₀
  obtain ⟨uval, huS⟩ := xi_S_row ξ χ hχ y₀ hy₀ hχA hχS hχY' hpres
  obtain ⟨b, hbY⟩ := xi_Y_row ξ χ hχ y₀ hy₀ hχA hχS hχY' hpres
  -- the `S̄`-exponent is a unit: the same row extraction for `ξ⁻¹` provides the cofactor
  have hpres' : ∀ x, χ (ξ.symm x) = χ x := fun x => by
    have h := hpres (ξ.symm x)
    rw [ContinuousMulEquiv.apply_symm_apply] at h
    exact h.symm
  obtain ⟨u', huS'⟩ := xi_S_row ξ.symm χ hχ y₀ hy₀ hχA hχS hχY' hpres'
  have hcomp : (abMk d0S : topAbelianization (D0 : Type)) = sBar (uval * u') := by
    have h1 : (abMk d0S : topAbelianization (D0 : Type)) = ξ (ξ.symm (abMk d0S)) :=
      (ξ.apply_symm_apply _).symm
    rw [huS', sBar, xi_zpow ξ, huS, sBar, zpowZtwo_zpowZtwo] at h1
    exact h1
  have hunit : IsUnit uval := by
    have hone : sBar (1 : ℤ_[2]) = abMk d0S := by rw [sBar, zpowZtwo_one_exp]
    have h1 : (1 : ℤ_[2]) = uval * u' := sBar_injective B (hone.trans hcomp)
    exact IsUnit.of_mul_eq_one u' h1.symm
  obtain ⟨u, hu⟩ : ∃ u : ℤ_[2]ˣ, (u : ℤ_[2]) = uval := ⟨hunit.unit, hunit.unit_spec⟩
  -- the three rows in `B.e`-coordinates
  have hSrow : B.e (ξ (abMk d0S)) = ofAdd ((0 : ZMod 2), uval, (0 : ℤ_[2])) := by
    rw [huS]
    exact bE_sBar B uval
  have hYrow : B.e (ξ (abMk d0Y)) = ofAdd ((0 : ZMod 2), b, (1 : ℤ_[2])) := by
    rw [hbY, map_mul, bE_sBar B, B.map_Y, ← ofAdd_add]
    refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show (0 : ZMod 2) + 0 = 0
      decide
    · show b + 0 = b
      ring
    · show (0 : ℤ_[2]) + 1 = 1
      ring
  have hArow : B.e (ξ (abMk d0A)) = ofAdd ((1 : ZMod 2), -2 * uval, (0 : ℤ_[2])) := by
    have hAdec : (abMk d0A : topAbelianization (D0 : Type))
        = abMk (d0A * d0S ^ 2) * ((abMk d0S) ^ 2)⁻¹ := by
      rw [map_mul, map_pow, mul_inv_cancel_right]
    have hξA : ξ (abMk d0A) = abMk (d0A * d0S ^ 2) * ((sBar uval) ^ 2)⁻¹ := by
      rw [hAdec, map_mul, map_inv, map_pow, xi_fixes_t B ξ, huS]
    rw [hξA, map_mul, map_inv, map_pow, B.map_t, bE_sBar B, pow_two, ← ofAdd_add,
      ← ofAdd_neg, ← ofAdd_add]
    refine congrArg ofAdd (Prod.ext ?_ (Prod.ext ?_ ?_))
    · show (1 : ZMod 2) + -((0 : ZMod 2) + 0) = 1
      decide
    · show (0 : ℤ_[2]) + -(uval + uval) = -2 * uval
      ring
    · show (0 : ℤ_[2]) + -((0 : ℤ_[2]) + 0) = 0
      ring
  refine ⟨(u, b), ⟨?_, ?_, ?_⟩, ?_⟩
  · show B.e (ξ (abMk d0A)) = ofAdd ((1 : ZMod 2), -2 * (u : ℤ_[2]), (0 : ℤ_[2]))
    rw [hu]
    exact hArow
  · show B.e (ξ (abMk d0S)) = ofAdd ((0 : ZMod 2), (u : ℤ_[2]), (0 : ℤ_[2]))
    rw [hu]
    exact hSrow
  · exact hYrow
  · rintro ⟨v, c⟩ ⟨-, hvS, hvY⟩
    have hv : (v : ℤ_[2]) = uval := by
      have h := hvS.symm.trans hSrow
      exact congrArg (fun z => (Multiplicative.toAdd z).2.1) h
    have hc : c = b := by
      have h := hvY.symm.trans hYrow
      exact congrArg (fun z => (Multiplicative.toAdd z).2.1) h
    refine Prod.ext ?_ ?_
    · show v = u
      refine Units.ext ?_
      rw [hu]
      exact hv
    · exact hc

end SectionThree

end ClassificationHalf

end GQ2
