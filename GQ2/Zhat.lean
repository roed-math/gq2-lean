import GQ2.AppendixB

/-!
# `ℤ̂` and `ẑ`-exponentiation: the profinite home of `ω₂`  (ticket T-06, unlock U1)

The paper's presentation `Γ_A` uses words with *profinite* exponents: `τ^{ω₂}`, `x₀^{ω₂}` for the
idempotent `ω₂ ∈ ℤ̂` (`≡ 1` on the pro-2 part, `≡ 0` on the odd part).  This file provides that
machinery on top of Mathlib's `ProfiniteGrp.ProfiniteCompletion`:

* `GQ2.Zhat` — `ℤ̂`, the profinite completion of `ℤ` (as `Multiplicative ℤ`; the group law of
  `Zhat` is *addition of exponents*).
* `GQ2.Zhat.ofInt` — the canonical dense embedding `ℤ → ℤ̂` (`Zhat.denseRange_ofInt`).
* `GQ2.zpowHat` (notation `x ^ᶻ γ`) — for `x` in any profinite group, the continuous extension
  of `n ↦ xⁿ` to exponents `γ : ℤ̂`, via the universal property of the completion.
  Naturality: `map_zpowHat`.
* `GQ2.omega2` — `ω₂ ∈ ℤ̂`, constructed componentwise as the compatible family
  `(omega2Exp N)_N` (compatibility = `GQ2.omega2Exp_modEq`).
* **Headline** (`zpowHat_omega2`, `map_zpowHat_omega2`): through every finite quotient, the
  profinite `ω₂`-power computes the finite `ω₂`-calculus of Appendices A/B:
  `f (x ^ᶻ ω₂) = powOmega2 (f x)`.

Only the *group* structure of `ℤ̂` is provided; the ring structure (e.g. `ω₂ · ω₂ = ω₂`) is out
of scope until something needs it.
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

/-! ## Finite-index subgroups of `ℤ`

Everything about `ℤ̂ = lim ℤ/H` reduces to: classes in `ℤ/H` are integers mod the index of `H`.
The two lemmas here make that precise without classifying the subgroups of `ℤ`: in the quotient,
the generator `1` has order exactly `[ℤ : H]`. -/

section IntLevel

/-- In the quotient of `Multiplicative ℤ` by any subgroup, the class of the generator `ofAdd 1`
has order exactly the index (`0` if the index is infinite). -/
lemma orderOf_mk_ofAdd_one (H : Subgroup (Multiplicative ℤ)) :
    orderOf ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : Multiplicative ℤ ⧸ H)
      = H.index := by
  have hgen : ∀ y : Multiplicative ℤ ⧸ H,
      y ∈ Subgroup.zpowers
        ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : Multiplicative ℤ ⧸ H) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      refine Subgroup.mem_zpowers_iff.mpr ⟨x.toAdd, ?_⟩
      rw [← QuotientGroup.mk_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one, ofAdd_toAdd]
  rw [← Nat.card_zpowers, (Subgroup.eq_top_iff' _).mpr hgen, Subgroup.index_eq_card]
  exact Nat.card_congr Subgroup.topEquiv.toEquiv

/-- Membership in a subgroup of `Multiplicative ℤ` is divisibility by its index. -/
lemma ofAdd_mem_iff_index_dvd {H : Subgroup (Multiplicative ℤ)} {a : ℤ} :
    Multiplicative.ofAdd a ∈ H ↔ (H.index : ℤ) ∣ a := by
  have hq : ((Multiplicative.ofAdd a : Multiplicative ℤ) : Multiplicative ℤ ⧸ H)
      = ((Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : Multiplicative ℤ ⧸ H) ^ a := by
    rw [← QuotientGroup.mk_zpow, ← ofAdd_zsmul, smul_eq_mul, mul_one]
  rw [← QuotientGroup.eq_one_iff, hq, ← orderOf_dvd_iff_zpow_eq_one, orderOf_mk_ofAdd_one]

/-- Classes of integers in `ℤ/H` are congruence classes mod the index:
`[a] = [b] ↔ [ℤ : H] ∣ b - a`. -/
lemma mk_ofAdd_eq_mk_ofAdd_iff {H : Subgroup (Multiplicative ℤ)} {a b : ℤ} :
    ((Multiplicative.ofAdd a : Multiplicative ℤ) : Multiplicative ℤ ⧸ H)
      = ((Multiplicative.ofAdd b : Multiplicative ℤ) : Multiplicative ℤ ⧸ H)
      ↔ (H.index : ℤ) ∣ b - a := by
  rw [QuotientGroup.eq, ← ofAdd_neg, ← ofAdd_add, neg_add_eq_sub, ofAdd_mem_iff_index_dvd]

end IntLevel

/-! ## A neighborhood-basis property of profinite completions -/

open ProfiniteGrp.ProfiniteCompletion in
set_option backward.isDefEq.respectTransparency false in
/-- **Congruence neighborhoods are a basis**: if `U ∋ γ` is open in the profinite completion of
`G`, there is a single finite-index level `H₀` such that every element agreeing with `γ` in
`G ⧸ H₀` already lies in `U`.  (Same cofinality argument as `ProfiniteCompletion.denseRange`.) -/
lemma completion_exists_level {G : GrpCat} {γ : completion G} {U : Set (completion G)}
    (hU : IsOpen U) (hγ : γ ∈ U) :
    ∃ H₀ : FiniteIndexNormalSubgroup G, ∀ δ : completion G, δ.1 H₀ = γ.1 H₀ → δ ∈ U := by
  obtain ⟨s, hsO, hsv⟩ := hU
  rw [← hsv, Set.mem_preimage] at hγ
  rcases (isOpen_pi_iff.mp hsO) _ hγ with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => (j.val : Subgroup G)
  have hM : M.Normal := Subgroup.normal_iInf_normal fun j => inferInstance
  have hMFinite : M.FiniteIndex := by
    apply Subgroup.finiteIndex_iInf
    infer_instance
  let m : FiniteIndexNormalSubgroup G := { toSubgroup := M }
  refine ⟨m, fun δ hδ => ?_⟩
  rw [← hsv]
  refine Set.mem_preimage.mpr (hJ2 fun a haJ => ?_)
  let π : m ⟶ a := (iInf_le (fun (j : J) => (j.val : Subgroup G)) ⟨a, haJ⟩).hom
  have hcomp : δ.1 a = γ.1 a := by
    have hδa := (δ.2 π).symm
    have hγa := γ.2 π
    rw [hδa, hδ, hγa]
  exact Set.mem_of_eq_of_mem hcomp (hJ1 a haJ).2

/-! ## `ℤ̂` -/

/-- **`ℤ̂`** — the profinite completion of the integers, i.e. `lim_N ℤ/N` over all finite-index
subgroups.  The paper's profinite exponents (most importantly `ω₂`, cf. `GQ2.omega2`) live here.

Convention: `Zhat` is a completion of the *multiplicative* group `Multiplicative ℤ`, so the group
operation of `Zhat` corresponds to **addition of exponents**: `x ^ᶻ (γ * δ) = x ^ᶻ γ * x ^ᶻ δ`.
Only the group structure is provided (no ring structure yet). -/
def Zhat : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

namespace Zhat

/-- The canonical dense embedding `ℤ → ℤ̂` (written multiplicatively:
`ofInt (a + b) = ofInt a * ofInt b`). -/
def ofInt (n : ℤ) : Zhat :=
  ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ)) (Multiplicative.ofAdd n)

@[simp] lemma ofInt_add (a b : ℤ) : ofInt (a + b) = ofInt a * ofInt b := rfl

@[simp] lemma ofInt_zero : ofInt 0 = 1 := rfl

/-- `ℤ` is dense in `ℤ̂`. -/
lemma denseRange_ofInt : DenseRange ofInt := by
  have h : Set.range ofInt
      = Set.range (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (Multiplicative ℤ))) := by
    ext γ
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨Multiplicative.ofAdd n, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g.toAdd, by simp [ofInt]⟩
  show Dense (Set.range ofInt)
  rw [h]
  exact ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- Two continuous maps out of `ℤ̂` agreeing on `ℤ` agree everywhere. -/
lemma funext_ofInt {X : Type*} [TopologicalSpace X] [T2Space X] {f g : Zhat → X}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ n : ℤ, f (ofInt n) = g (ofInt n)) : f = g :=
  Continuous.ext_on denseRange_ofInt hf hg (by rintro _ ⟨n, rfl⟩; exact h n)


end Zhat

/-! ## `ω₂` as an element of `ℤ̂` -/

/-- **The profinite idempotent `ω₂ ∈ ℤ̂`** (paper §1 and App. A/B): the unique element of
`ℤ̂ = lim_N ℤ/N` that is `≡ 1` on the pro-2 part and `≡ 0` on the odd part.  Constructed
componentwise: at a finite-index subgroup `H ≤ ℤ` the component is the integer representative
`omega2Exp [ℤ:H]` (at the Appendix-B modulus `85667662080` this is the paper's serialized value
`40491355905`, cf. `omega2Exp_appendixB_value`); compatibility of the family is exactly
`omega2Exp_modEq`. -/
noncomputable def omega2 : Zhat :=
  ⟨fun H => QuotientGroup.mk (Multiplicative.ofAdd (omega2Exp H.toSubgroup.index : ℤ)),
   fun H K π => by
    show QuotientGroup.map H.toSubgroup K.toSubgroup (MonoidHom.id _) π.le
        (QuotientGroup.mk (Multiplicative.ofAdd (omega2Exp H.toSubgroup.index : ℤ)))
      = QuotientGroup.mk (Multiplicative.ofAdd (omega2Exp K.toSubgroup.index : ℤ))
    rw [QuotientGroup.map_mk, MonoidHom.id_apply]
    exact mk_ofAdd_eq_mk_ofAdd_iff.mpr
      ((omega2Exp_modEq (Subgroup.index_dvd_of_le π.le)
        Subgroup.FiniteIndex.index_ne_zero).dvd)⟩

/-! ## `ẑ`-exponentiation -/

section ZpowHat

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The `ẑ`-power morphism: for `x` in a profinite group `G`, the unique continuous extension of
`n ↦ xⁿ` to a morphism `ℤ̂ ⟶ G`, via the universal property of the profinite completion. -/
noncomputable def zpowHatHom (x : G) : Zhat ⟶ ProfiniteGrp.of G :=
  ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of G) (GrpCat.ofHom (zpowersHom G x))

/-- `x ^ᶻ γ`: the `γ`-th power of `x : G` for a profinite exponent `γ : ℤ̂` (`G` profinite).
Extends ordinary powers (`zpowHat_ofInt : x ^ᶻ ofInt n = x ^ n`) continuously; the paper's words
`τ^{ω₂}`, `x₀^{ω₂}` are instances (with `γ = GQ2.omega2`). -/
noncomputable def zpowHat (x : G) (γ : Zhat) : G := zpowHatHom x γ

@[inherit_doc] scoped infixr:75 " ^ᶻ " => zpowHat

lemma continuous_zpowHat (x : G) : Continuous (x ^ᶻ ·) :=
  (zpowHatHom x).hom.continuous_toFun

/-- `ẑ`-exponentiation extends ordinary (`ℤ`-)powers. -/
@[simp] lemma zpowHat_ofInt (x : G) (n : ℤ) : x ^ᶻ Zhat.ofInt n = x ^ n := by
  have h := ProfiniteGrp.ProfiniteCompletion.lift_eta
    (P := ProfiniteGrp.of G) (GrpCat.ofHom (zpowersHom G x))
  exact ConcreteCategory.congr_hom h (Multiplicative.ofAdd n)

/-- The exponent group law: `Zhat`-multiplication is addition of exponents. -/
@[simp] lemma zpowHat_mul (x : G) (γ δ : Zhat) : x ^ᶻ (γ * δ) = (x ^ᶻ γ) * (x ^ᶻ δ) :=
  map_mul (zpowHatHom x).hom γ δ

@[simp] lemma zpowHat_one (x : G) : x ^ᶻ (1 : Zhat) = 1 :=
  map_one (zpowHatHom x).hom

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]

/-- **Naturality of `ẑ`-exponentiation**: continuous homomorphisms of profinite groups commute
with `^ᶻ`.  Both sides are continuous extensions of `n ↦ f x ^ n`, so this is uniqueness of the
lift through the completion (`ProfiniteCompletion.lift_unique`). -/
lemma map_zpowHat (f : ContinuousMonoidHom G H) (x : G) (γ : Zhat) :
    f (x ^ᶻ γ) = (f x) ^ᶻ γ := by
  have key : ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of G)
        (GrpCat.ofHom (zpowersHom G x)) ≫ ProfiniteGrp.ofHom f
      = ProfiniteGrp.ProfiniteCompletion.lift (P := ProfiniteGrp.of H)
        (GrpCat.ofHom (zpowersHom H (f x))) := by
    apply ProfiniteGrp.ProfiniteCompletion.lift_unique
    rw [Functor.map_comp, ← Category.assoc, ProfiniteGrp.ProfiniteCompletion.lift_eta,
      ProfiniteGrp.ProfiniteCompletion.lift_eta]
    apply GrpCat.ext
    intro m
    show f (zpowersHom G x m) = zpowersHom H (f x) m
    simp [map_zpow]
  have h2 := ConcreteCategory.congr_hom key γ
  simpa [ProfiniteGrp.comp_apply, zpowHat, zpowHatHom] using! h2


/-! ## Evaluation of `ω₂` through finite quotients -/

/-- **`ω₂` acts on finite groups as the 2-primary projection**: in a finite (discrete) group,
`x ^ᶻ ω₂ = powOmega2 x = x ^ omega2Exp (orderOf x)`.  This ties the profinite element `omega2`
to the entire finite `ω₂`-calculus of Appendices A/B (`GQ2.powOmega2`, `GQ2.markOmega2`, the
word ledger of `GQ2/Words.lean`). -/
theorem zpowHat_omega2 {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
    (x : P) : x ^ᶻ omega2 = powOmega2 x := by
  have hU : IsOpen ((x ^ᶻ ·) ⁻¹' {x ^ᶻ omega2}) :=
    (continuous_zpowHat x).isOpen_preimage _ (isOpen_discrete _)
  have hmem : omega2 ∈ (x ^ᶻ ·) ⁻¹' {x ^ᶻ omega2} := rfl
  obtain ⟨H₀, hH₀⟩ := completion_exists_level hU hmem
  have hN₀ : H₀.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hM : Nat.lcm H₀.toSubgroup.index (orderOf x) ≠ 0 := Nat.lcm_ne_zero hN₀ hord
  have hcomp : (Zhat.ofInt (omega2Exp (Nat.lcm H₀.toSubgroup.index (orderOf x)) : ℤ)).1 H₀
      = omega2.1 H₀ := by
    show ((Multiplicative.ofAdd (omega2Exp (Nat.lcm H₀.toSubgroup.index (orderOf x)) : ℤ) :
        Multiplicative ℤ) : Multiplicative ℤ ⧸ H₀.toSubgroup)
      = ((Multiplicative.ofAdd (omega2Exp H₀.toSubgroup.index : ℤ) :
        Multiplicative ℤ) : Multiplicative ℤ ⧸ H₀.toSubgroup)
    rw [mk_ofAdd_eq_mk_ofAdd_iff]
    exact (omega2Exp_modEq (Nat.dvd_lcm_left _ _) hM).dvd
  have hev : x ^ᶻ Zhat.ofInt (omega2Exp (Nat.lcm H₀.toSubgroup.index (orderOf x)) : ℤ)
      = x ^ᶻ omega2 := hH₀ _ hcomp
  rw [zpowHat_ofInt, zpow_natCast, powOmega2_pow_eq x (Nat.dvd_lcm_right _ _) hM] at hev
  exact hev.symm

/-- **Headline lemma of T-06**: for any continuous homomorphism `f` from a profinite group to a
finite (discrete) group, `f (x ^ᶻ ω₂) = powOmega2 (f x)` — the profinite `ω₂` and the paper's
finite `ω₂`-calculus compute the same thing through every finite quotient.  In particular the
`Γ_A`-relator words, once written with `^ᶻ omega2`, evaluate in finite markings to exactly the
words of `GQ2/Words.lean`. -/
theorem map_zpowHat_omega2 {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P]
    [Finite P] (f : ContinuousMonoidHom G P) (x : G) :
    f (x ^ᶻ omega2) = powOmega2 (f x) := by
  rw [map_zpowHat f x omega2, zpowHat_omega2]

end ZpowHat

/-! ## Sanity checks in `S₃`

The tame frame `S₃ = DihedralGroup 3` of `GQ2/AppendixB.lean`, now computed via the *profinite*
`ω₂`: the odd rotation dies, the reflection survives. -/

section SanityS3


end SanityS3

end GQ2
