/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.UVFrames

/-!
# W45 — surjectivity by mod-2 linear algebra, and the arbitrary-dressing family

Two things, the first of which is independent of the second.

## Headline 1 — surjectivity is mod-2 linear algebra on `H₁`

`SqCore/LamFrames.lean` §2b and `SqCore/UVFrames.lean` §3 prove a frame's lift surjective by
*stripping off* the dressings: the argument needs one of the two cleared letters to sit in a slot
bare, which is why the two-letter family is posed at `d = d' = 0`.  §1–§2 here replace the
strip-off by the pro-2 Burnside/Frattini criterion of `GQ2/FrattiniCriterion.lean`:

```text
SqModTwoIndep m := ∀ M : OpenNormalSubgroup (D_sq h), index M = 2 → ∃ i, m i ∉ M
```

and `sqSurjective_of_modTwoIndep` turns that into surjectivity of **any** endomorphism realizing
`m`.  Since an index-2 open normal subgroup swallows every square and every commutator (§1), the
condition is exactly "the slots span `H₁ = D_sq h / [G,G]G²` over `𝔽₂`" — checkable by hand for
any dressing, with no recovery argument at all.  ⭐ It costs nothing on the completeness side:
`sqModTwoIndep_of_aut` says a frame read off an automorphism satisfies it automatically.

⚠ **The `d = d' = 0` restriction is gone.**  §3 checks the condition for `sqEichFrameUV` at
**every** weight tuple with `d·d'` even (`sqEichFrameUV_modTwoIndep`), so the two-letter frame's
lift is surjective there (`sqEichFrameUV_surjective_of_even`) and `sqEichStepUV_of_even` is the
clearing step at general `(d, d')`.  The `d·d'`-even hypothesis is not an artefact: at `d` and
`d'` both odd the frame matrix `!![1, d; d', 1]` is singular mod 2 and the frame really is not a
basis of `H₁` — the offline `D₄` sweep recorded in `UVFrames` sees the same `1 − d·d'`.

## Headline 2 — the arbitrary-dressing family, and why it is the last one

`LamFrames` §4 named the widening that neither recorded refutation mechanism can reach: dress the
moved slots by **arbitrary** `λ`-trivial, `ν'`-trivial elements rather than by words in the two
cleared letters.  §4–§6 build it:

```text
base = ( σ , x₀ , x₁ , U , V , … )        (the `j`-th handle letters cleared, rest standing)
m i  = base i · a i ,   a i ∈ ker λ ∩ ker ν'
```

The rows transpose verbatim from `LamFrames` §2a for the third time — those proofs use only that
the dressing is `λ`-trivial and `ν'`-trivial — and surjectivity is Headline 1.  What is left is
again a single closed equation, `SqArbRelWord h`.

⭐⭐ **And this family is *complete*:** `sqArbRelWord_iff_clearingStep` proves

```text
SqArbRelWord h ↔ SqClearingStep h        and hence   SqArbRelWord 1 ↔ SqLamMarkTransitivity 1
```

— the arbitrary-dressing existential is not merely *out of reach* of the collapse mechanism of
`SqCore/EichRefutation.lean` §7, it is out of reach of **every** homomorphism-based refutation,
because refuting it would refute `SqClearingStep h` itself (and at one handle, the residual).
That settles the family-hunting phase of the search: no further widening of the one-handle
clearing scheme exists, since this one already *is* the scheme.

⚠ What it does **not** do: `SqArbRelWord h` is a hypothesis, not a theorem.  The equivalence
relocates the difficulty rather than removing it — the content of the residual is now visibly
"exhibit the five dressings", with the rows, the surjectivity and the composition all discharged.

## Contents

* **§1** the index-two membership calculus (squares, commutators, `ℤ₂`-powers);
* **§2** `SqModTwoIndep`, `sqSurjective_of_modTwoIndep`, `sqModTwoIndep_of_aut`;
* **§3** the two-letter family at general `(d, d')`, `d·d'` even;
* **§4** `sqArbBase`, `sqArbFrame` and their slots;
* **§5** the rows, the clearing step;
* **§6** `SqArbRelWord`, the equivalence with `SqClearingStep`, and the residual;
* **§7** stress pins, **§8** committed axiom prints.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3** (`propext`,
`Classical.choice`, `Quot.sound`).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The index-two membership calculus

An index-two normal subgroup `M` of any group has quotient of exponent two, hence abelian, so `M`
swallows every square and every commutator.  In a pro-2 group it therefore also swallows every
`ℤ₂`-power at an even exponent, and an odd `ℤ₂`-power lies in `M` exactly when its base does.
That is the whole of "membership mod `M` is `𝔽₂`-linear algebra on `H₁`". -/

section IndexTwo

variable {P : Type*} [Group P] {M : Subgroup P} [M.Normal]

omit [M.Normal] in
private theorem quot_card_two (hM : M.index = 2) : Nat.card (P ⧸ M) = 2 := by
  rwa [← Subgroup.index_eq_card]

/-- An index-two quotient has exponent two. -/
private theorem quot_sq_eq_one (hM : M.index = 2) (z : P ⧸ M) : z ^ 2 = 1 :=
  orderOf_dvd_iff_pow_eq_one.mp (by rw [← quot_card_two hM]; exact orderOf_dvd_natCard z)

/-- **Every square lies in an index-two normal subgroup.** -/
theorem sq_mem_of_index_two (hM : M.index = 2) (z : P) : z ^ 2 ∈ M := by
  refine (QuotientGroup.eq_one_iff _).mp ?_
  have hq : QuotientGroup.mk' M (z ^ 2) = 1 := by
    rw [map_pow, quot_sq_eq_one hM]
  exact hq

/-- **Every commutator lies in an index-two normal subgroup** — the quotient has exponent two,
hence is abelian. -/
theorem commP_mem_of_index_two (hM : M.index = 2) (x y : P) : commP x y ∈ M := by
  refine (QuotientGroup.eq_one_iff _).mp ?_
  have hinv : ∀ z : P ⧸ M, z⁻¹ = z := fun z => by
    have hz := quot_sq_eq_one hM z
    rw [pow_two] at hz
    exact inv_eq_of_mul_eq_one_left hz
  have hab : QuotientGroup.mk' M x * QuotientGroup.mk' M y *
      (QuotientGroup.mk' M x * QuotientGroup.mk' M y) = 1 := by
    have h2 := quot_sq_eq_one hM (QuotientGroup.mk' M x * QuotientGroup.mk' M y)
    rwa [pow_two] at h2
  have hq : QuotientGroup.mk' M (commP x y) = 1 := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv, hinv, hinv, ← mul_assoc] at *
    exact hab
  exact hq

end IndexTwo

section IndexTwoProP

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {M : Subgroup P} [M.Normal]

/-- A `ℤ₂`-power at an **even** exponent is a square. -/
theorem zpowZtwo_two_mul (hP : IsProP 2 P) (x : P) (s : ℤ_[2]) :
    zpowZtwo hP x (2 * s) = zpowZtwo hP x s ^ 2 := by
  rw [mul_comm, ← zpowZtwo_zpowZtwo, show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by push_cast; ring,
    zpowZtwo_natCast]

/-- **Even `ℤ₂`-powers land in an index-two normal subgroup**, whatever the base. -/
theorem zpowZtwo_mem_of_even (hP : IsProP 2 P) (hM : M.index = 2) (x : P) {k : ℤ_[2]}
    (hk : (2 : ℤ_[2]) ∣ k) : zpowZtwo hP x k ∈ M := by
  obtain ⟨s, rfl⟩ := hk
  rw [zpowZtwo_two_mul]
  exact sq_mem_of_index_two hM _

/-- **An odd `ℤ₂`-power lies in an index-two normal subgroup exactly when its base does.** -/
theorem zpowZtwo_mem_iff_of_odd (hP : IsProP 2 P) (hM : M.index = 2) (x : P) {k : ℤ_[2]}
    (hk : ¬ (2 : ℤ_[2]) ∣ k) : zpowZtwo hP x k ∈ M ↔ x ∈ M := by
  obtain ⟨q, hq⟩ := two_dvd_sub_of_isUnit (isUnit_iff_not_two_dvd.mpr hk) isUnit_one
  have hsplit : k = 1 + 2 * q := by linear_combination hq
  have heven : zpowZtwo hP x (2 * q) ∈ M := zpowZtwo_mem_of_even hP hM x ⟨q, rfl⟩
  rw [hsplit, zpowZtwo_add, zpowZtwo_one_exp]
  refine ⟨fun hmem => ?_, fun hx => M.mul_mem hx heven⟩
  simpa using M.mul_mem hmem (M.inv_mem heven)

/-- **A `ℤ₂`-power of a member is a member.** -/
theorem zpowZtwo_mem_of_mem (hP : IsProP 2 P) (hM : M.index = 2) {x : P} (hx : x ∈ M)
    (k : ℤ_[2]) : zpowZtwo hP x k ∈ M := by
  by_cases hk : (2 : ℤ_[2]) ∣ k
  · exact zpowZtwo_mem_of_even hP hM x hk
  · exact (zpowZtwo_mem_iff_of_odd hP hM x hk).mpr hx

end IndexTwoProP

/-! ## §2 The criterion: a frame is surjective iff it spans `H₁`

The pro-2 Burnside/Frattini criterion (`GQ2/FrattiniCriterion.lean`,
`surjective_of_forall_not_le_index_p`) says a continuous endomorphism of `D_sq h` is surjective
as soon as its range escapes every index-2 open normal subgroup.  For an endomorphism realizing a
frame that is a condition on the **five words alone**, and by §1 it is `𝔽₂`-linear. -/

section ModTwoCriterion

variable {h : ℕ}

/-- **No index-two open normal subgroup of `D_sq h` swallows every standard generator** — they
generate topologically, and an open subgroup is closed. -/
theorem exists_sqGen_notMem (M : OpenNormalSubgroup (DSq h : Type))
    (hM : M.toSubgroup.index = 2) : ∃ i, sqGen h i ∉ M.toSubgroup := by
  by_contra hc
  have hmem : ∀ i, sqGen h i ∈ M.toSubgroup := fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hclosed : IsClosed ((M.toSubgroup : Subgroup (DSq h : Type)) : Set (DSq h : Type)) :=
    Subgroup.isClosed_of_isOpen _ M.isOpen'
  have hle : Subgroup.closure (Set.range (sqGen h)) ≤ M.toSubgroup :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have htop := Subgroup.topologicalClosure_minimal _ hle hclosed
  rw [dsq_topGen h] at htop
  have hMtop : M.toSubgroup = ⊤ := eq_top_iff.mpr htop
  rw [hMtop, Subgroup.index_top] at hM
  omega

/-- **Mod-2 independence of a frame**: no index-two open normal subgroup swallows every slot.
Dually this says the five slots span `H₁ = D_sq h ⧸ [G,G]G²` over `𝔽₂` — by §1 membership mod
such a subgroup ignores squares and commutators, so the condition is `𝔽₂`-linear algebra. -/
def SqModTwoIndep {h : ℕ} (m : Fin (sqRank h) → (DSq h : Type)) : Prop :=
  ∀ M : OpenNormalSubgroup (DSq h : Type), M.toSubgroup.index = 2 → ∃ i, m i ∉ M.toSubgroup

/-- **The surjectivity reduction.**  Any endomorphism realizing a mod-2 independent frame is
surjective — no strip-off, no recovery of the cleared letters, no relator. -/
theorem sqSurjective_of_modTwoIndep {m : Fin (sqRank h) → (DSq h : Type)}
    (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = m i) (hm : SqModTwoIndep m) : Function.Surjective Φ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_not_le_index_p (p := 2) (isProP_DSq h) Φ ?_
  intro M hM hle
  obtain ⟨i, hi⟩ := hm M hM
  exact hi (hle ⟨sqGen h i, hΦ i⟩)

/-- The same for the frame's own lift. -/
theorem sqLiftHom_surjective_of_modTwoIndep {m : Fin (sqRank h) → (DSq h : Type)}
    (hrel : sqRelWord m = 1) (hm : SqModTwoIndep m) :
    Function.Surjective (sqLiftHom h (isProP_DSq h) m hrel) :=
  sqSurjective_of_modTwoIndep _ (sqLiftHom_gen h (isProP_DSq h) m hrel) hm

/-- ⭐ **The criterion costs nothing on the completeness side**: a frame read off an automorphism
is mod-2 independent automatically.  So imposing it on a frame family does not shrink the family
of *achievable* frames — which is what makes §6's equivalence an equivalence. -/
theorem sqModTwoIndep_of_aut (Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type)) :
    SqModTwoIndep (fun i => Ψ (sqGen h i)) := by
  intro M hM
  by_contra hc
  have hmem : ∀ i, Ψ (sqGen h i) ∈ M.toSubgroup := fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hclosed : IsClosed ((M.toSubgroup.comap (autHom Ψ).toMonoidHom :
      Subgroup (DSq h : Type)) : Set (DSq h : Type)) := by
    rw [Subgroup.coe_comap]
    exact (Subgroup.isClosed_of_isOpen _ M.isOpen').preimage (autHom Ψ).continuous_toFun
  have hle : Subgroup.closure (Set.range (sqGen h)) ≤
      M.toSubgroup.comap (autHom Ψ).toMonoidHom :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact hmem i)
  have htop := Subgroup.topologicalClosure_minimal _ hle hclosed
  rw [dsq_topGen h] at htop
  have hMtop : M.toSubgroup = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro y
    have hy : Ψ (Ψ.symm y) ∈ M.toSubgroup := htop (Subgroup.mem_top (Ψ.symm y))
    rwa [Ψ.apply_symm_apply] at hy
  rw [hMtop, Subgroup.index_top] at hM
  omega

end ModTwoCriterion

/-! ## §3 The two-letter family at general `(d, d')`

`UVFrames` §3 proves surjectivity only at `d = d' = 0`, because there the two cleared letters sit
bare in their slots and every dressing strips off.  §2 removes that: mod an index-2 subgroup the
handle slots read `Ū + d·V̄` and `V̄ + d'·Ū`, a 2-by-2 system with determinant `1 − d·d'`, and it
is invertible over `𝔽₂` exactly when `d·d'` is **even**.  That is the whole check. -/

section UVGeneral

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}
  {f f' e e' d d' : ℤ_[2]}

/-- The pivot `w = σ·x₀^{−c₀}` lies in any index-two normal subgroup containing `σ` and `x₀`. -/
theorem sqPivot_mem_of_index_two {M : Subgroup (DSq h : Type)} [M.Normal] (hM : M.index = 2)
    (hs : dsqSigma h ∈ M) (hx : dsqX0 h ∈ M) : sqPivot h ∈ M := by
  rw [sqPivot, sqMixPivotElem]
  exact M.mul_mem hs (M.inv_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hx _))

/-- An odd `d` forces an even `d'` once `d·d'` is even. -/
private theorem two_dvd_right_of_two_dvd_mul (hdd : (2 : ℤ_[2]) ∣ d * d')
    (hd : ¬ (2 : ℤ_[2]) ∣ d) : (2 : ℤ_[2]) ∣ d' := by
  obtain ⟨w, hw⟩ := isUnit_iff_not_two_dvd.mpr hd
  obtain ⟨k, hk⟩ := hdd
  have hwd : (↑w⁻¹ : ℤ_[2]) * d = 1 := by
    rw [← hw, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  refine ⟨(↑w⁻¹ : ℤ_[2]) * k, ?_⟩
  calc d' = ((↑w⁻¹ : ℤ_[2]) * d) * d' := by rw [hwd, one_mul]
    _ = (↑w⁻¹ : ℤ_[2]) * (d * d') := by ring
    _ = 2 * ((↑w⁻¹ : ℤ_[2]) * k) := by rw [hk]; ring

/-- **The two-letter frame spans `H₁` at every weight tuple with `d·d'` even.**  Only the two
handle slots carry any content: `d·d'` even is exactly invertibility of `!![1, d; d', 1]`. -/
theorem sqEichFrameUV_modTwoIndep (hdd : (2 : ℤ_[2]) ∣ d * d') :
    SqModTwoIndep (sqEichFrameUV h nu' j f f' e e' d d') := by
  intro M hM
  by_contra hc
  have hslot : ∀ i, sqEichFrameUV h nu' j f f' e e' d d' i ∈ M.toSubgroup :=
    fun i => not_not.mp fun hni => hc ⟨i, hni⟩
  have hu := hslot (sqHandleIdxU j)
  have hv := hslot (sqHandleIdxV j)
  rw [sqEichFrameUV_handleU] at hu
  rw [sqEichFrameUV_handleV] at hv
  -- the 2-by-2 recovery, done mod `M`
  have hUV : sqEichU h nu' j ∈ M.toSubgroup ∧ sqEichV h nu' j ∈ M.toSubgroup := by
    by_cases hd : (2 : ℤ_[2]) ∣ d
    · have hA : sqEichU h nu' j ∈ M.toSubgroup := by
        have hp := M.toSubgroup.mul_mem hu
          (M.toSubgroup.inv_mem (zpowZtwo_mem_of_even (isProP_DSq h) hM (sqEichV h nu' j) hd))
        rwa [mul_inv_cancel_right] at hp
      refine ⟨hA, ?_⟩
      have hp := M.toSubgroup.mul_mem hv
        (M.toSubgroup.inv_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hA d'))
      rwa [mul_inv_cancel_right] at hp
    · have hB : sqEichV h nu' j ∈ M.toSubgroup := by
        have hp := M.toSubgroup.mul_mem hv
          (M.toSubgroup.inv_mem (zpowZtwo_mem_of_even (isProP_DSq h) hM (sqEichU h nu' j)
            (two_dvd_right_of_two_dvd_mul hdd hd)))
        rwa [mul_inv_cancel_right] at hp
      refine ⟨?_, hB⟩
      have hp := M.toSubgroup.mul_mem hu
        (M.toSubgroup.inv_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hB d))
      rwa [mul_inv_cancel_right] at hp
  obtain ⟨hA, hB⟩ := hUV
  -- every dressing is now inside `M`, so the three core letters strip off
  have hcore : ∀ (x : (DSq h : Type)) (k l : ℤ_[2]),
      x * zpowZtwo (isProP_DSq h) (sqEichU h nu' j) k *
          zpowZtwo (isProP_DSq h) (sqEichV h nu' j) l ∈ M.toSubgroup → x ∈ M.toSubgroup := by
    intro x k l hx
    have h1 := M.toSubgroup.mul_mem hx
      (M.toSubgroup.inv_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hB l))
    rw [mul_inv_cancel_right] at h1
    have h2 := M.toSubgroup.mul_mem h1
      (M.toSubgroup.inv_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hA k))
    rwa [mul_inv_cancel_right] at h2
  have hsig : dsqSigma h ∈ M.toSubgroup :=
    hcore _ f e (by have := hslot 0; rwa [sqEichFrameUV_zero] at this)
  have hx0 : dsqX0 h ∈ M.toSubgroup :=
    hcore _ f' e' (by have := hslot 1; rwa [sqEichFrameUV_one] at this)
  have hx1 : dsqX1 h ∈ M.toSubgroup :=
    hcore _ (2 * f') (2 * e') (by have := hslot 2; rwa [sqEichFrameUV_two] at this)
  have hpiv : sqPivot h ∈ M.toSubgroup := sqPivot_mem_of_index_two hM hsig hx0
  have hgenU : sqGen h (sqHandleIdxU j) ∈ M.toSubgroup := by
    rw [← pivotPow_mul_sqEichU (h := h) (nu' := nu') (j := j)]
    exact M.toSubgroup.mul_mem (zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _) hA
  have hgenV : sqGen h (sqHandleIdxV j) ∈ M.toSubgroup := by
    rw [← sqEichV_mul_pivotPow (h := h) (nu' := nu') (j := j)]
    exact M.toSubgroup.mul_mem hB (zpowZtwo_mem_of_mem (isProP_DSq h) hM hpiv _)
  obtain ⟨i, hi⟩ := exists_sqGen_notMem M hM
  refine hi ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · exact hsig
  · exact hx0
  · exact hx1
  · by_cases hjj : j' = j
    · subst hjj; exact hgenU
    · have := hslot (sqHandleIdxU j'); rwa [sqEichFrameUV_handleU_ne hjj] at this
  · by_cases hjj : j' = j
    · subst hjj; exact hgenV
    · have := hslot (sqHandleIdxV j'); rwa [sqEichFrameUV_handleV_ne hjj] at this

/-- **Any endomorphism realizing the two-letter frame with `d·d'` even is surjective** — the
`d = d' = 0` hypothesis of `sqEichFrameUV_surjective_of_hom` is gone. -/
theorem sqEichFrameUV_surjective_of_hom_of_even
    (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrameUV h nu' j f f' e e' d d' i)
    (hdd : (2 : ℤ_[2]) ∣ d * d') : Function.Surjective Φ :=
  sqSurjective_of_modTwoIndep Φ hΦ (sqEichFrameUV_modTwoIndep hdd)

/-- …and hence the frame's own lift. -/
theorem sqEichFrameUV_surjective_of_even
    (hrel : sqRelWord (sqEichFrameUV h nu' j f f' e e' d d') = 1) (hdd : (2 : ℤ_[2]) ∣ d * d') :
    Function.Surjective
      (sqLiftHom h (isProP_DSq h) (sqEichFrameUV h nu' j f f' e e' d d') hrel) :=
  sqLiftHom_surjective_of_modTwoIndep hrel (sqEichFrameUV_modTwoIndep hdd)

/-- **The two-letter clearing step at general `(d, d')`.**  `UVFrames` §3's step is the
`d = d' = 0` case. -/
theorem sqEichStepUV_of_even (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (hdd : (2 : ℤ_[2]) ∣ d * d')
    (hrel : sqRelWord (sqEichFrameUV h nu' j f f' e e' d d') = 1) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
          nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
            ∀ j' : Fin h, j' ≠ j →
              nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j')) := by
  refine ⟨sqAutOfMark hrel (sqEichFrameUV_surjective_of_even hrel hdd), fun x => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · have hext : (nuLam h).comp
        (autHom (sqAutOfMark hrel (sqEichFrameUV_surjective_of_even hrel hdd))) = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel (sqEichFrameUV_surjective_of_even hrel hdd) (sqGen h i))
          = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, sqEichFrameUV_nuLam]
    exact DFunLike.congr_fun hext x
  · show nu' (sqAutOfMark hrel (sqEichFrameUV_surjective_of_even hrel hdd) (sqGen h 0))
      = ofAdd (1 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrameUV_zero hsigma hx0]
  · show nu' (sqAutOfMark hrel (sqEichFrameUV_surjective_of_even hrel hdd) (sqGen h 1))
      = ofAdd (0 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqEichFrameUV_one hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrameUV_handleU_self hsigma hx0]
  · rw [sqAutOfMark_gen, nu_sqEichFrameUV_handleV_self hsigma hx0]
  · exact fun j' hjj => ⟨by rw [sqAutOfMark_gen, sqEichFrameUV_handleU_ne hjj],
      by rw [sqAutOfMark_gen, sqEichFrameUV_handleV_ne hjj]⟩

end UVGeneral

/-! ## §8 Axiom pins

Committed prints: the whole file is **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no
census axiom is reachable. -/

section AxiomPins

#print axioms sq_mem_of_index_two
#print axioms commP_mem_of_index_two
#print axioms zpowZtwo_two_mul
#print axioms zpowZtwo_mem_of_even
#print axioms zpowZtwo_mem_iff_of_odd
#print axioms zpowZtwo_mem_of_mem
#print axioms exists_sqGen_notMem
#print axioms SqModTwoIndep
#print axioms sqSurjective_of_modTwoIndep
#print axioms sqLiftHom_surjective_of_modTwoIndep
#print axioms sqModTwoIndep_of_aut
#print axioms sqPivot_mem_of_index_two
#print axioms sqEichFrameUV_modTwoIndep
#print axioms sqEichFrameUV_surjective_of_hom_of_even
#print axioms sqEichFrameUV_surjective_of_even
#print axioms sqEichStepUV_of_even

end AxiomPins

end SqCore

end Dyadic

end GQ2
