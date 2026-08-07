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

**Offline confirmation.**  A sweep over 27 groups of order 8, 16 and 32 (all five of order 8
exhaustively; 20000 sampled markings each at order 16, 5000 at order 32; every pivot exponent
`c₀` mod 8 and every handle row pair `(t, s)`) finds **no** probe refuting the arbitrary-dressing
shape.  The same sweep restricted to `U`/`V`-word dressings *does* reproduce the known refutation
on `DihedralGroup 8` at `ν' = nuSel h j 1 1`, so the sweep has the discriminating power — the
arbitrary family survives exactly where the two-letter family dies.  That is the numerical shadow
of `sqArbRelWord_iff_clearingStep`, which says no such probe can ever exist.

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

/-! ## §4 The arbitrary-dressing frame

`LamFrames` §4 named the widening: dress the moved slots by **arbitrary** `λ`-trivial,
`ν'`-trivial elements.  Written out, the frame is the undressed one — the two cleared letters
`U, V` in the `j`-th handle slots, every other letter standing — with each slot multiplied by its
own dressing:

```text
base = ( σ , x₀ , x₁ , U , V , … ) ,      m i = base i · a i ,   a i ∈ ker λ ∩ ker ν'
```

Note that *every* slot may be dressed, the untouched handles included: their dressings are
`ν'`-trivial, so those rows stay exactly where they were, which is what `SqClearingStep` asks. -/

section ArbFrame

variable {h : ℕ} {nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])} {j : Fin h}

variable (h nu' j) in
/-- **The undressed frame** at handle `j`: the two cleared letters in the handle slots, every
other letter standing. -/
noncomputable def sqArbBase : Fin (sqRank h) → (DSq h : Type) :=
  fun i =>
    if (i : ℕ) = (sqHandleIdxU j : ℕ) then sqEichU h nu' j else
    if (i : ℕ) = (sqHandleIdxV j : ℕ) then sqEichV h nu' j else
    sqGen h i

variable (h nu' j) in
/-- **The arbitrary-dressing frame**: `sqArbBase` with each slot multiplied by its own dressing.
The dressings are unconstrained here; the row hypotheses `λ(a i) = ν'(a i) = 1` enter §5. -/
noncomputable def sqArbFrame (a : Fin (sqRank h) → (DSq h : Type)) :
    Fin (sqRank h) → (DSq h : Type) := fun i => sqArbBase h nu' j i * a i

@[simp] theorem sqArbBase_zero : sqArbBase h nu' j 0 = dsqSigma h := by
  simp only [sqArbBase, sqVal_zero, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

@[simp] theorem sqArbBase_one : sqArbBase h nu' j 1 = dsqX0 h := by
  simp only [sqArbBase, sqVal_one, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

@[simp] theorem sqArbBase_two : sqArbBase h nu' j 2 = dsqX1 h := by
  simp only [sqArbBase, sqVal_two, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]
  rfl

@[simp] theorem sqArbBase_handleU : sqArbBase h nu' j (sqHandleIdxU j) = sqEichU h nu' j := by
  simp only [sqArbBase]
  simp

@[simp] theorem sqArbBase_handleV : sqArbBase h nu' j (sqHandleIdxV j) = sqEichV h nu' j := by
  simp only [sqArbBase, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega)]
  simp

theorem sqArbBase_handleU_ne {j' : Fin h} (hne : j' ≠ j) :
    sqArbBase h nu' j (sqHandleIdxU j') = sqGen h (sqHandleIdxU j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqArbBase, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]

theorem sqArbBase_handleV_ne {j' : Fin h} (hne : j' ≠ j) :
    sqArbBase h nu' j (sqHandleIdxV j') = sqGen h (sqHandleIdxV j') := by
  have hv : (j' : ℕ) ≠ (j : ℕ) := fun hc => hne (Fin.val_injective hc)
  simp only [sqArbBase, sqHandleIdxU_val, sqHandleIdxV_val]
  rw [if_neg (by omega), if_neg (by omega)]

/-- The undressed frame carries the standard `λ`-row: both cleared letters are `λ`-trivial, as
are the handle letters they replace. -/
theorem nuLam_sqArbBase (i : Fin (sqRank h)) :
    nuLam h (sqArbBase h nu' j i) = nuLam h (sqGen h i) := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show nuLam h (sqArbBase h nu' j 0) = nuLam h (dsqSigma h)
    rw [sqArbBase_zero]
  · show nuLam h (sqArbBase h nu' j 1) = nuLam h (dsqX0 h)
    rw [sqArbBase_one]
  · show nuLam h (sqArbBase h nu' j 2) = nuLam h (dsqX1 h)
    rw [sqArbBase_two]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbBase_handleU, nuLam_handleU]
      exact Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichU, toAdd_one])
    · rw [sqArbBase_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj
      rw [sqArbBase_handleV, nuLam_handleV]
      exact Multiplicative.toAdd.injective (by rw [toAdd_nuLam_sqEichV, toAdd_one])
    · rw [sqArbBase_handleV_ne hjj]

/-! ## §5 The rows, and the clearing step

For the third time the row proofs of `LamFrames` §2a transpose **verbatim**: they use only that
the dressing is `λ`-trivial and `ν'`-trivial, and here that is the defining hypothesis rather
than a computation. -/

variable {a : Fin (sqRank h) → (DSq h : Type)}

/-- **The λ-row of the arbitrary-dressing frame is the standard one.** -/
theorem sqArbFrame_nuLam (ha : ∀ i, nuLam h (a i) = 1) (i : Fin (sqRank h)) :
    nuLam h (sqArbFrame h nu' j a i) = nuLam h (sqGen h i) := by
  rw [sqArbFrame, map_mul, ha, mul_one, nuLam_sqArbBase]

/-- The `σ`-row, with **no** hypothesis on the other handles. -/
theorem nu_sqArbFrame_zero (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (ha : ∀ i, nu' (a i) = 1) : nu' (sqArbFrame h nu' j a 0) = ofAdd (1 : ℤ_[2]) := by
  rw [sqArbFrame, sqArbBase_zero, map_mul, ha, mul_one, hsigma]

/-- The `x₀`-row. -/
theorem nu_sqArbFrame_one (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (ha : ∀ i, nu' (a i) = 1) : nu' (sqArbFrame h nu' j a 1) = ofAdd (0 : ℤ_[2]) := by
  rw [sqArbFrame, sqArbBase_one, map_mul, ha, mul_one, hx0]

/-- The `x₁`-row: the `L_sq` core forces `ν(x₁) = 2ν(x₀)`, so a selected marking puts it at the
standard value already. -/
theorem nu_sqArbFrame_two (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]))
    (ha : ∀ i, nu' (a i) = 1) : nu' (sqArbFrame h nu' j a 2) = nuSq h (dsqX1 h) := by
  rw [sqArbFrame, sqArbBase_two, map_mul, ha, mul_one]
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_nu_dsqX1, hx0, nuSq_x1]
  simp

/-- **Handle `j` is cleared**: its `u`-row vanishes. -/
theorem nu_sqArbFrame_handleU_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (ha : ∀ i, nu' (a i) = 1) :
    nu' (sqArbFrame h nu' j a (sqHandleIdxU j)) = 1 := by
  rw [sqArbFrame, sqArbBase_handleU, map_mul, ha, mul_one]
  exact Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichU hsigma hx0, toAdd_one])

/-- **Handle `j` is cleared**: its `v`-row vanishes. -/
theorem nu_sqArbFrame_handleV_self (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (ha : ∀ i, nu' (a i) = 1) :
    nu' (sqArbFrame h nu' j a (sqHandleIdxV j)) = 1 := by
  rw [sqArbFrame, sqArbBase_handleV, map_mul, ha, mul_one]
  exact Multiplicative.toAdd.injective (by rw [toAdd_nu_sqEichV hsigma hx0, toAdd_one])

/-- **Every other handle row stays exactly where it was** — the dressing is `ν'`-trivial, so
dressing the untouched slots costs nothing. -/
theorem nu_sqArbFrame_handleU_ne (ha : ∀ i, nu' (a i) = 1) {j' : Fin h} (hne : j' ≠ j) :
    nu' (sqArbFrame h nu' j a (sqHandleIdxU j')) = nu' (sqGen h (sqHandleIdxU j')) := by
  rw [sqArbFrame, sqArbBase_handleU_ne hne, map_mul, ha, mul_one]

/-- …and on the `v`-side. -/
theorem nu_sqArbFrame_handleV_ne (ha : ∀ i, nu' (a i) = 1) {j' : Fin h} (hne : j' ≠ j) :
    nu' (sqArbFrame h nu' j a (sqHandleIdxV j')) = nu' (sqGen h (sqHandleIdxV j')) := by
  rw [sqArbFrame, sqArbBase_handleV_ne hne, map_mul, ha, mul_one]

/-- **The ν-row of the arbitrary-dressing frame is the standard marking's**, at handle `j`. -/
theorem sqArbFrame_nu (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (ha : ∀ i, nu' (a i) = 1)
    (hoth : ∀ j' : Fin h, j' ≠ j →
      nu' (sqGen h (sqHandleIdxU j')) = 1 ∧ nu' (sqGen h (sqHandleIdxV j')) = 1)
    (i : Fin (sqRank h)) : nu' (sqArbFrame h nu' j a i) = nuSq h (sqGen h i) := by
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · show nu' (sqArbFrame h nu' j a 0) = nuSq h (dsqSigma h)
    rw [nu_sqArbFrame_zero hsigma ha, nuSq_sigma]
  · show nu' (sqArbFrame h nu' j a 1) = nuSq h (dsqX0 h)
    rw [nu_sqArbFrame_one hx0 ha, nuSq_x0]
  · show nu' (sqArbFrame h nu' j a 2) = nuSq h (dsqX1 h)
    exact nu_sqArbFrame_two hx0 ha
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqArbFrame_handleU_self hsigma hx0 ha, nuSq_handleU]
    · rw [nu_sqArbFrame_handleU_ne ha hjj, (hoth j' hjj).1, nuSq_handleU]
  · by_cases hjj : j' = j
    · subst hjj
      rw [nu_sqArbFrame_handleV_self hsigma hx0 ha, nuSq_handleV]
    · rw [nu_sqArbFrame_handleV_ne ha hjj, (hoth j' hjj).2, nuSq_handleV]

/-- **The one-handle clearing step for the arbitrary-dressing family** — the same five clauses as
`sqEichStep`, `sqEichStepT` and `sqEichStepUV`, with §2's criterion in place of a strip-off. -/
theorem sqArbStep (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) (halam : ∀ i, nuLam h (a i) = 1)
    (hanu : ∀ i, nu' (a i) = 1) (hindep : SqModTwoIndep (sqArbFrame h nu' j a))
    (hrel : sqRelWord (sqArbFrame h nu' j a) = 1) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      (∀ x, nuLam h (Ψ x) = nuLam h x) ∧ nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1 ∧
          nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1 ∧
            ∀ j' : Fin h, j' ≠ j →
              nu' (Ψ (sqGen h (sqHandleIdxU j'))) = nu' (sqGen h (sqHandleIdxU j')) ∧
                nu' (Ψ (sqGen h (sqHandleIdxV j'))) = nu' (sqGen h (sqHandleIdxV j')) := by
  have hsurj := sqLiftHom_surjective_of_modTwoIndep hrel hindep
  refine ⟨sqAutOfMark hrel hsurj, fun x => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hext : (nuLam h).comp (autHom (sqAutOfMark hrel hsurj)) = nuLam h :=
      dsq_hom_ext _ _ fun i => by
        show nuLam h (sqAutOfMark hrel hsurj (sqGen h i)) = nuLam h (sqGen h i)
        rw [sqAutOfMark_gen, sqArbFrame_nuLam halam]
    exact DFunLike.congr_fun hext x
  · show nu' (sqAutOfMark hrel hsurj (sqGen h 0)) = ofAdd (1 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqArbFrame_zero hsigma hanu]
  · show nu' (sqAutOfMark hrel hsurj (sqGen h 1)) = ofAdd (0 : ℤ_[2])
    rw [sqAutOfMark_gen, nu_sqArbFrame_one hx0 hanu]
  · rw [sqAutOfMark_gen, nu_sqArbFrame_handleU_self hsigma hx0 hanu]
  · rw [sqAutOfMark_gen, nu_sqArbFrame_handleV_self hsigma hx0 hanu]
  · exact fun j' hjj => ⟨by rw [sqAutOfMark_gen, nu_sqArbFrame_handleU_ne hanu hjj],
      by rw [sqAutOfMark_gen, nu_sqArbFrame_handleV_ne hanu hjj]⟩

end ArbFrame

/-! ## §6 The residual, and the completeness of the family

`SqArbRelWord h` is again a bare existential — five dressings, one word equation, plus the mod-2
side condition §2 showed is free.  It plugs into `LamFrames` §3's induction like its three
predecessors, and unlike them it is **complete**: `sqArbRelWord_of_clearingStep` reads the
dressings straight off a clearing automorphism, so the family exhausts `SqClearingStep h`.  ⭐
Consequently *no* homomorphism-based refutation can reach it without refuting `SqClearingStep h`
itself — and at one handle, without refuting `SqLamMarkTransitivity 1`. -/

section ArbReduction

variable {h : ℕ}

/-- **The arbitrary-dressing relator identity**: at every selected marking and every handle there
are `λ`-trivial, `ν'`-trivial dressings whose frame spans `H₁` and kills the relator.

This is the widening `LamFrames` §4 named, and by `sqArbRelWord_iff_clearingStep` it is exactly
`SqClearingStep h` — so, unlike `SqEichRelWord`, `SqEichRelWordT`, `SqEichRelWordMix` and
`SqEichRelWordUV`, it is **not** known to be false, and cannot be refuted without refuting the
clearing scheme itself. -/
def SqArbRelWord (h : ℕ) : Prop :=
  ∀ (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ a : Fin (sqRank h) → (DSq h : Type),
        (∀ i, nuLam h (a i) = 1) ∧ (∀ i, nu' (a i) = 1) ∧
          SqModTwoIndep (sqArbFrame h nu' j a) ∧ sqRelWord (sqArbFrame h nu' j a) = 1

/-- The arbitrary-dressing identity supplies a clearing step (§5). -/
theorem sqClearingStep_of_arbRelWord (H : SqArbRelWord h) : SqClearingStep h := by
  intro nu' j hsigma hx0
  obtain ⟨a, halam, hanu, hindep, hrel⟩ := H nu' j hsigma hx0
  exact sqArbStep hsigma hx0 halam hanu hindep hrel

/-- ⭐ **…and conversely.**  A clearing automorphism *is* an arbitrary-dressing frame: put
`a i = base(i)⁻¹ · Ψ(gen i)`.  Every clause is one of `SqClearingStep`'s five, the mod-2 condition
is `sqModTwoIndep_of_aut`, and the relator identity is naturality. -/
theorem sqArbRelWord_of_clearingStep (H : SqClearingStep h) : SqArbRelWord h := by
  intro nu' j hsigma hx0
  obtain ⟨Ψ, hlam, hs, hx, hU, hV, hoth⟩ := H nu' j hsigma hx0
  refine ⟨fun i => (sqArbBase h nu' j i)⁻¹ * Ψ (sqGen h i), ?_, ?_, ?_, ?_⟩
  · intro i
    rw [map_mul, map_inv, hlam, nuLam_sqArbBase, inv_mul_cancel]
  · -- the `ν'`-row of `Ψ(gen i)` is the `ν'`-row of the undressed slot, clause by clause
    have hbase : ∀ i, nu' (Ψ (sqGen h i)) = nu' (sqArbBase h nu' j i) := by
      intro i
      rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
      · show nu' (Ψ (dsqSigma h)) = nu' (sqArbBase h nu' j 0)
        rw [sqArbBase_zero, hs, hsigma]
      · show nu' (Ψ (dsqX0 h)) = nu' (sqArbBase h nu' j 1)
        rw [sqArbBase_one, hx, hx0]
      · show nu' (Ψ (dsqX1 h)) = nu' (sqArbBase h nu' j 2)
        rw [sqArbBase_two]
        refine Multiplicative.toAdd.injective ?_
        have hcomp : toAdd ((nu'.comp (autHom Ψ)) (dsqX1 h))
            = 2 * toAdd ((nu'.comp (autHom Ψ)) (dsqX0 h)) := toAdd_nu_dsqX1 _
        show toAdd ((nu'.comp (autHom Ψ)) (dsqX1 h)) = toAdd (nu' (dsqX1 h))
        rw [hcomp, toAdd_nu_dsqX1]
        show 2 * toAdd (nu' (Ψ (dsqX0 h))) = 2 * toAdd (nu' (dsqX0 h))
        rw [hx, hx0]
      · by_cases hjj : j' = j
        · subst hjj
          rw [sqArbBase_handleU, hU]
          exact (Multiplicative.toAdd.injective
            (by rw [toAdd_nu_sqEichU hsigma hx0, toAdd_one])).symm
        · rw [sqArbBase_handleU_ne hjj]
          exact (hoth j' hjj).1
      · by_cases hjj : j' = j
        · subst hjj
          rw [sqArbBase_handleV, hV]
          exact (Multiplicative.toAdd.injective
            (by rw [toAdd_nu_sqEichV hsigma hx0, toAdd_one])).symm
        · rw [sqArbBase_handleV_ne hjj]
          exact (hoth j' hjj).2
    intro i
    rw [map_mul, map_inv, hbase, inv_mul_cancel]
  · have hframe : sqArbFrame h nu' j (fun i => (sqArbBase h nu' j i)⁻¹ * Ψ (sqGen h i))
        = fun i => Ψ (sqGen h i) := funext fun i => mul_inv_cancel_left _ _
    rw [hframe]
    exact sqModTwoIndep_of_aut Ψ
  · have hframe : sqArbFrame h nu' j (fun i => (sqArbBase h nu' j i)⁻¹ * Ψ (sqGen h i))
        = fun i => Ψ (sqGen h i) := funext fun i => mul_inv_cancel_left _ _
    rw [hframe]
    have hnat := map_sqRelWord (autHom Ψ) (sqGen h)
    rw [dsq_relation h, map_one] at hnat
    exact hnat.symm

/-- ⭐⭐ **The arbitrary-dressing family is exactly the clearing scheme.**  Two consequences:
the family cannot be widened further inside the one-handle scheme, and it cannot be refuted by
any test that does not refute `SqClearingStep h`. -/
theorem sqArbRelWord_iff_clearingStep : SqArbRelWord h ↔ SqClearingStep h :=
  ⟨sqClearingStep_of_arbRelWord, sqArbRelWord_of_clearingStep⟩

/-- **The residual, from the arbitrary-dressing identity.** -/
theorem sqLamMarkTransitivity_of_arbRelWord (H : SqArbRelWord h) : SqLamMarkTransitivity h :=
  sqLamMarkTransitivity_of_clearingStep (sqClearingStep_of_arbRelWord H)

/-- …and hence the handle stratum at every unit exponent. -/
theorem sqHandleMixFixesCore_of_arbRelWord {c : ℤ_[2]} (hc : IsUnit c) (hh : 0 < h)
    (H : SqArbRelWord h) : SqHandleMixFixesCore h c :=
  sqHandleMixFixesCore_of_lamMarkTransitivity hc hh (sqLamMarkTransitivity_of_arbRelWord H)

/-- At one handle a clearing step *is* a full correction: there is no other handle to leave
standing. -/
theorem sqClearingStep_one_of_lamMarkTransitivity (H : SqLamMarkTransitivity 1) :
    SqClearingStep 1 := by
  intro nu' j hsigma hx0
  obtain ⟨Ψ, hlam, hval⟩ := H nu' hsigma hx0
  exact ⟨Ψ, hlam, (hval _).trans (nuSq_sigma 1), (hval _).trans (nuSq_x0 1),
    (hval _).trans (nuSq_handleU 1 j), (hval _).trans (nuSq_handleV 1 j),
    fun j' hjj => absurd (Subsingleton.elim j' j) hjj⟩

/-- **At one handle the clearing scheme is the residual itself.**

**Subsumed** by `sqClearingStep_iff : SqClearingStep h ↔ SqLamMarkTransitivity h`
(`SqCore/CommFrames.lean` §1), which holds at *every* `h`.  The `h = 1` restriction here was only
the absence of a builder for a marking with one handle zeroed and the rest left alone;
`CommFrames`' `sqNuClear` supplies it.  Kept as the `h = 1` instance and as the record of what
was available before W46. -/
theorem sqClearingStep_one_iff : SqClearingStep 1 ↔ SqLamMarkTransitivity 1 :=
  ⟨sqLamMarkTransitivity_of_clearingStep, sqClearingStep_one_of_lamMarkTransitivity⟩

/-- ⭐⭐ **The smallest open instance, exactly.**  At one handle the arbitrary-dressing word
equation is *equivalent* to `SqLamMarkTransitivity 1`.  So a `D₈`-style refutation of this family
would refute the residual outright — which is why the collapse mechanism of
`SqCore/EichRefutation.lean` §7, and every mechanism like it, provably cannot reach it.

**Subsumed** by `sqArbRelWord_iff_lamMarkTransitivity : SqArbRelWord h ↔ SqLamMarkTransitivity h`
(`SqCore/CommFrames.lean` §1), the same statement at every `h`.  Kept as the `h = 1` instance —
the ⭐⭐ reading above is about the smallest open case specifically, and that is what this
spelling says. -/
theorem sqArbRelWord_one_iff : SqArbRelWord 1 ↔ SqLamMarkTransitivity 1 :=
  sqArbRelWord_iff_clearingStep.trans sqClearingStep_one_iff

end ArbReduction

/-! ## §7 Stress pins -/

section StressTests

/-- **The arbitrary ansatz is satisfiable.**  At the standard marking both handle letters are
already cleared, so the undressed frame *is* the standard generating tuple. -/
theorem sqArbBase_nuSq (h : ℕ) (j : Fin h) : sqArbBase h (nuSq h) j = sqGen h := by
  have hV : sqEichV h (nuSq h) j = sqGen h (sqHandleIdxV j) := by
    rw [sqEichV, nuSq_handleV, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, mul_one]
  have hU : sqEichU h (nuSq h) j = sqGen h (sqHandleIdxU j) := by
    rw [sqEichU, nuSq_handleU, toAdd_one, SectionThree.zpowZtwo_zero, inv_one, one_mul]
  refine funext fun i => ?_
  rcases sqIdx_cases i with rfl | rfl | rfl | ⟨j', rfl⟩ | ⟨j', rfl⟩
  · rw [sqArbBase_zero]; rfl
  · rw [sqArbBase_one]; rfl
  · rw [sqArbBase_two]; rfl
  · by_cases hjj : j' = j
    · subst hjj; rw [sqArbBase_handleU, hU]
    · rw [sqArbBase_handleU_ne hjj]
  · by_cases hjj : j' = j
    · subst hjj; rw [sqArbBase_handleV, hV]
    · rw [sqArbBase_handleV_ne hjj]

/-- Stress: hence the trivial dressing already kills the relator at the standard marking. -/
example (h : ℕ) (j : Fin h) : sqRelWord (sqArbFrame h (nuSq h) j fun _ => 1) = 1 := by
  have hf : (sqArbFrame h (nuSq h) j fun _ => 1) = sqGen h := by
    refine funext fun i => ?_
    rw [sqArbFrame, mul_one]
    exact congrFun (sqArbBase_nuSq h j) i
  rw [hf]
  exact dsq_relation h

/-- Stress: `h = 0` runs through the arbitrary reduction too. -/
example : SqLamMarkTransitivity 0 :=
  sqLamMarkTransitivity_of_arbRelWord fun _ j _ _ => absurd j.isLt (by omega)

example : SqArbRelWord 0 := fun _ j _ _ => absurd j.isLt (by omega)

/-- Stress: **every refuted family implies this one** — through `SqClearingStep`, which is what
completeness buys.  So the arbitrary-dressing existential is weaker than all four. -/
example (h : ℕ) (H : SqEichRelWord h) : SqArbRelWord h :=
  sqArbRelWord_of_clearingStep (sqClearingStep_of_eichRelWord H)

example (h : ℕ) (H : SqEichRelWordT h) : SqArbRelWord h :=
  sqArbRelWord_of_clearingStep (sqClearingStep_of_eichRelWordT H)

example (h : ℕ) (H : SqEichRelWordMix h) : SqArbRelWord h :=
  sqArbRelWord_of_clearingStep (sqClearingStep_of_eichRelWordMix H)

example (h : ℕ) (H : SqEichRelWordUV h) : SqArbRelWord h :=
  sqArbRelWord_of_clearingStep (sqClearingStep_of_eichRelWordUV H)

/-- Stress: the `λ`-row is unconditional in the dressings' `λ`-triviality alone — no marking
hypothesis, no weights, no handle count. -/
example (h : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (a : Fin (sqRank h) → (DSq h : Type)) (ha : ∀ i, nuLam h (a i) = 1) (i : Fin (sqRank h)) :
    nuLam h (sqArbFrame h nu' j a i) = nuLam h (sqGen h i) := sqArbFrame_nuLam ha i

/-- Stress: surjectivity of the two-letter frame at a tuple `UVFrames` §3 cannot reach —
`d = 1`, `d' = 2`, so `d·d'` is even but neither slot is bare. -/
example (h : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)
    (f f' e e' : ℤ_[2]) (Φ : ContinuousMonoidHom (DSq h : Type) (DSq h : Type))
    (hΦ : ∀ i, Φ (sqGen h i) = sqEichFrameUV h nu' j f f' e e' 1 2 i) :
    Function.Surjective Φ :=
  sqEichFrameUV_surjective_of_hom_of_even Φ hΦ ⟨1, by ring⟩

/-- Stress: the frame characterization of `LamFrames` §1 is what the whole search aims at, and
the arbitrary family now sits directly underneath it. -/
example (h : ℕ) (H : SqArbRelWord h) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_lamMarkTransitivity (sqLamMarkTransitivity_of_arbRelWord H)

end StressTests

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
#print axioms sqArbBase
#print axioms sqArbFrame
#print axioms sqArbBase_zero
#print axioms sqArbBase_one
#print axioms sqArbBase_two
#print axioms sqArbBase_handleU
#print axioms sqArbBase_handleV
#print axioms sqArbBase_handleU_ne
#print axioms sqArbBase_handleV_ne
#print axioms nuLam_sqArbBase
#print axioms sqArbFrame_nuLam
#print axioms nu_sqArbFrame_zero
#print axioms nu_sqArbFrame_one
#print axioms nu_sqArbFrame_two
#print axioms nu_sqArbFrame_handleU_self
#print axioms nu_sqArbFrame_handleV_self
#print axioms nu_sqArbFrame_handleU_ne
#print axioms nu_sqArbFrame_handleV_ne
#print axioms sqArbFrame_nu
#print axioms sqArbStep
#print axioms SqArbRelWord
#print axioms sqClearingStep_of_arbRelWord
#print axioms sqArbRelWord_of_clearingStep
#print axioms sqArbRelWord_iff_clearingStep
#print axioms sqLamMarkTransitivity_of_arbRelWord
#print axioms sqHandleMixFixesCore_of_arbRelWord
#print axioms sqClearingStep_one_of_lamMarkTransitivity
#print axioms sqClearingStep_one_iff
#print axioms sqArbRelWord_one_iff
#print axioms sqArbBase_nuSq

end AxiomPins

end SqCore

end Dyadic

end GQ2
