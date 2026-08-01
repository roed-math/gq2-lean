/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Words.N0
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.Words.M0
import GQ2.Dyadic.Words.Mpc

/-!
# `WordCertificate.hwild` (dyadic campaign, ticket CB-W)

CB-0 refuted `hwild` as a *generic* statement by exhibiting a counterexample at `R = 1`
(`Count/Routine.lean` §6, `not_isProP_two_ker_tameOfSpec_one`) and handed the per-branch
obligation to AS2–AS5.  This file was chartered to land those five discharges, shaped on the
`ℚ₂` precedents `GQ2.isProP_wildCore` / `GQ2.isProP_wildCoreR`.

**It does not, because they are not provable.**  `hwild` is false for *every* branch, and this
file proves that.

## The finding

`R = 1` is not special.  For **any** relator word `R` over an alphabet with at least two wild
letters, `Γ_R` admits a continuous hom onto `ℤ/3` under which some wild letter hits a generator —
so `ker(tameOfSpec) = W_R` is never pro-`2`.  All five frozen branch families have at least two
wild letters (`N`, `Npc`, `M`, `Mpc` live on `Generator (2 + 2h)`, `L` on `Generator (2h + 1)`,
and `Generator m` carries `m + 1` wild letters), so `hwild` fails for all five — §5.

The reason is a **counting** one, and it is visible in the definition of `GammaR`:

  `gammaRelators n q R = {tameRelatorGen n q, (freeMarking n).eval R}`

is a **two**-relator presentation, and only *one* of those two relators constrains the wild
letters.  Send `σ, τ ↦ 1` and the wild letters into `ℤ/3`: the tame relator `τ^σ · (τ^q)⁻¹` dies
for free, and `R` imposes a single `𝔽₃`-linear condition on the `n + 1` wild images.  One linear
condition in `≥ 2` unknowns always has a nonzero solution (§3), so a wild letter always survives
into `ℤ/3`, whose order-`3` elements are not `2`-elements.

## Why the `ℚ₂` compactness argument does not transfer — the structural point

The ticket asked me to generalize `isProP_wildCore` (`GQ2/AdmissibleLimit.lean:375`).  Reading it
shows why no generalization is possible: **it is not a theorem about a presented group.**  Both
`ℚ₂` precedents run over

  `Γ_A = F₄ ⧸ N_A`   with   `N_A = ⨅ {U open normal // IsAdmissibleU U}`

(`GQ2/GammaA.lean:211`, `GQ2/Roe/GammaR.lean:182`), where `IsAdmissibleU U` **includes the
`Marking.Pro2Core` clause** (`GQ2/Words.lean:132`).  Pro-`2`-ness of the wild core is therefore
built into the *definition* of `Γ_A`/`Γ_R`; the ~80 lines of `isProP_wildCore` do not prove it
from relators, they are the compactness work needed to pass the clause from the finite admissible
quotients up to the limit (Steps A–F: trap an open `V ≤ wildCore` under `W ∩ wildCore`, pull `W`
back to an admissible `Ŵ ≥ N_A`, read off its `Pro2Core` clause, transfer the `2`-power bound).

`GQ2.Dyadic.GammaR` has no such clause — it is `profinitePresentation` of two relator words.  So
the `ℚ₂` argument has no hypothesis to consume here, and §3 shows there is nothing to consume:
the property genuinely fails.  **The gap is definitional, in `GammaR`, not per-branch.**

## What this file lands

* **§1–§3** the refutation machinery: the rank-`2` test group `(ℤ/3)²`, the test marking and the
  hom out of `Γ_R` it induces, and the `𝔽₃`-linear choice of exponents that kills `R`.
* **§4** `not_isProP_two_wildPartR` — for every `n ≥ 1`, every `q` and **every** `R` — and
  `not_hwild`, the certificate field itself, via F3b's `TameSpec.ker_tameOfSpec`.
* **§5** the five branch corollaries; **§6** the `√−2` pilot.
* **§7 the generic core** — the compactness reduction transferred from `isProP_wildCore` to the
  presented setting: `IsProP 2 (wildPartR n q R)` **iff** every finite continuous quotient of
  `Γ_R` has `2`-group wild normal closure (`isProP_wildPartR_iff_pro2Core`).  This is the
  `Pro2Core`-style criterion the ticket anticipated.  It is stated and proved unconditionally, and
  it is exactly the clause that would have to be **added to the definition of `GammaR`** to make
  `hwild` provable — so it survives whatever the owner decides, and §7 is the constructive half
  of this file's report.

## Axiom posture

Every declaration is `sorry`-free and introduces **no axiom**; per-headline `#print axioms` are
the standard three.  The `decide`s are kernel `decide`s in the three-element group.

⚠ `hwild` *is* an axiom on the arithmetic side (B10's `TameQuotientData.isProP`; AX4's structure
field).  It is **not** made one here, and must not be: §4 proves it false for the candidate, so
axiomatizing it would make the candidate layer inconsistent, not merely unproved.

## Sources

`GQ2/AdmissibleLimit.lean` §WildCore (the precedent); `GQ2/Roe/AdmissibleLimit.lean:231`;
`GQ2/Dyadic/TameBoundary.lean` (`gammaRelators`, `wildPartR`, `TameSpec.ker_tameOfSpec`);
`GQ2/Dyadic/Count/Routine.lean` §6 (CB-0's `R = 1` refutation, which §4 generalizes).
-/

namespace GQ2.Dyadic

namespace Count

open GQ2 GQ2.Dyadic.Words

/-! ## §1 The rank-`2` test group `(ℤ/3)²`

The refutation needs two independent `ℤ/3`-directions — one per wild letter it plays off — and
then collapses them along an `𝔽₃`-linear functional chosen to kill `R`.  `ZmodThree` (F3's
`Multiplicative (ZMod 3)`, `TameBoundary.lean:1113`) is the target; its square is the workspace,
and needs no new instances: `DiscreteTopology` on a product is automatic. -/

section TestGroup

/-- The workspace `(ℤ/3)²`, multiplicatively.  Finite and discrete, so it carries every instance
`Marking.eval` needs. -/
abbrev ZmodThreeSq : Type := ZmodThree × ZmodThree

/-- The chosen generator of `ℤ/3`. -/
def gThree : ZmodThree := Multiplicative.ofAdd (1 : ZMod 3)

theorem gThree_pow (k : ℕ) : gThree ^ k = Multiplicative.ofAdd ((k : ZMod 3)) := by
  rw [gThree, ← ofAdd_nsmul, nsmul_eq_mul, mul_one]

theorem gThree_pow_eq_one_iff (k : ℕ) : gThree ^ k = 1 ↔ (k : ZMod 3) = 0 := by
  rw [gThree_pow]
  constructor
  · intro h; simpa using congrArg Multiplicative.toAdd h
  · intro h; rw [h]; rfl

/-- The generator is nontrivial — kernel `decide` on a three-element group. -/
theorem gThree_ne_one : gThree ≠ 1 := by decide

/-- Every element of `ℤ/3` is killed by cubing — kernel `decide` on a three-element group. -/
theorem pow_three_zmodThree (y : ZmodThree) : y ^ 3 = 1 := by revert y; decide

/-- A nontrivial element of `ℤ/3` has order `3`. -/
theorem orderOf_eq_three {y : ZmodThree} (hy : y ≠ 1) : orderOf y = 3 := by
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _
    (orderOf_dvd_of_pow_eq_one (pow_three_zmodThree y)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hy
  · exact h

/-- **The `2`-group obstruction.**  A subgroup of `ℤ/3` containing a nontrivial element is not a
`2`-group.  This is the contradiction every branch of §4 ends in. -/
theorem not_isPGroup_two_of_mem {H : Subgroup ZmodThree} (hp : IsPGroup 2 H) {y : ZmodThree}
    (hy : y ∈ H) (hy1 : y ≠ 1) : False := by
  obtain ⟨k, hk⟩ := hp ⟨y, hy⟩
  have hk1 : y ^ (2 ^ k) = 1 := congrArg Subtype.val hk
  have hdvd : (3 : ℕ) ∣ 2 ^ k := by
    have h := orderOf_dvd_of_pow_eq_one hk1
    rwa [orderOf_eq_three hy1] at h
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

/-- **The collapse.**  The `𝔽₃`-linear functional `(y, z) ↦ y^c z^d`, as a continuous hom of
finite discrete groups.  `ZmodThreeSq` is commutative, so this is a hom. -/
def collapse (c d : ℕ) : ContinuousMonoidHom ZmodThreeSq ZmodThree where
  toFun p := p.1 ^ c * p.2 ^ d
  map_one' := by simp
  map_mul' p p' := by
    simp only [Prod.fst_mul, Prod.snd_mul, mul_pow]
    exact mul_mul_mul_comm _ _ _ _
  continuous_toFun := continuous_of_discreteTopology

@[simp] theorem collapse_apply (c d : ℕ) (p : ZmodThreeSq) :
    collapse c d p = p.1 ^ c * p.2 ^ d := rfl

@[simp] theorem collapse_one (c d : ℕ) : collapse c d 1 = 1 := by simp

/-- The collapse read additively: it is `(a, b) ↦ c·a + d·b` on `𝔽₃²`. -/
theorem collapse_eq_one_iff (c d : ℕ) (p : ZmodThreeSq) :
    collapse c d p = 1 ↔
      (c : ZMod 3) * Multiplicative.toAdd p.1 + (d : ZMod 3) * Multiplicative.toAdd p.2 = 0 := by
  have h : Multiplicative.toAdd (collapse c d p)
      = (c : ZMod 3) * Multiplicative.toAdd p.1 + (d : ZMod 3) * Multiplicative.toAdd p.2 := by
    simp [collapse_apply, toAdd_mul, toAdd_pow, nsmul_eq_mul]
  rw [← h]
  exact ⟨fun hc => by rw [hc]; rfl, fun hc => Multiplicative.toAdd.injective (by rw [hc]; rfl)⟩

end TestGroup

/-! ## §2 The test marking and the hom out of `Γ_R`

`sqMarking` sends `σ, τ ↦ 1`, `x₀ ↦ (g, 1)`, `x₁ ↦ (1, g)` and every other wild letter to `1`;
`testMarking c d` is its collapse along `(y, z) ↦ y^c z^d`.  The point of routing through the
square is that `Marking.map_eval` then computes `(testMarking c d).eval R` *linearly* in `(c, d)`
from the single group element `(sqMarking n).eval R` — which is what makes §3's choice possible
without knowing anything about `R`. -/

section TestMarking

variable {n : ℕ}

/-- `(1 : Fin (n + 1)) ≠ 0` as soon as there are two wild letters. -/
theorem fin_one_ne_zero (hn : 1 ≤ n) : (1 : Fin (n + 1)) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega)] at hv
  omega

/-- The rank-`2` test marking: `σ, τ ↦ 1`, `x₀ ↦ (g, 1)`, `x₁ ↦ (1, g)`, all other wild letters
`↦ 1`. -/
def sqMarking (n : ℕ) : Marking n ZmodThreeSq :=
  Marking.ofLetters 1 1 (fun i => if i = 0 then (gThree, 1) else if i = 1 then (1, gThree) else 1)

theorem sqMarking_sigma : sqMarking n .sigma = 1 := rfl

theorem sqMarking_tau : sqMarking n .tau = 1 := rfl

theorem sqMarking_wild (i : Fin (n + 1)) :
    sqMarking n (.wild i)
      = if i = 0 then (gThree, 1) else if i = 1 then (1, gThree) else 1 := rfl

/-- The collapsed test marking, valued in `ℤ/3`. -/
def testMarking (n c d : ℕ) : Marking n ZmodThree := (sqMarking n).map ⇑(collapse c d)

@[simp] theorem testMarking_apply_sigma (c d : ℕ) :
    testMarking n c d .sigma = 1 := by
  simp only [testMarking, Marking.map_apply, sqMarking_sigma, collapse_one]

@[simp] theorem testMarking_apply_tau (c d : ℕ) :
    testMarking n c d .tau = 1 := by
  simp only [testMarking, Marking.map_apply, sqMarking_tau, collapse_one]

@[simp] theorem testMarking_wild_zero (c d : ℕ) :
    testMarking n c d (.wild 0) = gThree ^ c := by
  simp only [testMarking, Marking.map_apply, sqMarking_wild, collapse_apply]
  simp

@[simp] theorem testMarking_wild_one (hn : 1 ≤ n) (c d : ℕ) :
    testMarking n c d (.wild 1) = gThree ^ d := by
  simp only [testMarking, Marking.map_apply, sqMarking_wild, if_neg (fin_one_ne_zero hn),
    collapse_apply]
  simp

/-- **Linearity in the exponents.**  `Marking.map_eval` computes the test marking's value on `R`
from the single element `(sqMarking n).eval R`, for every `(c, d)` at once. -/
theorem testMarking_eval (c d : ℕ) (R : PWord (Generator n)) :
    (testMarking n c d).eval R = collapse c d ((sqMarking n).eval R) :=
  (Marking.map_eval (collapse c d) (sqMarking n) R).symm

/-- The classifying map of the test marking out of the free profinite group, typed at the **plain
carrier instances**.

⚠ The type ascription is load-bearing.  `(… ).hom` elaborates at `profiniteZmodThree`'s bundled
`ProfiniteGrp` instances, while `Marking.map_eval` and `presentationLift` both want the plain
`ZmodThree` ones; the two are defeq but not syntactically equal, so a lemma proved about one form
will not `rw` into a goal stated in the other.  Pinning the type once, here, keeps every
downstream statement on the same instance path. -/
noncomputable def testBaseHom (n c d : ℕ) :
    ContinuousMonoidHom ((FreeProfiniteGroup (Generator n)) : Type) ZmodThree :=
  ((FreeProfiniteGroup.homEquiv (Generator n) profiniteZmodThree).symm
    ⇑(testMarking n c d)).hom

@[simp] theorem testBaseHom_of (c d : ℕ) (g : Generator n) :
    testBaseHom n c d (FreeProfiniteGroup.of g) = testMarking n c d g :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- Pushing the free marking along the classifying map returns the test marking. -/
theorem freeMarking_map_testBaseHom (c d : ℕ) :
    (freeMarking n).map ⇑(testBaseHom n c d) = testMarking n c d := by
  ext g
  exact testBaseHom_of c d g

/-- The tame relator dies because `τ ↦ 1`.  (CB-0's `oddBase_tameRelatorGen`, at the test
marking.) -/
theorem testBaseHom_tameRelatorGen (q c d : ℕ) :
    testBaseHom n c d (tameRelatorGen n q) = 1 := by
  simp only [tameRelatorGen, conjP, map_mul, map_inv, map_pow, testBaseHom_of,
    testMarking_apply_sigma, testMarking_apply_tau]
  group

/-- The `R`-relator's image is the test marking's value on `R`. -/
theorem testBaseHom_eval_R (c d : ℕ) (R : PWord (Generator n)) :
    testBaseHom n c d ((freeMarking n).eval R) = (testMarking n c d).eval R := by
  rw [Marking.map_eval (testBaseHom n c d) (freeMarking n) R, freeMarking_map_testBaseHom]

/-- **The odd quotient of `Γ_R`.**  Whenever the exponents `(c, d)` kill `R`, the test marking
descends to a continuous hom `Γ_R → ℤ/3`. -/
noncomputable def testHom (n q c d : ℕ) (R : PWord (Generator n))
    (hR : (testMarking n c d).eval R = 1) :
    ContinuousMonoidHom ((GammaR n q R) : Type) ZmodThree :=
  presentationLift (gammaRelators n q R) (testBaseHom n c d) <| by
    rintro r (rfl | rfl)
    · exact testBaseHom_tameRelatorGen q c d
    · rw [testBaseHom_eval_R]; exact hR

@[simp] theorem testHom_gammaGen (q c d : ℕ) (R : PWord (Generator n))
    (hR : (testMarking n c d).eval R = 1) (g : Generator n) :
    testHom n q c d R hR (gammaGen n q R g) = testMarking n c d g :=
  (presentationLift_mk _ _ _ (FreeProfiniteGroup.of g)).trans (testBaseHom_of c d g)

end TestMarking

/-! ## §3 The exponent choice — one `𝔽₃`-linear condition in two unknowns

This is the whole content of the refutation, and the reason `R` never matters.  Write
`(sqMarking n).eval R = (u, v)` and `a = log u`, `b = log v` in `𝔽₃`.  §2's linearity says the
test marking kills `R` exactly when `c·a + d·b = 0`.  That is **one** linear condition on
`(c, d) ∈ 𝔽₃²`, so its solution space has dimension `≥ 1` and contains a nonzero vector:
`(b, −a)` when `(a, b) ≠ (0, 0)`, and `(1, 0)` when `(a, b) = (0, 0)`. -/

section Exponents

variable {n : ℕ}

/-- **The choice.**  For every `R` there are exponents `(c, d)` that kill `R` under the test
marking and yet leave `x₀` or `x₁` with nontrivial image. -/
theorem exists_test_exponents (hn : 1 ≤ n) (R : PWord (Generator n)) :
    ∃ c d : ℕ, (testMarking n c d).eval R = 1 ∧
      (testMarking n c d (.wild 0) ≠ 1 ∨ testMarking n c d (.wild 1) ≠ 1) := by
  have key : ∀ c d : ℕ, ((testMarking n c d).eval R = 1 ↔
      (c : ZMod 3) * Multiplicative.toAdd ((sqMarking n).eval R).1
        + (d : ZMod 3) * Multiplicative.toAdd ((sqMarking n).eval R).2 = 0) := by
    intro c d
    rw [testMarking_eval, collapse_eq_one_iff]
  set a := Multiplicative.toAdd ((sqMarking n).eval R).1 with ha
  set b := Multiplicative.toAdd ((sqMarking n).eval R).2 with hb
  by_cases hab : a = 0 ∧ b = 0
  · -- `R` already dies with `x₀ ↦ g`, `x₁ ↦ 1`
    refine ⟨1, 0, (key 1 0).mpr ?_, Or.inl ?_⟩
    · rw [hab.1]; simp
    · rw [testMarking_wild_zero, pow_one]
      exact gThree_ne_one
  · -- otherwise `(b, −a)` is a nonzero solution of the single linear condition
    refine ⟨b.val, (-a).val, (key _ _).mpr ?_, ?_⟩
    · rw [ZMod.natCast_val, ZMod.cast_id, ZMod.natCast_val, ZMod.cast_id]
      ring
    · rcases not_and_or.mp hab with hA | hB
      · refine Or.inr ?_
        rw [testMarking_wild_one hn, ne_eq, gThree_pow_eq_one_iff, ZMod.natCast_val, ZMod.cast_id]
        simpa using hA
      · refine Or.inl ?_
        rw [testMarking_wild_zero, ne_eq, gThree_pow_eq_one_iff, ZMod.natCast_val, ZMod.cast_id]
        exact hB

end Exponents

/-! ## §4 The refutation

`wildPartR` is never pro-`2` once there are two wild letters — for **every** `q` and **every**
`R`.  CB-0's `not_isProP_two_ker_tameOfSpec_one` is the special case `R = 1`. -/

section Refutation

variable {n : ℕ}

/-- **`W_R` is never pro-`2`.**  For every `n ≥ 1`, every `q` and every relator word `R`, the
wild part of `Γ_R` surjects onto a subgroup of `ℤ/3` containing an element of order `3`.

This is the general form of CB-0's `R = 1` counterexample, and it is what makes the five branch
discharges of `hwild` impossible rather than merely unwritten. -/
theorem not_isProP_two_wildPartR (hn : 1 ≤ n) (q : ℕ) (R : PWord (Generator n)) :
    ¬ IsProP 2 (wildPartR n q R) := by
  intro hpro
  obtain ⟨c, d, hR, hne⟩ := exists_test_exponents hn R
  set f := testHom n q c d R hR with hf
  have hp : IsPGroup 2 ↥((wildPartR n q R).map f.toMonoidHom) :=
    Aux.isPGroup_map_of_isProP hpro f.toMonoidHom f.continuous_toFun
  rcases hne with h0 | h1
  · exact not_isPGroup_two_of_mem hp
      ⟨_, gammaGen_wild_mem_wildPartR 0, testHom_gammaGen q c d R hR (.wild 0)⟩ h0
  · exact not_isPGroup_two_of_mem hp
      ⟨_, gammaGen_wild_mem_wildPartR 1, testHom_gammaGen q c d R hR (.wild 1)⟩ h1

/-- **`WordCertificate.hwild` is false**, for every `n ≥ 1`, every `q`, every `R` and *every*
tame-specialization witness.  Uses F3b's `TameSpec.ker_tameOfSpec` (`ker(tameOfSpec) = W_R`)
rather than re-deriving the reduction. -/
theorem not_hwild (hn : 1 ≤ n) {q : ℕ} {R : PWord (Generator n)}
    (hspec : TameSpec.TameSpecializes n q R) :
    ¬ IsProP 2 (TameSpec.tameOfSpec n q R hspec).toMonoidHom.ker := by
  rw [TameSpec.ker_tameOfSpec hspec]
  exact not_isProP_two_wildPartR hn q R

/-- **No `WordCertificate` exists over any of these words.**  `hwild` is one of the seventeen
fields, so the refutation propagates to the record: for `n ≥ 1` the type is empty. -/
theorem isEmpty_wordCertificate (hn : 1 ≤ n) {q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
    {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n} :
    IsEmpty (WordCertificate n q R P hP nuP SN) :=
  ⟨fun W => not_hwild hn W.tameSpecialization W.hwild⟩

end Refutation

/-! ## §5 The five frozen branch families

Every frozen family lives on an alphabet with at least two wild letters — `N`, `Npc`, `M` and
`Mpc` on `Generator (2 + 2h)` and `L` on `Generator (2h + 1)`, and `Generator m` carries `m + 1`
wild letters — so §4 applies verbatim to all five.  Each discharge is `by omega`: there is no
per-family content, because the obstruction does not see the word. -/

section Branches

/-- **Compact `N`** (the `√−2` branch). -/
theorem not_hwild_nCompact {q α h : ℕ}
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q (nCompactW α h)) :
    ¬ IsProP 2 (TameSpec.tameOfSpec (2 + 2 * h) q (nCompactW α h) hspec).toMonoidHom.ker :=
  not_hwild (by omega) hspec

/-- **`L`** (the square branch) — the tightest alphabet, and still two wild letters at `h = 0`. -/
theorem not_hwild_lSq {q h : ℕ}
    (hspec : TameSpec.TameSpecializes (2 * h + 1) q (LSq.lSqW h)) :
    ¬ IsProP 2 (TameSpec.tameOfSpec (2 * h + 1) q (LSq.lSqW h) hspec).toMonoidHom.ker :=
  not_hwild (by omega) hspec

/-- **Non-compact `N`**. -/
theorem not_hwild_npcW {q α r h : ℕ} {e : EtaData}
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q (Npc.npcW α r h e)) :
    ¬ IsProP 2 (TameSpec.tameOfSpec (2 + 2 * h) q (Npc.npcW α r h e) hspec).toMonoidHom.ker :=
  not_hwild (by omega) hspec

/-- **Compact `M`**. -/
theorem not_hwild_mCompact {q α h : ℕ}
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q (MCompact.mCompactW α h)) :
    ¬ IsProP 2
      (TameSpec.tameOfSpec (2 + 2 * h) q (MCompact.mCompactW α h) hspec).toMonoidHom.ker :=
  not_hwild (by omega) hspec

/-- **Non-compact `M`**.  Note that no `1 ≤ α` hypothesis is needed: unlike `tameSpecialization`,
the obstruction is insensitive to the word's parameters. -/
theorem not_hwild_mpcW {q α r p h : ℕ} {η : Mpc.EtaDisplay}
    (hspec : TameSpec.TameSpecializes (2 + 2 * h) q (Mpc.mpcW α r p η h)) :
    ¬ IsProP 2
      (TameSpec.tameOfSpec (2 + 2 * h) q (Mpc.mpcW α r p η h) hspec).toMonoidHom.ker :=
  not_hwild (by omega) hspec

end Branches

/-! ## §6 The pilot: compact `N` at `√−2`

`K = ℚ₂(√−2)`, `α = 2`, `h = 0`, `q_K = 2` — the frozen row of `Words/N0.lean`.

⚠ CB-0's `pilot_tameSpecialization` could not be reused: `Count/Routine.lean` does not currently
compile (see this file's report — the `dyadic` merge left it calling `TameSpecializes` and
`tameOfSpec` at top level, where F3b has since moved them into `namespace TameSpec`).  The pilot
witness is therefore rebuilt here from F3b's `tameSpecializes_of_tau_pow` and N0's own boundary
theorem, which is the same one-liner CB-0's §7 used. -/

section Pilot

/-- The pilot word. -/
noncomputable abbrev pilotW : PWord (Generator (2 + 2 * 0)) := nCompactW 2 0

/-- Gate B at the pilot — CB-0's `pilot_tameSpecialization`, rebuilt against `TameSpec`. -/
theorem pilot_tameSpecialization : TameSpec.TameSpecializes (2 + 2 * 0) 2 pilotW :=
  TameSpec.tameSpecializes_of_tau_pow (by omega) (by decide)
    (eval_killWildLetters_nCompact 2 0 (tameMarking (2 + 2 * 0) 2))

/-- **`hwild` fails at the pilot**, end-to-end: the tame kernel of the `√−2` candidate is not
pro-`2`. -/
theorem pilot_not_hwild :
    ¬ IsProP 2
      (TameSpec.tameOfSpec (2 + 2 * 0) 2 pilotW pilot_tameSpecialization).toMonoidHom.ker :=
  not_hwild_nCompact pilot_tameSpecialization

/-- **No word certificate exists at the pilot.**  The `√−2` row cannot be completed as
`CertificateMain` currently states it. -/
theorem pilot_isEmpty_wordCertificate {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics (2 + 2 * 0)} :
    IsEmpty (WordCertificate (2 + 2 * 0) 2 pilotW P hP nuP SN) :=
  isEmpty_wordCertificate (by omega)

end Pilot

end Count

end GQ2.Dyadic
