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
# The routine `WordCertificate` fields  (dyadic campaign, ticket CB-0)

AS1's `WordCertificate` (`GQ2/Dyadic/CertificateMain.lean:450`) has **17** fields.  CB1's memo
(`docs/dyadic/cb-design.md` §1.1, row 7–10) classified four of them as *routine, unwritten*, and
SD3 left two more (`htame`, `hwild`) as instantiation-side conditions.  This file lands the
routine group, generically where it is generic:

| field | status after this file |
|---|---|
| `tameSpecialization` | **CLOSED** — generic hook (§2) + all five branches instantiated (§7) |
| `tfg` | **CLOSED generically** (§3) |
| `smulZmod2`, `contSMulZmod2`, `htriv` | **CLOSED generically** (§4) |
| `htame` | **CLOSED generically** (§5) — it is F3's `tameOfSpec_surjective`, free |
| `hwild` | **OPEN, and NOT routine** — refuted as a generic statement (§6) |

That is **6 of the 17 fields closed** (`tameSpecialization`, `tfg`, `smulZmod2`, `contSMulZmod2`,
`htriv`, `htame`).  §8 instantiates all of them at the compact-`N`/`√−2` pilot and checks, by
substitution into an arbitrary pilot certificate, that they sit at exactly the field types.  The
remaining eleven are CB-P's pro-2 block (`pro2`, `ker_pro2`, `hpro2`, `compat`), the two landed
word-level fields (`coreRel`, `proTwoWord`), CB-1's four analytic clauses (`exactLifting`,
`stokes`, `scalar`, `determinant`), and `hwild`.

## §1's lemma is the one thing the campaign was actually missing

`CertificateMain.lean:358-362` asserts that all five branches supply `TameSpecializes` "and
`τ^{ω₂} = 1` holds in `T_q` by Lem. 3.1".  The assertion is right and the composition was never
carried out, because packet Lemma 3.1 is landed only in **finite-image** form
(`tqTau_odd_order_map`, `map_tqTau_eq_one_of_isPGroup`, `maxProPMk_tqTau`) and `T_q` is not
finite.  `tqTau_zpowHat_omega2` (§1) is the missing profinite step, and it is the single
load-bearing lemma of this file: every branch's `tameSpecialization` factors through it.

## ⚠ Two findings, recorded for AS2–AS5 and the G3 census

1. **The five branch tame-boundary theorems are not uniform**, contrary to the shape the ticket
   assumed.  `N0`, `L` and `Npc` state the bare value `= t.τ ^ᶻ ω₂`; `M0` states
   `t.τ^ᶻω₂ * eBlock …` and `Mpc` a fourteen-factor word.  What *is* uniform is the weaker
   consequence "`t.τ ^ᶻ ω₂ = 1` ⇒ the word dies", which all five carry (`M0`'s
   `eval_killWildLetters_mCompact_of_tau`, `Mpc`'s `eval_killWildLetters_mpcW_eq_one`).  §2 is
   therefore built on that hook, not on the value form; the value form is offered as a
   convenience route (`tameSpecializes_of_eval_eq_tau_omega2`) for the three branches that have
   it.  **`Mpc` additionally needs `1 ≤ α`** — no other branch does.
2. **`hwild` is not routine** (§6).  It is *false* for general `R` satisfying
   `TameSpecializes`, so no generic proof can exist; `wildPartR_not_isProP_two_of_trivialWord`
   refutes it outright at `R = 1`.  §6 reduces it to `IsProP 2 (wildPartR n q R)` and hands that
   to AS2–AS5 as a genuine per-branch obligation.

## Axiom posture

Every declaration is `sorry`-free and introduces **no axiom**.  Per-headline `#print axioms` are
the **standard three** throughout — this file consumes F3's `TameBoundary` layer, the `Words/*`
branch theorems and Mathlib only, none of which carries a `B`-axiom.

There is exactly one `decide`, in §6's `orderOf_ofAdd_one_zmodThree` (`x ^ 3 = 1` and `x ≠ 1` in
the three-element group `ℤ/3`).  It is a **kernel** `decide` — the campaign's permitted form, and
the same idiom as `Words/Alphabet.lean`'s `orderOf_dvd_eight` on `Multiplicative (ZMod 8)`.

## Sources

Packet `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` Lem. 3.1, Prop. 3.4, §10;
ledger §5.2; `docs/dyadic/cb-design.md` §1.1 (rows 7–10) and §5 (the CB-0 row).
-/

namespace GQ2.Dyadic

namespace Count

open GQ2 GQ2.Dyadic.Words

/-! ## §1 Packet Lemma 3.1, profinite form: `τ^{ω₂} = 1` in `T_q`

F3 landed Lemma 3.1 only after passing to a finite quotient.  The branch words evaluate to
`τ^{ω₂}` *in `T_q` itself*, so the finite-image form does not apply; this section supplies the
profinite step by pushing through every open normal subgroup. -/

section LemmaThreeOne

variable {q : ℕ}

/-- In a finite group an element of odd order is killed by the `2`-primary idempotent `ω₂`.
(`GQ2.Dyadic.NpcJet.zpowHat_omega2_eq_one_of_odd` is the same statement, but `NpcJet` is not in
this file's import closure.) -/
private theorem zpowHat_omega2_eq_one_of_odd' {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] {y : P} (h : Odd (orderOf y)) : y ^ᶻ omega2 = 1 := by
  have h2 : ¬ (2 ∣ orderOf y) := by
    have := Nat.odd_iff.mp h
    omega
  have hexp : omega2Exp (orderOf y) = 0 := by
    simp only [omega2Exp, Nat.factorization_eq_zero_of_not_dvd h2, if_pos]
  rw [zpowHat_omega2, powOmega2, hexp, pow_zero]

/-- **Packet Lemma 3.1, profinite form** — `τ^{ω₂} = 1` in `T_q` for even `q ≠ 0`.

Tame inertia is pro-odd, so the `2`-primary idempotent kills `τ`.  F3's §1 proves this after
mapping to a finite quotient (`tqTau_odd_order_map`); `T_q` is profinite, so the statement about
`T_q` itself needs the extra step, which is the usual one — an element lying in every open normal
subgroup is trivial.

This is the lemma `CertificateMain.lean:362` promises and nothing in the repo supplied: **every
branch's `tameSpecialization` factors through it** (§2). -/
theorem tqTau_zpowHat_omega2 (hq0 : q ≠ 0) (hqe : Even q) : (tqTau q) ^ᶻ omega2 = 1 := by
  refine eq_one_of_forall_mem_openNormalSubgroup fun U => ?_
  haveI : Finite ((Tq q : Type) ⧸ U.toSubgroup) := inferInstance
  set mk : ContinuousMonoidHom ((Tq q : Type)) ((Tq q : Type) ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩ with hmk
  have hpush : mk ((tqTau q) ^ᶻ omega2) = (mk (tqTau q)) ^ᶻ omega2 := map_zpowHat _ _ omega2
  have hodd : Odd (orderOf (mk (tqTau q))) :=
    tqTau_odd_order_map hq0 hqe (QuotientGroup.mk' U.toSubgroup)
  have hone : mk ((tqTau q) ^ᶻ omega2) = 1 := by
    rw [hpush, zpowHat_omega2_eq_one_of_odd' hodd]
  exact (QuotientGroup.eq_one_iff _).mp hone

variable (n : ℕ)

/-- The tame marking's `τ`-letter is `T_q`'s tame generator. -/
@[simp] theorem tameMarking_tau (q : ℕ) : (tameMarking n q).τ = tqTau q := rfl

/-- §1 at the tame marking — the exact hypothesis shape the five branch lanes' `_of_tau` /
`_eq_one` theorems bind. -/
theorem tameMarking_tau_zpowHat_omega2 (hq0 : q ≠ 0) (hqe : Even q) :
    ((tameMarking n q).τ) ^ᶻ omega2 = 1 := by
  rw [tameMarking_tau]
  exact tqTau_zpowHat_omega2 hq0 hqe

end LemmaThreeOne

/-! ## §2 `WordCertificate` field 1 — `tameSpecialization`

`TameSpecializes n q R` is `(tameMarking n q).eval R = 1`.  The generic step is the same for
every branch; only the last mile (which branch theorem to quote) differs. -/

section TameSpecialization

variable {n q : ℕ} {R : PWord (Generator n)}

/-- **The base bridge.**  `tameMarking` is already wild-killed
(`killWildLetters_tameMarking`), so a branch's kill-wild evaluation *is* the ledger's
`specializeTame R`. -/
theorem tameSpecializes_of_killWildLetters
    (h : (Marking.killWildLetters (tameMarking n q)).eval R = 1) : TameSpecializes n q R := by
  rwa [killWildLetters_tameMarking] at h

/-- **The uniform hook.**  All five branch lanes prove "`t.τ ^ᶻ ω₂ = 1` ⇒ the word dies", either
directly (`M0`, `Mpc`) or through their value form (`N0`, `L`, `Npc`).  Feed that implication in
and §1 discharges its hypothesis. -/
theorem tameSpecializes_of_tau_omega2 (hq0 : q ≠ 0) (hqe : Even q)
    (h : ((tameMarking n q).τ) ^ᶻ omega2 = 1 →
      (Marking.killWildLetters (tameMarking n q)).eval R = 1) :
    TameSpecializes n q R :=
  tameSpecializes_of_killWildLetters (h (tameMarking_tau_zpowHat_omega2 n hq0 hqe))

/-- **The value route**, for the three branches (`N0`, `L`, `Npc`) whose tame boundary is the
bare `τ^{ω₂}`. -/
theorem tameSpecializes_of_eval_eq_tau_omega2 (hq0 : q ≠ 0) (hqe : Even q)
    (h : (Marking.killWildLetters (tameMarking n q)).eval R = ((tameMarking n q).τ) ^ᶻ omega2) :
    TameSpecializes n q R :=
  tameSpecializes_of_tau_omega2 hq0 hqe fun hτ => h.trans hτ

end TameSpecialization

/-! ## §3 `WordCertificate` field 8 — `tfg`

FG1's Route-D shape made topological finite generation a record field.  On the arithmetic side
that field is FG1's `absGalK_isTopologicallyFinitelyGenerated`
(`GQ2/Dyadic/FinitelyGeneratedK.lean`, from census axiom B1); on the candidate side it is free,
because `Γ_R` is by construction a continuous quotient of the free profinite group on the finite
alphabet `Generator n`.  This is the exact mechanism of the `ℚ₂` original
`GQ2.Roe.gammaR_topologicallyFinitelyGenerated` — the relators are irrelevant. -/

section Tfg

variable (n q : ℕ) (R : PWord (Generator n))

/-- `Γ_R` is topologically generated by its marked generators `σ, τ, x₀, …, x_n`.  F3's
`topGen_tameGammaR` one level down. -/
theorem topGen_gammaR :
    (Subgroup.closure (Set.range (gammaGen n q R))).topologicalClosure = ⊤ := by
  have h := TopGen.map (f := (gammaMk n q R).toMonoidHom)
    (gammaMk n q R).continuous_toFun (quotientMk_surjective _)
    (TopGen.freeProfiniteGroup (Generator n))
  rwa [← Set.range_comp] at h

/-- **`WordCertificate.tfg`, generically.**  `Generator n` is a `Fintype`, so §3's topological
generating set is finite on the nose. -/
theorem gammaR_topologicallyFinitelyGenerated :
    ∃ s : Finset ((GammaR n q R) : Type),
      (Subgroup.closure (s : Set ((GammaR n q R) : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (gammaGen n q R), ?_⟩
  have hcoe : ((Finset.univ.image (gammaGen n q R) : Finset ((GammaR n q R) : Type)) :
      Set ((GammaR n q R) : Type)) = Set.range (gammaGen n q R) := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  rw [hcoe]
  exact topGen_gammaR n q R

end Tfg

/-! ## §4 `WordCertificate` fields 9–11 — the scalar-action trio

`Aut(𝔽₂) = 1`, so there is exactly one action and it is trivial.  Stated over an arbitrary
monoid rather than over `Γ_R`, because nothing about `Γ_R` is used; the `ℚ₂` originals are
`GQ2.RStageGammaR.instDistribMulActionGammaR` / `.htriv_gammaR`, which are per-group. -/

section Scalar

/-- **`WordCertificate.smulZmod2`, generically.**  The unique — hence trivial — action of any
monoid on `𝔽₂`.  Deliberately a `def` and not an `instance`: `SourceDataN`/`WordCertificate`
carry the action as *data*, and registering a global instance on every monoid would shadow the
genuine `ZMod 2`-module structures the `(140)` layer builds. -/
@[reducible] def trivialSMulZmodTwo (M : Type*) [Monoid M] : DistribMulAction M (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- **`WordCertificate.contSMulZmod2`, generically.**  The action is the second projection. -/
theorem trivialContSMulZmodTwo (M : Type*) [Monoid M] [TopologicalSpace M] :
    letI := trivialSMulZmodTwo M; ContinuousSMul M (ZMod 2) := by
  letI := trivialSMulZmodTwo M
  exact ⟨continuous_snd⟩

/-- **`WordCertificate.htriv`, generically.**  Definitional. -/
theorem trivialHtrivZmodTwo (M : Type*) [Monoid M] :
    letI := trivialSMulZmodTwo M; ∀ (γ : M) (m : ZMod 2), γ • m = m :=
  fun _ _ => rfl

end Scalar

/-! ## §5 `WordCertificate` field 16 — `htame`

SD3's first §10 instantiation-side condition, and the one field of the group that costs nothing:
AS1's `tameOfSpec_surjective` proves it outright, for every `n`, `q` and `R`.  Named here so
AS2–AS5 have a handle with the field's spelling. -/

section Htame

variable {n q : ℕ} {R : PWord (Generator n)}

/-- **`WordCertificate.htame`, generically** — F3's `tameR_surjective` at AS1's satisfiable
hypothesis.  `Γ_R ↠ T_q` because `σ, τ` are already in the image and the image is closed. -/
theorem htame_of_tameSpecializes (hspec : TameSpecializes n q R) :
    Function.Surjective (tameOfSpec n q R hspec) :=
  tameOfSpec_surjective hspec

end Htame

/-! ## §6 `WordCertificate` field 17 — `hwild` is **NOT routine**

⚠ **The finding.**  `hwild : IsProP 2 (tameOfSpec n q R _).toMonoidHom.ker` is *false* for general
`R` satisfying `TameSpecializes`, so **no generic proof can exist** and CB1's sizing for it (if it
was ever grouped with the routine four) is wrong.  §6 proves the refutation rather than asserting
it, so that AS2–AS5 do not spend a lane looking for the generic lemma.

**The witness is the trivial word `R = 1`.**  `TameSpecializes n q 1` holds on the nose, but
`Γ_1 = ⟨σ, τ, x₀, …, x_n ∣ τ^σ = τ^q⟩` admits the continuous surjection onto `ℤ/3` sending every
wild letter to a generator and `σ, τ ↦ 1`; the wild letters lie in `ker(tame)`, whose image is
therefore not a `2`-group.

**What is actually owed, per branch.**  The `ℚ₂` precedents are all substantial or axiomatic:
at `G_ℚ₂` pro-`2`-ness of wild inertia is the **census axiom** (`TameQuotientData.isProP`, through
the B10 bundle); at `G_K` it is a *structure field* of `OrientedTameQuotientK` (AX4); and for the
`ℚ₂` candidates `Γ_A`/`Γ_R` it is `GQ2.isProP_wildCore` / `GQ2.isProP_wildCoreR`
(`GQ2/AdmissibleLimit.lean:375`, `GQ2/Roe/AdmissibleLimit.lean:231`) — ~80-line admissible-limit
compactness arguments keyed to the specific relator families `N_A`/`N_R` and their
`Marking.Pro2Core` clause.  Generalizing that argument to `gammaRelators n q R` is the honest
shape of the obligation, and it is per-relator-family, not generic.

**The missing reduction.**  `IsProP 2 (ker tameOfSpec) ↔ IsProP 2 (wildPartR n q R)` needs
`ker_tameOfSpec`, i.e. F3's `ker_tameR` (`TameBoundary.lean:534`) re-done at `TameSpecializes`.
That is left to **F3b**, which is rebuilding the Gate-B interface in `TameBoundary.lean` anyway;
duplicating it here would collide with that landing. -/

section Hwild

variable {n q : ℕ}

/-- The trivial word satisfies the ledger's tame equation on the nose. -/
theorem tameSpecializes_one (n q : ℕ) : TameSpecializes n q .one :=
  Marking.eval_one _

/-- The odd test marking: every wild letter goes to a generator of `ℤ/3`, `σ` and `τ` die. -/
noncomputable def oddMarking (n : ℕ) : Marking n ZmodThree :=
  Marking.ofLetters 1 1 (fun _ => Multiplicative.ofAdd 1)

/-- Its classifying map out of the free profinite group. -/
noncomputable def oddBase (n : ℕ) : FreeProfiniteGroup (Generator n) ⟶ profiniteZmodThree :=
  (FreeProfiniteGroup.homEquiv (Generator n) profiniteZmodThree).symm ⇑(oddMarking n)

@[simp] theorem oddBase_of (n : ℕ) (g : Generator n) :
    (oddBase n).hom.toMonoidHom (FreeProfiniteGroup.of g) = oddMarking n g :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem oddMarking_sigma (n : ℕ) : oddMarking n .sigma = 1 := rfl

@[simp] theorem oddMarking_tau (n : ℕ) : oddMarking n .tau = 1 := rfl

/-- The tame relator dies because `τ ↦ 1`.  F3's `tameBase_tameRelatorGen`, restated. -/
theorem oddBase_tameRelatorGen (n q : ℕ) :
    (oddBase n).hom.toMonoidHom (tameRelatorGen n q) = 1 := by
  simp only [tameRelatorGen, conjP, map_mul, map_inv, map_pow, oddBase_of, oddMarking_sigma,
    oddMarking_tau]
  -- `group` normalizes at the `ProfiniteGrp`-carrier instance, where `simp`'s `one_pow` does not
  -- match; it leaves the single `zpow` obligation.
  group
  exact one_zpow _

/-- **The odd quotient of `Γ_1`.**  `σ, τ ↦ 1` and `x_i ↦ 1 ∈ ℤ/3`: the tame relator dies because
`τ ↦ 1`, and the wild relator is the empty word. -/
noncomputable def oddHom (n q : ℕ) :
    ContinuousMonoidHom ((GammaR n q .one) : Type) ZmodThree :=
  presentationLift (gammaRelators n q .one) (oddBase n).hom <| by
    rintro r (rfl | rfl)
    · exact oddBase_tameRelatorGen n q
    · rw [show (freeMarking n).eval (PWord.one : PWord (Generator n)) = 1 from Marking.eval_one _,
        map_one]

/-- A generator of `ℤ/3` has order `3` — kernel `decide` on a three-element group. -/
theorem orderOf_ofAdd_one_zmodThree : orderOf (Multiplicative.ofAdd (1 : ZMod 3)) = 3 := by
  have h3 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ 3 = 1 := by decide
  have h1 : (Multiplicative.ofAdd (1 : ZMod 3)) ≠ 1 := by decide
  rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ (orderOf_dvd_of_pow_eq_one h3) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) h1
  · exact h

@[simp] theorem oddHom_gammaGen (n q : ℕ) (g : Generator n) :
    oddHom n q (gammaGen n q .one g) = oddMarking n g :=
  (presentationLift_mk _ _ _ (FreeProfiniteGroup.of g)).trans (oddBase_of n g)

/-- **`hwild` is not generic.**  At the trivial word the tame kernel maps onto `ℤ/3`, so it is
not pro-`2` — even though `TameSpecializes` holds.  Hence there is no proof of
`WordCertificate.hwild` uniform in `R`, and each branch owes its own. -/
theorem not_isProP_two_ker_tameOfSpec_one (n q : ℕ) :
    ¬ IsProP 2 (tameOfSpec n q .one (tameSpecializes_one n q)).toMonoidHom.ker := by
  intro hpro
  set K := (tameOfSpec n q (.one : PWord (Generator n)) (tameSpecializes_one n q)).toMonoidHom.ker
    with hK
  -- the wild letter `x₀` lies in the tame kernel, because the tame marking kills it
  have hmem : gammaGen n q .one (.wild 0) ∈ K := by
    rw [hK, MonoidHom.mem_ker]
    exact tameOfSpec_gammaGen (tameSpecializes_one n q) (.wild 0)
  -- ... and its image under `oddHom` generates `ℤ/3`
  have himg : Multiplicative.ofAdd (1 : ZMod 3) ∈ K.map (oddHom n q).toMonoidHom :=
    ⟨_, hmem, oddHom_gammaGen n q (.wild 0)⟩
  have hp : IsPGroup 2 ↥(K.map (oddHom n q).toMonoidHom) :=
    Aux.isPGroup_map_of_isProP hpro (oddHom n q).toMonoidHom (oddHom n q).continuous_toFun
  obtain ⟨k, hk⟩ := hp ⟨_, himg⟩
  -- a `2`-power kills a generator of `ℤ/3`, so `3 ∣ 2 ^ k`
  have hk1 : (Multiplicative.ofAdd (1 : ZMod 3)) ^ (2 ^ k) = 1 :=
    congrArg Subtype.val hk
  have hdvd : (3 : ℕ) ∣ 2 ^ k := by
    have hd := orderOf_dvd_of_pow_eq_one hk1
    rwa [orderOf_ofAdd_one_zmodThree] at hd
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

end Hwild

/-! ## §7 The five branch instantiations of `tameSpecialization`

⚠ The branch theorems are **not** uniform (module docstring, finding 1).  `N0`, `L` and `Npc` go
through the value route; `M0` and `Mpc` through the `_of_tau` hook, and `Mpc` alone needs
`1 ≤ α`. -/

section Branches

variable {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)

include hq0 hqe in
/-- **Compact `N`** (the `√−2` branch). -/
theorem tameSpecializes_nCompact (α h : ℕ) : TameSpecializes (2 + 2 * h) q (nCompactW α h) :=
  tameSpecializes_of_eval_eq_tau_omega2 hq0 hqe
    (eval_killWildLetters_nCompact α h (tameMarking (2 + 2 * h) q))

include hq0 hqe in
/-- **`L`** (the square branch). -/
theorem tameSpecializes_lSq (h : ℕ) : TameSpecializes (2 * h + 1) q (LSq.lSqW h) :=
  tameSpecializes_of_eval_eq_tau_omega2 hq0 hqe
    (LSq.eval_killWildLetters_lSq h (tameMarking (2 * h + 1) q))

include hq0 hqe in
/-- **Non-compact `N`**. -/
theorem tameSpecializes_npcW (α r h : ℕ) (e : EtaData) :
    TameSpecializes (2 + 2 * h) q (Npc.npcW α r h e) :=
  tameSpecializes_of_eval_eq_tau_omega2 hq0 hqe
    (Npc.eval_killWildLetters_npcW α r h e (tameMarking (2 + 2 * h) q))

include hq0 hqe in
/-- **Compact `M`** — via the `_of_tau` hook, since its tame boundary is `τ^{ω₂} · eBlock …`. -/
theorem tameSpecializes_mCompact (α h : ℕ) :
    TameSpecializes (2 + 2 * h) q (MCompact.mCompactW α h) :=
  tameSpecializes_of_tau_omega2 hq0 hqe
    (MCompact.eval_killWildLetters_mCompact_of_tau α h (tameMarking (2 + 2 * h) q))

include hq0 hqe in
/-- **Non-compact `M`** — the `_of_tau` hook again, and the only branch needing `1 ≤ α`. -/
theorem tameSpecializes_mpcW {α : ℕ} (hα : 1 ≤ α) (r p : ℕ) (η : Mpc.EtaDisplay) (h : ℕ) :
    TameSpecializes (2 + 2 * h) q (Mpc.mpcW α r p η h) :=
  tameSpecializes_of_tau_omega2 hq0 hqe
    (Mpc.eval_killWildLetters_mpcW_eq_one hα r p η (tameMarking (2 + 2 * h) q))

end Branches

/-! ## §8 The pilot: compact `N` at `√−2`

`K = ℚ₂(√−2)` is ramified of degree `2`, so `f = 1` and `q_K = 2`; the frozen row is
`α = 2, h = 0` (`Words/N0.lean`'s `branchData_sqrtNegTwo`), on the alphabet `Generator 2`.
Everything CB-0 owns is instantiated here at exactly the `WordCertificate` field types. -/

section Pilot

/-- The pilot word. -/
noncomputable abbrev pilotW : PWord (Generator (2 + 2 * 0)) := nCompactW 2 0

/-- Field 1 at the pilot. -/
theorem pilot_tameSpecialization : TameSpecializes (2 + 2 * 0) 2 pilotW :=
  tameSpecializes_nCompact (by omega) (by decide) 2 0

/-- Field 8 at the pilot. -/
theorem pilot_tfg :
    ∃ s : Finset ((GammaR (2 + 2 * 0) 2 pilotW) : Type),
      (Subgroup.closure (s : Set ((GammaR (2 + 2 * 0) 2 pilotW) : Type))).topologicalClosure = ⊤ :=
  gammaR_topologicallyFinitelyGenerated _ _ _

/-- Fields 9–11 at the pilot. -/
@[reducible] noncomputable def pilot_smulZmod2 :
    DistribMulAction ↥(GammaR (2 + 2 * 0) 2 pilotW) (ZMod 2) :=
  trivialSMulZmodTwo _

theorem pilot_contSMulZmod2 :
    letI := pilot_smulZmod2; ContinuousSMul ↥(GammaR (2 + 2 * 0) 2 pilotW) (ZMod 2) :=
  trivialContSMulZmodTwo _

theorem pilot_htriv :
    letI := pilot_smulZmod2;
    ∀ (γ : ↥(GammaR (2 + 2 * 0) 2 pilotW)) (m : ZMod 2), γ • m = m :=
  trivialHtrivZmodTwo _

/-- Field 16 at the pilot. -/
theorem pilot_htame :
    Function.Surjective (tameOfSpec (2 + 2 * 0) 2 pilotW pilot_tameSpecialization) :=
  htame_of_tameSpecializes _

/-- **The acceptance check.**  Substituting this file's terms for the corresponding fields of an
arbitrary pilot word certificate again yields a word certificate.  That this elaborates is the
real verification: `tameSpecialization` is *depended on* by `compat`, `determinant`, `htame` and
`hwild`, so the substitution only typechecks if CB-0's term sits at exactly the field's type.

⚠ The scalar trio cannot be substituted the same way and this is **not** a defect in §4:
`smulZmod2` is *data*, and `stokes`/`scalar`/`determinant` are stated **under** it, so swapping it
would require transporting those three clauses.  Every action on `𝔽₂` is trivial, so the transport
is real but content-free; it belongs to whichever ticket first builds a certificate outright.
`pilot_smulZmod2`/`pilot_contSMulZmod2`/`pilot_htriv` are each stated at the field's verbatim
type. -/
noncomputable def pilotSubstitute {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics (2 + 2 * 0)}
    (W : WordCertificate (2 + 2 * 0) 2 pilotW P hP nuP SN) :
    WordCertificate (2 + 2 * 0) 2 pilotW P hP nuP SN :=
  { W with
    tameSpecialization := pilot_tameSpecialization
    tfg := pilot_tfg
    htame := pilot_htame }

end Pilot

end Count

end GQ2.Dyadic
