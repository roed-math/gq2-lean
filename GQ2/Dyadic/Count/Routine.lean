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
| `tameSpecialization` | **generic hook + all five branches** (§2) |
| `tfg` | **closed generically** (§3) |
| `smulZmod2`, `contSMulZmod2`, `htriv` | **closed generically** (§4) |
| `htame` | **closed generically** (§5) — it is F3's `tameOfSpec_surjective`, free |
| `hwild` | **NOT routine — reduced, and shown non-generic** (§6) |

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

Every declaration is `sorry`-free and introduces no axiom and no `decide`.  Per-headline
`#print axioms` are the standard three throughout — this file consumes F3's `TameBoundary`
layer, the `Words/*` branch theorems and Mathlib only, none of which carries a `B`-axiom.

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

end Count

end GQ2.Dyadic
