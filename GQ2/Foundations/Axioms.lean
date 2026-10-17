/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Foundations.TauCetiInstance
public import GQ2.Dyadic.MarkedRecipBundle
public import GQ2.UnitFiltration
public import GQ2.Dyadic.OrientedTameBundle

@[expose] public section

/-!
# Classical literature inputs: the remaining axioms (census 2)

Every `axiom` in the GQ2 library lives in this file, a rule enforced by `scripts/check_axioms.sh`.
Until 2026-10-17 it held eleven: the nine ℚ₂ inputs of Theorem 1.2 and the two `K`-level inputs of
the dyadic campaign.  The Tau Ceti discharge campaign (`docs/orchestration/tauceti-tickets.md`,
merged into this branch) proved the nine from the Tau Ceti library; they are now theorems and
definitions under their legacy names in `GQ2/Foundations/TauCetiInstance.lean`, with their
statements unchanged, and this file keeps the two that remain:

* **B5-K** `markedRecipAt` — marked local reciprocity over every finite `K/ℚ₂` (AX3;
  owner-approved 2026-07-29).
* **B10-K** `orientedTameQuotientAt` — the oriented tame quotient of `G_K` at `q_K` for every
  finite `K/ℚ₂` (AX4; owner-approved 2026-07-29).

Both are the subject of `docs/dyadic/tauceti-discharge-plan.md`, which proves them from Tau
Ceti's local class field theory at a finite `K` and then deletes this file (census 2 → 0).  Their
docstrings below give the precise statement, source citation, paper cross-reference and encoding
conventions; the dependency table is `docs/dyadic/literature-axioms-dyadic.md`.

References from the paper bibliography:

[1] Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2015.  (NSW)
[7] Serre, *Local Fields*, GTM 67, Springer 1979.
-/

open GQ2.ContCoh

namespace GQ2

/-! ## B5-K — marked local reciprocity over finite `K/ℚ₂` (AX3)

The twelve-field bundle structure `Dyadic.MarkedRecip R K` (reciprocity map into `GalKab K`,
the unramified quotient `ν_ur^K` with its normalization clauses, the level datum `r`, and the
`K(i)`-unramifiedness clause) is defined in `GQ2/Dyadic/MarkedRecipBundle.lean`, together with
its axiom-free derived layer (`χ_K`, `C`, `λ`/`I`/`γ`, the `(r, ε, η)` extraction API and the
field-language bridge), the `K = ⊥` reduction regression `markedRecip_bot_reduces`
(merge-gate-8 evidence: the bottom instance reproduces B5's data), and the synthetic `r = 2`
mock pair mandated by the proposal's §7 R2.  That file quantifies over an arbitrary
`LocalReciprocity`; this axiom instantiates it at B5. -/

/-- **The B5-K axiom (AX3).** Marked local reciprocity for every finite extension `K/ℚ₂`:
local class field theory provides the marked reciprocity bundle over `K`, normalized
compatibly with B5 (`localReciprocity`) through norm functoriality.

Proposal and sign-off: `docs/dyadic/ax3-proposal.md` (statement §2.3); owner-approved at gate
G-AX 2026-07-29 — one axiom, the finite-layer norm-residue clause omitted, extend-not-replace
for B5.  Consumers bind the statement through the derived layer of
`GQ2/Dyadic/MarkedRecipBundle.lean` (F4's branch corollary, MC5, the boundary lane).

Citation (targets owner-approved 2026-07-29; **not yet verified against the cited PDFs**):
NSW [1] Ch. I §5 and Ch. VII §7.1 (functoriality); Serre *Local Fields* [7] Ch. XI §3 (norm
functoriality of the reciprocity map).  Paper: the general-`K` analogue of Lemma 3.5;
`docs/literature-axioms.md` B5-K. -/
axiom markedRecipAt (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] : Dyadic.MarkedRecip localReciprocity K

/-! ## B10-K — the oriented tame quotient of `G_K` at `q_K` (AX4)

The five-clause structure `Dyadic.OrientedTameQuotientK B FF` (normal closed pro-2 wild
subgroup `W`, the quotient identification with `T_{q_K}`, and the two reciprocity
normalization clauses), its derived layer (`tameFK`, maximality via `o2_Tq_eq_bot`,
`W`-uniqueness, `tameCharK` descent, `compatF_K`, the §5 interim binder spellings), and the
`K = ⊥` reduction regression `tameQuotientK_bot_reduces` (with the residue degree `f`
genuinely computed from the filtration — the R2 soundness guard) are defined in
`GQ2/Dyadic/OrientedTameBundle.lean`, quantified over an arbitrary bundle.  This axiom
instantiates it at B5-K's `markedRecipAt` and the unit filtration — the parametrization that
pins the residue degree (a free `f` is inconsistent: `T₂ᵃᵇ = Ẑ` vs `T₄ᵃᵇ = Ẑ × ℤ/3`). -/

/-- **The B10-K axiom (AX4).** The oriented tame quotient of `G_K` at `q_K = 2^{f_K}` for
every finite extension `K/ℚ₂`, marked compatibly with B5-K's reciprocity bundle and
parametrized by the canonical unit filtration (which supplies the residue degree and a
uniformizer).

Proposal and sign-off: `docs/dyadic/ax4-proposal.md` (statement §2.3); owner-approved at gate
G-AX 2026-07-29 — one separate axiom, `DyadicUnitFiltration` parametrization, self-contained
`W` with the compatibility clause omitted, no `Ẑ`-valued tame character.  Note: this axiom's
type mentions `markedRecipAt`, so its consumers also print B5 and B5-K (inherent to the
parametrization).

Citation (targets owner-approved 2026-07-29; **not yet verified against the cited PDFs**):
NSW [1] Ch. VII §7.5, (7.5.3) (Iwasawa) with (7.5.2); Serre *Local Fields* [7] Ch. IV (wild
inertia pro-`p`); Ch. XIII §4 Prop. 13 + corollary.  Paper: the general-`K` analogue of the
B10 interface; `docs/literature-axioms.md` B10-K. -/
axiom orientedTameQuotientAt (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K) :
    Dyadic.OrientedTameQuotientK (markedRecipAt K) FF

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Cor 3.12 = ⟦cor-relativeDemushkin⟧
  * eq. (111) = ⟦eq-SWconvention⟧
  * eq. (13) = ⟦eq-localmarkingorientation⟧
  * eq. (145) = ⟦eq-recursionR5a⟧
  * eq. (93) = ⟦eq-squareclassgraded⟧
  * Lemma 10.1 = ⟦lem-tameframeexhaustion⟧
  * Lemma 3.3 = ⟦lem-o2tame⟧
  * Lemma 3.4 = ⟦lem-standardorientation⟧
  * Lemma 3.5 = ⟦lem-markedinitialform⟧
  * Lemma 3.6 = ⟦lem-peripheralpower⟧ (= lemma 3.7 in current tex)
  * Lemma 6.10 = ⟦lem-middlelayer⟧
  * Lemma 6.11 = ⟦lem-faithfulprojective⟧
  * Lemma 6.13 = ⟦lem-twopointevans⟧
  * Lemma 6.16 = ⟦lem-evensvanish⟧
  * Lemma 6.17 = ⟦lem-shapirodet⟧
  * Prop 1.1 = ⟦prop-markedDem⟧
  * Prop 3.14 = ⟦prop-compatiblemarking⟧
  * Prop 3.2 = ⟦prop-tamequotient⟧
  * Thm 1.1 = ⟦prop-markedDem⟧ [cited as theorem; paper says proposition]
  * Theorem 1.2 = ⟦thm-main⟧
  * Thm 2.5 = ⟦lem-reconstruction⟧ [cited as theorem; paper says lemma]
-/
