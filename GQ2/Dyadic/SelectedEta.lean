/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.SelectedWords

/-!
# The field-unit to selected-word display seam

`BranchData.Npc` and `.Mpc` carry an arbitrary unit `eta : Z_2^*`, whereas the frozen word
constructors carry certificate display data (`EtaData` or `EtaDisplay`).  This file makes the
interface explicit and separates three notions:

1. a display represents the field unit (equality of its profinite exponent with `etaHatZ eta`);
2. the semantic arbitrary-unit word evaluates like the displayed frozen word;
3. literal equality of word syntax, which is stronger and is asserted only where it is true.

For `Npc`, every display word already uses a genuine `profPow`, so compatible exponents give
literal equality with the semantic word.  For `Mpc`, `.one` and `.lit` are deliberately different
syntax from a `profPow`; compatible displays therefore give evaluation equality, not literal
word equality.  Instantiating that equality at the tautological marking of the free profinite
group nevertheless identifies the actual relator elements.  The final section proves that this
preserves the relator set, its closed normal closure, the admissible-limit kernel `NR`, and hence
both `GammaBare` and the campaign's corrected `GammaR`.

The packages `NpcDisplayFor` and `MpcDisplayFor` also carry the certificate well-formedness
condition.  They need not exist for every `2`-adic unit: `EtaData` is a rational display, while a
general element of `Z_2^*` need not be rational.  The semantic constructors remain available for
every unit regardless.
-/

namespace GQ2.Dyadic

open GQ2

/-! ## Exact compatibility of display data with a field unit -/

/-- **Every `2`-adic unit is `1` modulo `2`.**  The residue map `ℤ_[2] → ZMod 2` sends a unit to
a unit, and `ZMod 2` has only the unit `1`; so `η - 1` lies in the maximal ideal `(2)`.

This is the arithmetic content the procyclic-`N` scalar sub-branch consumes.  A bare `EtaData` is
an arbitrary pair of integers and supplies nothing of the kind — `NProcyclicUnram`'s left-kernel
witness `heisEta1_npc_scalarNormal_kernel` shows the sub-branch is *false* without it — but every
`NpcDisplayFor` carries a genuine field unit, so at the selection seam the hypothesis is free. -/
theorem exists_padicUnit_eq_one_add_two_mul (eta : ℤ_[2]ˣ) :
    ∃ z : ℤ_[2], (eta : ℤ_[2]) = 1 + 2 * z := by
  have hmul : PadicInt.toZMod ((eta : ℤ_[2]) * (↑eta⁻¹ : ℤ_[2])) = 1 := by
    rw [eta.mul_inv, map_one]
  have hone : PadicInt.toZMod (eta : ℤ_[2]) = 1 := by
    rw [map_mul] at hmul
    revert hmul
    generalize (PadicInt.toZMod (eta : ℤ_[2]) : ZMod 2) = a
    generalize (PadicInt.toZMod (↑eta⁻¹ : ℤ_[2]) : ZMod 2) = b
    revert a b
    decide
  have hker : ((eta : ℤ_[2]) - 1) ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [RingHom.mem_ker, map_sub, hone, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨z, ?_⟩
  push_cast at hz
  rwa [sub_eq_iff_eq_add'] at hz

namespace EtaData

/-- A rational `EtaData` display represents a `2`-adic unit when its denoted `2`-adic value is
exactly that unit. -/
def RepresentsUnit (d : EtaData) (eta : ℤ_[2]ˣ) : Prop := d.toPadic = (eta : ℤ_[2])

theorem toZhat_eq_etaHatZ {d : EtaData} {eta : ℤ_[2]ˣ} (h : d.RepresentsUnit eta) :
    d.toZhat = etaHatZ (eta : ℤ_[2]) := by
  rw [EtaData.toZhat, h]

@[simp] theorem one_representsUnit : (EtaData.mk 1 1).RepresentsUnit (1 : ℤ_[2]ˣ) := by
  rw [RepresentsUnit, EtaData.one_toPadic, Units.val_one]

end EtaData

namespace Words.Mpc.EtaDisplay

/-- An `Mpc` certificate display represents a field unit when its denoted profinite exponent is
the unit's canonical lift `etaHatZ`.  This is exponent equality; it is intentionally not equality
of the display's `PWord` syntax. -/
def RepresentsUnit (d : EtaDisplay) (eta : ℤ_[2]ˣ) : Prop :=
  d.zhat = etaHatZ (eta : ℤ_[2])

@[simp] theorem one_representsUnit : (EtaDisplay.one).RepresentsUnit (1 : ℤ_[2]ˣ) := by
  rw [RepresentsUnit, EtaDisplay.zhat, Units.val_one, GQ2.Dyadic.etaHatZ_one]

/-- A genuine `.hat` display inherits compatibility from its underlying `EtaData`. -/
theorem hat_representsUnit {d : EtaData} {eta : ℤ_[2]ˣ} (h : d.RepresentsUnit eta) :
    (EtaDisplay.hat d.num d.den).RepresentsUnit eta := by
  show d.toZhat = etaHatZ (eta : ℤ_[2])
  exact EtaData.toZhat_eq_etaHatZ h

end Words.Mpc.EtaDisplay

/-- A well-formed `Npc` certificate display for the field unit `eta`. -/
structure NpcDisplayFor (eta : ℤ_[2]ˣ) where
  data : EtaData
  num_odd : data.num % 2 ≠ 0
  den_odd : data.den % 2 ≠ 0
  represents : data.RepresentsUnit eta

namespace NpcDisplayFor

/-- The canonical display package at `eta = 1`. -/
def one : NpcDisplayFor (1 : ℤ_[2]ˣ) where
  data := ⟨1, 1⟩
  num_odd := by norm_num
  den_odd := by norm_num
  represents := EtaData.one_representsUnit

/-- **The selected `Npc` display denotes a `2`-adic unit, hence is `1 + 2z`.**

This is the exact `(z, hd)` pair required by `NProcyclicUnram.scalarActionImageStokes` and
therefore by `NProcyclicUnram.uniformPushedHsimp`.  Discharging it here — at the seam where the
campaign actually selects `η` — is what makes the procyclic-`N` uniform Stokes residue, and every
consumer restated over it, unconditional on the selected row: `RepresentsUnit` says the display
denotes the branch's field unit, and `exists_padicUnit_eq_one_add_two_mul` does the rest.  The
oddness side conditions `num_odd`/`den_odd` are not used. -/
theorem exists_toPadic_eq_one_add_two_mul {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) :
    ∃ z : ℤ_[2], d.data.toPadic = 1 + 2 * z := by
  obtain ⟨z, hz⟩ := exists_padicUnit_eq_one_add_two_mul eta
  exact ⟨z, by rw [show d.data.toPadic = (eta : ℤ_[2]) from d.represents]; exact hz⟩

end NpcDisplayFor

/-- A well-formed `Mpc` certificate display for the field unit `eta`. -/
structure MpcDisplayFor (eta : ℤ_[2]ˣ) where
  display : Words.Mpc.EtaDisplay
  wf : display.wfB = true
  represents : display.RepresentsUnit eta

namespace MpcDisplayFor

/-- The canonical display package at `eta = 1`. -/
def one : MpcDisplayFor (1 : ℤ_[2]ˣ) where
  display := .one
  wf := rfl
  represents := Words.Mpc.EtaDisplay.one_representsUnit

/-- A well-formed `Npc` rational display can be reused as a genuine `.hat` display for `Mpc`.
This is the case in which both rows literally carry the same `etaHat` exponent node. -/
def ofNpc {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) : MpcDisplayFor eta where
  display := .hat d.data.num d.data.den
  wf := by simp [Words.Mpc.EtaDisplay.wfB, d.num_odd, d.den_odd]
  represents := Words.Mpc.EtaDisplay.hat_representsUnit d.represents

end MpcDisplayFor

/-! ## Semantic arbitrary-unit `Npc` word -/

namespace Words.Npc

/-- The `Npc` conjugator at an arbitrary profinite exponent. -/
noncomputable def aWAt (h : ℕ) (gamma : Zhat) : PWord (Generator (2 + 2 * h)) :=
  .profPow (.gen .sigma) gamma

/-- The compressed correction block at an arbitrary profinite exponent. -/
noncomputable def dBlockWAt (h r : ℕ) (gamma : Zhat) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.conj (deltaZeroW h) (aWAt h gamma),
     .conj (PWord.prodList [deltaZeroW h, .conj (deltaZeroW h) (aWAt h gamma)])
       (.inv (bW h r))]

/-- The `Npc` correction commutator at an arbitrary profinite exponent. -/
noncomputable def eBlockWAt (h r : ℕ) (gamma : Zhat) : PWord (Generator (2 + 2 * h)) :=
  .comm (dBlockWAt h r gamma) (.gen (coreLetter h 1))

/-- The corrected `Npc` word parametrized directly by its profinite exponent. -/
noncomputable def npcWAt (alpha r h : ℕ) (gamma : Zhat) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.zpow (.gen (coreLetter h 0)) (2 + 2 ^ alpha),
     .comm (.gen (coreLetter h 0)) (aWAt h gamma),
     .inv (.conj (.gen (coreLetter h 2))
       (PWord.prodList [.gen (coreLetter h 1), bW h r])),
     PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
     eBlockWAt h r gamma,
     handlesW h]

/-- Regression to the unchanged frozen constructor on an `EtaData` exponent. -/
@[simp] theorem npcWAt_etaData (alpha r h : ℕ) (d : EtaData) :
    npcWAt alpha r h d.toZhat = npcW alpha r h d := rfl

/-- The semantic corrected `Npc` word attached directly to an arbitrary field unit. -/
noncomputable def npcWUnit (alpha r h : ℕ) (eta : ℤ_[2]ˣ) :
    PWord (Generator (2 + 2 * h)) :=
  npcWAt alpha r h (etaHatZ (eta : ℤ_[2]))

/-- For `Npc`, a compatible display gives literal equality of `PWord`s, because both sides use
the same genuine `profPow` syntax. -/
theorem npcWUnit_eq_display (alpha r h : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) :
    npcWUnit alpha r h eta = npcW alpha r h d.data := by
  rw [npcWUnit, ← EtaData.toZhat_eq_etaHatZ d.represents, npcWAt_etaData]

end Words.Npc

/-! ## Semantic arbitrary-unit `Mpc` word -/

namespace Words.Mpc

/-- The linear-copy factor list with the `D` letter supplied semantically. -/
noncomputable def linFactorsAt (alpha r p h : ℕ) (D : PWord (Generator (2 + 2 * h))) :
    List (PWord (Generator (2 + 2 * h))) :=
  [.zpow (aW h (s r) (m alpha)) ((2 : ℕ) : ℤ),
   .comm (aW h (s r) (m alpha)) (bW h p),
   .zpow (c0W h (s r)) ((2 ^ alpha : ℕ) : ℤ),
   .comm (c0W h (s r)) D,
   e01W h (p + s r * m alpha) (s r * m alpha),
   e2W h (s r) (m alpha) p]

/-- The hat-copy factor list with the `D` letter supplied semantically. -/
noncomputable def hatFactorsAt (alpha r p h : ℕ) (D : PWord (Generator (2 + 2 * h))) :
    List (PWord (Generator (2 + 2 * h))) :=
  [.zpow (aHatW h (s r) (m alpha)) ((2 : ℕ) : ℤ),
   .comm (aHatW h (s r) (m alpha)) (bHatW h p),
   .zpow (c0HatW h (s r)) ((2 ^ alpha : ℕ) : ℤ),
   .comm (c0HatW h (s r)) D,
   e01W h (p + s r * m alpha) (s r * m alpha)]

/-- The selected `Mpc` word with an arbitrary semantic `D` letter. -/
noncomputable def mpcWAt (alpha r p h : ℕ) (D : PWord (Generator (2 + 2 * h))) :
    PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    (linFactorsAt alpha r p h D ++ hatFactorsAt alpha r p h D ++
      [.zpow (dW h 0) ((2 : ℕ) : ℤ), .comm (dW h 0) (dW h 1)] ++ handleTailW h)

/-- Regression to the unchanged frozen constructor on its exact displayed `D` letter. -/
@[simp] theorem mpcWAt_etaDisplay (alpha r p : ℕ) (d : EtaDisplay) (h : ℕ) :
    mpcWAt alpha r p h d.toPWord = mpcW alpha r p d h := rfl

/-- The semantic selected `Mpc` word attached directly to an arbitrary field unit. -/
noncomputable def mpcWUnit (alpha r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ) :
  PWord (Generator (2 + 2 * h)) :=
  mpcWAt alpha r p h (.profPow (.gen .sigma) (etaHatZ (eta : ℤ_[2])))

/-- Evaluation of `mpcWAt` depends on the semantic value of `D`, not its syntax. -/
theorem eval_mpcWAt_congr {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] {h : ℕ} (t : Marking (2 + 2 * h) G)
    (alpha r p : ℕ) {D D' : PWord (Generator (2 + 2 * h))} (hD : t.eval D = t.eval D') :
    t.eval (mpcWAt alpha r p h D) = t.eval (mpcWAt alpha r p h D') := by
  rw [mpcWAt, mpcWAt, eval_prodListM, eval_prodListM]
  simp only [linFactorsAt, hatFactorsAt, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, meval_comm, hD]

/-! ### The semantic pro-`2` boundary

Unlike the display comparison above, this statement needs no rational display for `eta`.  It
computes the semantic `.profPow` node directly, so it applies to every `2`-adic unit and keeps
the complete handle block. -/

/-- **Gate C for the semantic arbitrary-unit `Mpc` word, at every handle count.** -/
theorem eval_pro2_mpcWUnit {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {alpha : ℕ} (halpha : 1 ≤ alpha) (r p : ℕ) (eta : ℤ_[2]ˣ) (h : ℕ)
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (mpcWUnit alpha r p eta h))
      = MarkedCore.mWord alpha
          ((t (coreLetter h 0))⁻¹ * ((t (coreLetter h 2) * t.σ ^ s r) ^ m alpha)⁻¹)
          (t (coreLetter h 1) * t.σ ^ p)
          (t (coreLetter h 2) * t.σ ^ s r)
          (t.σ ^ᶻ etaHatZ (eta : ℤ_[2]))
        * MarkedCore.handleWord (fun j ↦ t (handleU j)) (fun j ↦ t (handleV j)) := by
  have heta :
      t.eval (pro2 (.profPow (.gen .sigma) (etaHatZ (eta : ℤ_[2]))))
        = t.σ ^ᶻ etaHatZ (eta : ℤ_[2]) := by
    rw [pro2_profPow_of_ne _ (Npc.etaHatZ_ne_omega2 (eta : ℤ_[2]))]
    rfl
  have htail : (((handleTailW h).map pro2).map (t.eval ·)).prod
      = t.eval (pro2 (handlesW h)) := by
    match h with
    | 0 => simp [handleTailW, handlesW]
    | h + 1 => simp [handleTailW]
  rw [mpcWUnit, mpcWAt, pro2_prodList, eval_prodListM, List.map_append,
    List.map_append, List.map_append, List.map_append, List.map_append, List.map_append,
    List.prod_append, List.prod_append, List.prod_append, htail]
  simp only [linFactorsAt, hatFactorsAt, List.map_cons, List.map_nil, pro2_zpow, pro2_comm,
    List.prod_cons, List.prod_nil, meval_zpow, meval_comm, mul_one, eval_pro2_aW,
    eval_pro2_bW, eval_pro2_c0W, eval_pro2_e01W, eval_pro2_e2W, eval_pro2_aHatW,
    eval_pro2_bHatW, eval_pro2_c0HatW, heta, eval_pro2_dW, one_zpow, commR_one_left,
    pro2_handlesW, eval_handlesW]
  rw [commR_eq_one_iff.mpr
      (((Commute.refl t.σ).pow_pow (s r * m alpha) p).inv_left),
    commR_eq_one_iff.mpr
      (commute_pow_zpowHat t.σ (s r) (etaHatZ (eta : ℤ_[2])))]
  simp only [zpow_natCast, one_mul, mul_one]
  rw [← pow_mul, s_mul_two_pow halpha r, mul_comm 2 (s r * m alpha), pow_mul]
  rw [MarkedCore.mWord]
  simp only [commR, GQ2.commP, mul_assoc]
  group

/-- A compatible `Mpc` display evaluates exactly like the semantic arbitrary-unit word.  This
does not claim literal word equality for `.one` or `.lit`. -/
theorem eval_mpcWUnit_eq_display {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {h : ℕ} (t : Marking (2 + 2 * h) G) (alpha r p : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    t.eval (mpcWUnit alpha r p eta h) = t.eval (mpcW alpha r p d.display h) := by
  rw [mpcWUnit, ← mpcWAt_etaDisplay alpha r p d.display h]
  apply eval_mpcWAt_congr t alpha r p
  rw [eval_etaDisplay, d.represents]
  rfl

/-- With a genuine `.hat` display, compatible exponents also give literal word equality. -/
theorem mpcWUnit_eq_hatDisplay (alpha r p h : ℕ) {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) :
    mpcWUnit alpha r p eta h =
      mpcW alpha r p (.hat d.data.num d.data.den) h := by
  rw [mpcWUnit, ← EtaData.toZhat_eq_etaHatZ d.represents]
  rfl

end Words.Mpc

/-! ## Invariance of the presented group under free-relator equality

The presentation API consumes the value of a `PWord` in the tautologically marked free profinite
group, not the syntax tree itself.  Therefore universal equality after profinite evaluation is
strictly more than is needed: its single `freeMarking` instance identifies the relator elements.
The following lemmas record the resulting invariant once, independently of the `Mpc` formulas.
-/

/-- Equal `PWord` values at the tautological marking give the same two-element relator set. -/
theorem gammaRelators_eq_of_freeMarking_eval_eq {n q : ℕ} {R S : PWord (Generator n)}
    (h : (freeMarking n).eval R = (freeMarking n).eval S) :
    gammaRelators n q R = gammaRelators n q S := by
  unfold gammaRelators
  rw [h]

/-- Free-relator equality preserves the closed normal subgroup defining the bare presentation. -/
theorem relatorSubgroup_gammaRelators_eq_of_freeMarking_eval_eq {n q : ℕ}
    {R S : PWord (Generator n)}
    (h : (freeMarking n).eval R = (freeMarking n).eval S) :
    relatorSubgroup (gammaRelators n q R) = relatorSubgroup (gammaRelators n q S) :=
  congrArg relatorSubgroup (gammaRelators_eq_of_freeMarking_eval_eq h)

/-- Free-relator equality gives the same class of admissible finite quotients. -/
theorem isAdmissibleU_iff_of_freeMarking_eval_eq {n q : ℕ}
    {R S : PWord (Generator n)}
    (h : (freeMarking n).eval R = (freeMarking n).eval S)
    (U : OpenNormalSubgroup (FreeProfiniteGroup (Generator n))) :
    IsAdmissibleU n q R U ↔ IsAdmissibleU n q S U := by
  unfold IsAdmissibleU
  rw [gammaRelators_eq_of_freeMarking_eval_eq h]

/-- Free-relator equality preserves the intersection of all admissible open normal subgroups. -/
theorem NR_eq_of_freeMarking_eval_eq {n q : ℕ} {R S : PWord (Generator n)}
    (h : (freeMarking n).eval R = (freeMarking n).eval S) :
    NR n q R = NR n q S := by
  unfold NR IsAdmissibleU
  rw [gammaRelators_eq_of_freeMarking_eval_eq h]

/-- Free-relator equality preserves the campaign's corrected, admissible-limit presentation. -/
theorem GammaR_eq_of_freeMarking_eval_eq {n q : ℕ} {R S : PWord (Generator n)}
    (h : (freeMarking n).eval R = (freeMarking n).eval S) :
    GammaR n q R = GammaR n q S := by
  unfold GammaR
  congr 1
  exact NR_eq_of_freeMarking_eval_eq h

/-- Free-relator equality also preserves the bare two-relator profinite presentation. -/
theorem GammaBare_eq_of_freeMarking_eval_eq {n q : ℕ} {R S : PWord (Generator n)}
    (h : (freeMarking n).eval R = (freeMarking n).eval S) :
    GammaBare n q R = GammaBare n q S := by
  unfold GammaBare
  rw [gammaRelators_eq_of_freeMarking_eval_eq h]

namespace Words.Mpc

/-- A compatible displayed `Mpc` word and its arbitrary-unit semantic word are the same relator
element of the free profinite group. -/
theorem freeMarking_eval_mpcWUnit_eq_display (alpha r p h : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    (freeMarking (2 + 2 * h)).eval (mpcWUnit alpha r p eta h) =
      (freeMarking (2 + 2 * h)).eval (mpcW alpha r p d.display h) :=
  eval_mpcWUnit_eq_display (freeMarking (2 + 2 * h)) alpha r p d

/-- A compatible `Mpc` display gives exactly the semantic arbitrary-unit relator set. -/
theorem gammaRelators_mpcWUnit_eq_display (alpha r p h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    gammaRelators (2 + 2 * h) q (mpcWUnit alpha r p eta h) =
      gammaRelators (2 + 2 * h) q (mpcW alpha r p d.display h) :=
  gammaRelators_eq_of_freeMarking_eval_eq
    (freeMarking_eval_mpcWUnit_eq_display alpha r p h d)

/-- The closed normal subgroup of the displayed `Mpc` presentation is the semantic one. -/
theorem relatorSubgroup_mpcWUnit_eq_display (alpha r p h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    relatorSubgroup (gammaRelators (2 + 2 * h) q (mpcWUnit alpha r p eta h)) =
      relatorSubgroup (gammaRelators (2 + 2 * h) q (mpcW alpha r p d.display h)) :=
  relatorSubgroup_gammaRelators_eq_of_freeMarking_eval_eq
    (freeMarking_eval_mpcWUnit_eq_display alpha r p h d)

/-- The corrected admissible-limit kernels for semantic and displayed `Mpc` words agree. -/
theorem NR_mpcWUnit_eq_display (alpha r p h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    NR (2 + 2 * h) q (mpcWUnit alpha r p eta h) =
      NR (2 + 2 * h) q (mpcW alpha r p d.display h) :=
  NR_eq_of_freeMarking_eval_eq (freeMarking_eval_mpcWUnit_eq_display alpha r p h d)

/-- A compatible displayed `Mpc` word presents exactly the semantic arbitrary-unit `GammaR`. -/
theorem GammaR_mpcWUnit_eq_display (alpha r p h q : ℕ) {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) :
    GammaR (2 + 2 * h) q (mpcWUnit alpha r p eta h) =
      GammaR (2 + 2 * h) q (mpcW alpha r p d.display h) :=
  GammaR_eq_of_freeMarking_eval_eq (freeMarking_eval_mpcWUnit_eq_display alpha r p h d)

end Words.Mpc

/-! ## Display packages consumed by `SelectedPresentation` -/

/-- The certificate display data required to select an exact frozen word for a branch.  Compact
rows need no display; the two procyclic rows require a well-formed compatible package. -/
def BranchData.DisplayFor : BranchData → Type
  | .L | .N0 _ | .M0 _ => PUnit
  | .Npc _ _ eta => NpcDisplayFor eta
  | .Mpc _ _ _ eta => MpcDisplayFor eta

namespace SelectedPresentation

/-- Select the exact R5 frozen word for a branch, requiring an honest compatible certificate
display on the procyclic rows. -/
noncomputable def ofBranch (h : ℕ) : (B : BranchData) → B.DisplayFor → SelectedPresentation
  | .L, _ => .L h
  | .N0 alpha, _ => .N0 alpha h
  | .Npc alpha r _, d => .Npc alpha r h d.data
  | .M0 alpha, _ => .M0 alpha h
  | .Mpc alpha r epsilon _, d => .Mpc alpha r epsilon d.display h

@[simp] theorem ofBranch_L (h : ℕ) : ofBranch h .L PUnit.unit = .L h := rfl

@[simp] theorem ofBranch_N0 (alpha h : ℕ) :
    ofBranch h (.N0 alpha) PUnit.unit = .N0 alpha h := rfl

@[simp] theorem ofBranch_Npc (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta) :
    ofBranch h (.Npc alpha r eta) d = .Npc alpha r h d.data := rfl

@[simp] theorem ofBranch_M0 (alpha h : ℕ) :
    ofBranch h (.M0 alpha) PUnit.unit = .M0 alpha h := rfl

@[simp] theorem ofBranch_Mpc (alpha r h : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ)
    (d : MpcDisplayFor eta) :
    ofBranch h (.Mpc alpha r epsilon eta) d = .Mpc alpha r epsilon d.display h := rfl

/-- The selected `Npc` word is literally the semantic word of the branch unit. -/
theorem word_ofBranch_Npc (alpha r h : ℕ) (eta : ℤ_[2]ˣ) (d : NpcDisplayFor eta) :
    (ofBranch h (.Npc alpha r eta) d).word = Words.Npc.npcWUnit alpha r h eta := by
  change Words.Npc.npcW alpha r h d.data = Words.Npc.npcWUnit alpha r h eta
  exact (Words.Npc.npcWUnit_eq_display alpha r h d).symm

/-- The selected `Mpc` word evaluates like the semantic word of the branch unit.  The statement
is deliberately at evaluation level because `.one` and `.lit` have different `PWord` syntax. -/
theorem eval_word_ofBranch_Mpc {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (alpha r h : ℕ) (epsilon : Bool) (eta : ℤ_[2]ˣ) (t : Marking (2 + 2 * h) G)
    (d : MpcDisplayFor eta) :
    t.eval ((ofBranch h (.Mpc alpha r epsilon eta) d).word) =
      t.eval (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta h) := by
  change t.eval (Words.Mpc.mpcW alpha r (p epsilon r) d.display h) =
    t.eval (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta h)
  exact (Words.Mpc.eval_mpcWUnit_eq_display t alpha r (p epsilon r) d).symm

/-- The selector's displayed `Mpc` row and its branch-unit semantic word define the same relator
set in the free profinite group. -/
theorem gammaRelators_word_ofBranch_Mpc (alpha r h q : ℕ) (epsilon : Bool)
    (eta : ℤ_[2]ˣ) (d : MpcDisplayFor eta) :
    gammaRelators (2 + 2 * h) q ((ofBranch h (.Mpc alpha r epsilon eta) d).word) =
      gammaRelators (2 + 2 * h) q
        (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta h) :=
  gammaRelators_eq_of_freeMarking_eval_eq
    (eval_word_ofBranch_Mpc alpha r h epsilon eta (freeMarking (2 + 2 * h)) d)

/-- Consequently the selected displayed `Mpc` row presents exactly the branch-unit semantic
admissible-limit group. -/
theorem GammaR_word_ofBranch_Mpc (alpha r h q : ℕ) (epsilon : Bool)
    (eta : ℤ_[2]ˣ) (d : MpcDisplayFor eta) :
    GammaR (2 + 2 * h) q ((ofBranch h (.Mpc alpha r epsilon eta) d).word) =
      GammaR (2 + 2 * h) q (Words.Mpc.mpcWUnit alpha r (p epsilon r) eta h) :=
  GammaR_eq_of_freeMarking_eval_eq
    (eval_word_ofBranch_Mpc alpha r h epsilon eta (freeMarking (2 + 2 * h)) d)

end SelectedPresentation

end GQ2.Dyadic
