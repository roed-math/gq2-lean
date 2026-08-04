/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H3FiniteBarFoxAssembly
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# A concrete finite bar--Fox chain map

This file constructs the easy, but indispensable, direction of the comparison between the
presentation complex and the inhomogeneous bar resolution. For a marking `m : I → Q`, the
presentation one-cell `eᵢ` is sent to the bar one-cell `[mᵢ]`. A canonical contraction of the
bar complex then fills every Fox row whose relator evaluates to one.

All modules below are the existing finite regular mod-two modules. In particular, the final
specialization is literally the improved square Fox row, not an abstract replacement. The two
chain-map identities are proved on all chains. What remains for the full
`SqFiniteToCompletedBarFoxAssembly` is the reverse comparison (bar to presentation), compatible
under refinement, and its passage to the completed inverse system.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2.ContCoh GQ2.FoxH
open GQ2.Dyadic.SqCore

variable {Q I rel : Type} [Group Q]

/-! ## Identification with Mathlib's bar resolution -/

/-- Convert tuple notation for two-cochains to Mathlib's `Fin 2` notation. -/
def finiteModTwoTupleToFinTwo :
    FiniteModTwoBarCochainTwo Q →+ ((Fin 2 → Q) → ZMod 2) where
  toFun c g := c (g 0, g 1)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Convert tuple notation for three-cochains to Mathlib's `Fin 3` notation. -/
def finiteModTwoTupleToFinThree :
    FiniteModTwoBarCochainThree Q →+ ((Fin 3 → Q) → ZMod 2) where
  toFun c g := c (g 0, g 1, g 2)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Convert tuple notation for four-cochains to Mathlib's `Fin 4` notation. -/
def finiteModTwoTupleToFinFour :
    FiniteModTwoBarCochainFour Q →+ ((Fin 4 → Q) → ZMod 2) where
  toFun c g := c (g 0, g 1, g 2, g 3)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Our explicit finite `d²` is exactly the inhomogeneous differential dual to Mathlib's
`Rep.barResolution`. -/
theorem finiteModTwoBarDTwo_eq_repBarDifferential
    (c : FiniteModTwoBarCochainTwo Q) :
    finiteModTwoTupleToFinThree (finiteModTwoBarDTwo Q c) =
      (inhomogeneousCochains.d (Rep.trivial (ZMod 2) Q (ZMod 2)) 2).hom
        (finiteModTwoTupleToFinTwo c) := by
  letI := trivialZModTwoAction Q
  funext g
  simp [finiteModTwoTupleToFinThree, finiteModTwoBarDTwo, dTwo,
    finiteModTwoTupleToFinTwo, inhomogeneousCochains.d_hom_apply,
    Fin.sum_univ_three]
  change c (g 1, g 2) - c (g 0 * g 1, g 2) +
      c (g 0, g 1 * g 2) - c (g 0, g 1) =
    c (g 1, g 2) +
      (c (g 0 * g 1, g 2) + c (g 0, g 1 * g 2) + c (g 0, g 1))
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  abel

/-- Our explicit finite `d³` is exactly the next differential dual to Mathlib's
`Rep.barResolution`. -/
theorem finiteModTwoBarDThree_eq_repBarDifferential
    (c : FiniteModTwoBarCochainThree Q) :
    finiteModTwoTupleToFinFour (finiteModTwoBarDThree Q c) =
      (inhomogeneousCochains.d (Rep.trivial (ZMod 2) Q (ZMod 2)) 3).hom
        (finiteModTwoTupleToFinThree c) := by
  letI := trivialZModTwoAction Q
  funext g
  simp [finiteModTwoTupleToFinFour, finiteModTwoBarDThree, dThree,
    finiteModTwoTupleToFinThree, inhomogeneousCochains.d_hom_apply,
    Fin.sum_univ_four]
  change c (g 1, g 2, g 3) - c (g 0 * g 1, g 2, g 3) +
        c (g 0, g 1 * g 2, g 3) - c (g 0, g 1, g 2 * g 3) +
        c (g 0, g 1, g 2) =
    c (g 1, g 2, g 3) +
      (c (g 0 * g 1, g 2, g 3) + c (g 0, g 1 * g 2, g 3) +
        c (g 0, g 1, g 2 * g 3) + c (g 0, g 1, g 2))
  simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two]
  abel

/-! ## The first three finite bar chain modules -/

/-- Degree zero of the mod-two inhomogeneous bar resolution. -/
abbrev FiniteModTwoBarChainZero (Q : Type) :=
  RegularModTwoRelationModule Q Unit

/-- Degree one of the mod-two inhomogeneous bar resolution. A basis element `(g,q)` denotes
the translate `g[q]`. -/
abbrev FiniteModTwoBarChainOne (Q : Type) :=
  RegularModTwoRelationModule Q Q

/-- Degree two of the mod-two inhomogeneous bar resolution. A basis element `(g,(q,r))`
denotes `g[q|r]`. -/
abbrev FiniteModTwoBarChainTwo (Q : Type) :=
  RegularModTwoRelationModule Q (Q × Q)

/-- The bar boundary `B₁ → B₀` in characteristic two: `g[q] ↦ [gq] + [g]`. -/
def finiteModTwoBarBoundaryOne :
    FiniteModTwoBarChainOne Q →ₗ[ZMod 2] FiniteModTwoBarChainZero Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × Q =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (p.1 * p.2, ()) 1 + Finsupp.single (p.1, ()) 1)

@[simp] theorem finiteModTwoBarBoundaryOne_single
    (g q : Q) (a : ZMod 2) :
    finiteModTwoBarBoundaryOne (Q := Q) (Finsupp.single (g, q) a) =
      Finsupp.single (g * q, ()) a + Finsupp.single (g, ()) a := by
  classical
  rw [finiteModTwoBarBoundaryOne, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_add, smul_eq_mul]

/-- The bar boundary `B₂ → B₁` in characteristic two:
`g[q|r] ↦ gq[r] + g[qr] + g[q]`. -/
def finiteModTwoBarBoundaryTwo :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarChainOne Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × (Q × Q) =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (p.1 * p.2.1, p.2.2) 1 +
        Finsupp.single (p.1, p.2.1 * p.2.2) 1 +
        Finsupp.single (p.1, p.2.1) 1)

@[simp] theorem finiteModTwoBarBoundaryTwo_single
    (g q r : Q) (a : ZMod 2) :
    finiteModTwoBarBoundaryTwo (Q := Q) (Finsupp.single (g, (q, r)) a) =
      Finsupp.single (g * q, r) a +
        Finsupp.single (g, q * r) a + Finsupp.single (g, q) a := by
  classical
  rw [finiteModTwoBarBoundaryTwo, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_add, smul_eq_mul]

/-- The first bar identity `∂₁∂₂ = 0`. -/
theorem finiteModTwoBarBoundaryOne_comp_boundaryTwo :
    (finiteModTwoBarBoundaryOne (Q := Q)).comp
        (finiteModTwoBarBoundaryTwo (Q := Q)) = 0 := by
  classical
  apply LinearMap.ext
  intro c
  change finiteModTwoBarBoundaryOne (finiteModTwoBarBoundaryTwo c) = 0
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, q, r⟩
      rw [map_add, map_add, ih, add_zero,
        finiteModTwoBarBoundaryTwo_single, map_add, map_add,
        finiteModTwoBarBoundaryOne_single, finiteModTwoBarBoundaryOne_single,
        finiteModTwoBarBoundaryOne_single, mul_assoc]
      let A : FiniteModTwoBarChainZero Q := Finsupp.single (g * (q * r), ()) a
      let B : FiniteModTwoBarChainZero Q := Finsupp.single (g * q, ()) a
      let C : FiniteModTwoBarChainZero Q := Finsupp.single (g, ()) a
      change (A + B) + (A + C) + (B + C) = 0
      calc
        (A + B) + (A + C) + (B + C) = (A + A) + (B + B) + (C + C) := by abel
        _ = 0 := by
          have hA : A + A = 0 := regularModTwoRelationModule_add_self Q Unit A
          have hB : B + B = 0 := regularModTwoRelationModule_add_self Q Unit B
          have hC : C + C = 0 := regularModTwoRelationModule_add_self Q Unit C
          rw [hA, hB, hC]
          simp

/-! ## The canonical contraction in degrees zero and one -/

/-- Insert a degree-zero basis vector as the bar one-cell `[g]`. -/
def finiteModTwoBarContractZero :
    FiniteModTwoBarChainZero Q →ₗ[ZMod 2] FiniteModTwoBarChainOne Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × Unit =>
    LinearMap.toSpanSingleton (ZMod 2) _ (Finsupp.single (1, p.1) 1)

@[simp] theorem finiteModTwoBarContractZero_single
    (g : Q) (a : ZMod 2) :
    finiteModTwoBarContractZero (Q := Q) (Finsupp.single (g, ()) a) =
      Finsupp.single (1, g) a := by
  classical
  rw [finiteModTwoBarContractZero, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- Insert a degree-one basis vector `g[q]` as the bar two-cell `[g|q]`. -/
def finiteModTwoBarContractOne :
    FiniteModTwoBarChainOne Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × Q =>
    LinearMap.toSpanSingleton (ZMod 2) _ (Finsupp.single (1, (p.1, p.2)) 1)

@[simp] theorem finiteModTwoBarContractOne_single
    (g q : Q) (a : ZMod 2) :
    finiteModTwoBarContractOne (Q := Q) (Finsupp.single (g, q) a) =
      Finsupp.single (1, (g, q)) a := by
  classical
  rw [finiteModTwoBarContractOne, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The all-chain contraction identity `∂₂s₁ + s₀∂₁ = id` on the first bar module. -/
theorem finiteModTwoBar_contracting_identity (c : FiniteModTwoBarChainOne Q) :
    finiteModTwoBarBoundaryTwo (finiteModTwoBarContractOne c) +
        finiteModTwoBarContractZero (finiteModTwoBarBoundaryOne c) = c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, q⟩
      simp only [map_add, finiteModTwoBarContractOne_single,
        finiteModTwoBarBoundaryTwo_single, finiteModTwoBarBoundaryOne_single,
        finiteModTwoBarContractZero_single]
      simp only [one_mul]
      let A : FiniteModTwoBarChainOne Q := Finsupp.single (1, g * q) a
      let B : FiniteModTwoBarChainOne Q := Finsupp.single (1, g) a
      let S : FiniteModTwoBarChainOne Q := Finsupp.single (g, q) a
      let T : FiniteModTwoBarChainOne Q :=
        finiteModTwoBarBoundaryTwo (finiteModTwoBarContractOne c)
      let U : FiniteModTwoBarChainOne Q :=
        finiteModTwoBarContractZero (finiteModTwoBarBoundaryOne c)
      change S + A + B + T + (A + B + U) = S + c
      calc
        S + A + B + T + (A + B + U) =
            S + (T + U) + (A + A) + (B + B) := by abel
        _ = S + (T + U) := by
          have hA : A + A = 0 := regularModTwoRelationModule_add_self Q Q A
          have hB : B + B = 0 := regularModTwoRelationModule_add_self Q Q B
          rw [hA, hB]
          simp
        _ = S + c := by rw [ih]

/-! ## Presentation one-cells and the forward comparison -/

/-- The presentation boundary on one-cells: `g eᵢ ↦ [g mᵢ] + [g]`. -/
def finiteMarkedBoundaryOne (m : I → Q) :
    RegularModTwoRelationModule Q I →ₗ[ZMod 2] FiniteModTwoBarChainZero Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × I =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (p.1 * m p.2, ()) 1 + Finsupp.single (p.1, ()) 1)

@[simp] theorem finiteMarkedBoundaryOne_single
    (m : I → Q) (g : Q) (i : I) (a : ZMod 2) :
    finiteMarkedBoundaryOne m (Finsupp.single (g, i) a) =
      Finsupp.single (g * m i, ()) a + Finsupp.single (g, ()) a := by
  classical
  rw [finiteMarkedBoundaryOne, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_add, smul_eq_mul]

/-- Send the presentation one-cell `g eᵢ` to the bar one-cell `g[mᵢ]`. -/
def finiteMarkedToBarOne (m : I → Q) :
    RegularModTwoRelationModule Q I →ₗ[ZMod 2] FiniteModTwoBarChainOne Q :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × I =>
    LinearMap.toSpanSingleton (ZMod 2) _ (Finsupp.single (p.1, m p.2) 1)

omit [Group Q] in
@[simp] theorem finiteMarkedToBarOne_single
    (m : I → Q) (g : Q) (i : I) (a : ZMod 2) :
    finiteMarkedToBarOne m (Finsupp.single (g, i) a) =
      Finsupp.single (g, m i) a := by
  classical
  rw [finiteMarkedToBarOne, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- The degree-one comparison is a chain map on every presentation one-chain. -/
theorem finiteMarkedToBarOne_boundary (m : I → Q)
    (c : RegularModTwoRelationModule Q I) :
    finiteModTwoBarBoundaryOne (finiteMarkedToBarOne m c) =
      finiteMarkedBoundaryOne m c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, i⟩
      simp [ih]

/-! ## The mod-two Fox fundamental identity -/

/-- The crossed-difference lift `q ↦ ([q]+[1],q)` into the split regular extension. -/
def finiteDifferenceWordLift : Q →* WordLift (FiniteModTwoBarChainZero Q) Q where
  toFun q := ⟨Finsupp.single (q, ()) 1 + Finsupp.single (1, ()) 1, q⟩
  map_one' := by
    apply WordLift.ext
    · exact regularModTwoRelationModule_add_self Q Unit _
    · rfl
  map_mul' q r := by
    apply WordLift.ext
    · change Finsupp.single (q * r, ()) 1 + Finsupp.single (1, ()) 1 =
        (Finsupp.single (q, ()) 1 + Finsupp.single (1, ()) 1) +
          q • (Finsupp.single (r, ()) 1 + Finsupp.single (1, ()) 1)
      change Finsupp.single (q * r, ()) 1 + Finsupp.single (1, ()) 1 =
        (Finsupp.single (q, ()) 1 + Finsupp.single (1, ()) 1) +
          regularModTwoTranslate Q Unit q
            (Finsupp.single (r, ()) 1 + Finsupp.single (1, ()) 1)
      rw [map_add, regularModTwoTranslate_single, regularModTwoTranslate_single, mul_one]
      let A : FiniteModTwoBarChainZero Q := Finsupp.single (q * r, ()) 1
      let B : FiniteModTwoBarChainZero Q := Finsupp.single (1, ()) 1
      let C : FiniteModTwoBarChainZero Q := Finsupp.single (q, ()) 1
      change A + B = (C + B) + (A + C)
      calc
        A + B = A + B + (C + C) := by
          rw [show C + C = 0 from regularModTwoRelationModule_add_self Q Unit C, add_zero]
        _ = (C + B) + (A + C) := by abel
      
    · rfl

@[simp] theorem finiteDifferenceWordLift_u (q : Q) :
    (finiteDifferenceWordLift (Q := Q) q).u =
      Finsupp.single (q, ()) 1 + Finsupp.single (1, ()) 1 := rfl

@[simp] theorem finiteDifferenceWordLift_g (q : Q) :
    (finiteDifferenceWordLift (Q := Q) q).g = q := rfl

/-- The presentation boundary of the universal Fox derivative is the mod-two difference
`[eval(w)] + [1]`. -/
theorem finiteMarkedBoundaryOne_modTwoFoxDerivative
    (m : I → Q) (w : FreeGroup I) :
    finiteMarkedBoundaryOne m (modTwoFoxDerivative m w) =
      Finsupp.single (FreeGroup.lift m w, ()) 1 + Finsupp.single (1, ()) 1 := by
  let a : I → FiniteModTwoBarChainZero Q := fun i =>
    Finsupp.single (m i, ()) 1 + Finsupp.single (1, ()) 1
  have heval (c : RegularModTwoRelationModule Q I) :
      finiteMarkedBoundaryOne m c =
        regularModTwoRelationEval
          (fun z => regularModTwoRelationModule_add_self Q Unit z) a c := by
    classical
    induction c using Finsupp.induction with
    | zero => simp
    | single_add p b c hp hb ih =>
        rcases p with ⟨q, i⟩
        rw [map_add, map_add, ih,
          finiteMarkedBoundaryOne_single,
          regularModTwoRelationEval_single]
        congr 1
        change Finsupp.single (q * m i, ()) b + Finsupp.single (q, ()) b =
          b.val • q •
            (Finsupp.single (m i, ()) 1 + Finsupp.single (1, ()) 1)
        have htranslate : q •
            (Finsupp.single (m i, ()) (1 : ZMod 2) + Finsupp.single (1, ()) 1) =
          Finsupp.single (q * m i, ()) 1 + Finsupp.single (q, ()) 1 := by
          change regularModTwoTranslate Q Unit q
              (Finsupp.single (m i, ()) 1 + Finsupp.single (1, ()) 1) = _
          rw [map_add, regularModTwoTranslate_single,
            regularModTwoTranslate_single, mul_one]
        rw [htranslate]
        have hleft :
            Finsupp.single (q * m i, ()) b + Finsupp.single (q, ()) b =
              b • (Finsupp.single (q * m i, ()) (1 : ZMod 2) +
                Finsupp.single (q, ()) 1) := by
          rw [smul_add, Finsupp.smul_single, Finsupp.smul_single]
          simp only [smul_eq_mul, mul_one]
        rw [hleft, ← ZMod.natCast_zmod_val b, Nat.cast_smul_eq_nsmul,
          ZMod.val_natCast]
        exact congrArg
          (fun n : ℕ => n •
            (Finsupp.single (q * m i, ()) (1 : ZMod 2) + Finsupp.single (q, ()) 1))
          (Nat.mod_eq_of_lt b.isLt).symm
  have hboundary :
      finiteMarkedBoundaryOne m (modTwoFoxDerivative m w) =
        (FreeGroup.lift (foxLift m a) w).u := by
    rw [heval]
    exact regularModTwoRelationEval_modTwoFoxDerivative
      (fun c => regularModTwoRelationModule_add_self Q Unit c) m a w
  have hlift : FreeGroup.lift (foxLift m a) =
      (finiteDifferenceWordLift (Q := Q)).comp (FreeGroup.lift m) := by
    apply FreeGroup.ext_hom
    intro i
    apply WordLift.ext
    · simp [a, foxLift]
    · simp [foxLift]
  rw [hboundary, hlift]
  rfl

/-- A relator that evaluates to one has a Fox row in the kernel of the presentation
one-boundary. -/
theorem finiteMarkedBoundaryOne_modTwoFoxDerivative_eq_zero
    (m : I → Q) (w : FreeGroup I) (hw : FreeGroup.lift m w = 1) :
    finiteMarkedBoundaryOne m (modTwoFoxDerivative m w) = 0 := by
  rw [finiteMarkedBoundaryOne_modTwoFoxDerivative, hw]
  exact regularModTwoRelationModule_add_self Q Unit _

/-- Every finite Fox relation matrix lands in presentation one-cycles when every listed relator
evaluates to one. -/
theorem finiteMarkedBoundaryOne_foxBoundary_eq_zero
    (m : I → Q) (w : rel → FreeGroup I)
    (hw : ∀ k, FreeGroup.lift m (w k) = 1)
    (c : RegularModTwoRelationModule Q rel) :
    finiteMarkedBoundaryOne m ((finiteLevelModTwoFoxBoundary m w).map c) = 0 := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, k⟩
      simp only [map_add, ih, add_zero, finiteLevelModTwoFoxBoundary_single, map_smul]
      have hequiv : finiteMarkedBoundaryOne m
          (regularModTwoTranslate Q I g (modTwoFoxDerivative m (w k))) =
        regularModTwoTranslate Q Unit g
          (finiteMarkedBoundaryOne m (modTwoFoxDerivative m (w k))) := by
        induction modTwoFoxDerivative m (w k) using Finsupp.induction with
        | zero => simp
        | single_add p b c hp hb ih =>
            rcases p with ⟨q, i⟩
            simp [ih, mul_assoc]
      rw [hequiv, finiteMarkedBoundaryOne_modTwoFoxDerivative_eq_zero m (w k) (hw k)]
      simp

/-! ## Filling the actual Fox row in the bar complex -/

/-- The degree-two forward comparison: apply the finite Fox row, map presentation one-cells
to bar one-cells, and fill the resulting bar cycle with the canonical contraction. -/
def finiteFoxToBarTwo (m : I → Q) (w : rel → FreeGroup I) :
    RegularModTwoRelationModule Q rel →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q :=
  (finiteModTwoBarContractOne (Q := Q)).comp
    ((finiteMarkedToBarOne m).comp (finiteLevelModTwoFoxBoundary m w).map)

/-- The degree-two comparison is a chain map on **every** relation chain. -/
theorem finiteFoxToBarTwo_boundary
    (m : I → Q) (w : rel → FreeGroup I)
    (hw : ∀ k, FreeGroup.lift m (w k) = 1)
    (c : RegularModTwoRelationModule Q rel) :
    finiteModTwoBarBoundaryTwo (finiteFoxToBarTwo m w c) =
      finiteMarkedToBarOne m ((finiteLevelModTwoFoxBoundary m w).map c) := by
  have hcontract := finiteModTwoBar_contracting_identity
    (Q := Q) (finiteMarkedToBarOne m ((finiteLevelModTwoFoxBoundary m w).map c))
  have hzero : finiteModTwoBarBoundaryOne
      (finiteMarkedToBarOne m ((finiteLevelModTwoFoxBoundary m w).map c)) = 0 := by
    rw [finiteMarkedToBarOne_boundary]
    exact finiteMarkedBoundaryOne_foxBoundary_eq_zero m w hw c
  rw [hzero, map_zero, add_zero] at hcontract
  exact hcontract

/-! ## Naturality of the forward comparison -/

variable {Q' J J' : Type} [Group Q']

/-- Simultaneous pushforward of the regular coefficient and basis labels. -/
def regularModTwoMap (φ : Q →* Q') (ψ : J → J') :
    RegularModTwoRelationModule Q J →ₗ[ZMod 2]
      RegularModTwoRelationModule Q' J' :=
  (Finsupp.lsum (ZMod 2)) fun p : Q × J =>
    LinearMap.toSpanSingleton (ZMod 2) _
      (Finsupp.single (φ p.1, ψ p.2) 1)

@[simp] theorem regularModTwoMap_single
    (φ : Q →* Q') (ψ : J → J') (g : Q) (j : J) (a : ZMod 2) :
    regularModTwoMap φ ψ (Finsupp.single (g, j) a) =
      Finsupp.single (φ g, ψ j) a := by
  classical
  rw [regularModTwoMap, Finsupp.lsum_single]
  simp [LinearMap.toSpanSingleton_apply, smul_eq_mul]

/-- Pushforward on bar one-chains. -/
def finiteModTwoBarMapOne (φ : Q →* Q') :
    FiniteModTwoBarChainOne Q →ₗ[ZMod 2] FiniteModTwoBarChainOne Q' :=
  regularModTwoMap φ φ

/-- Pushforward on bar two-chains. -/
def finiteModTwoBarMapTwo (φ : Q →* Q') :
    FiniteModTwoBarChainTwo Q →ₗ[ZMod 2] FiniteModTwoBarChainTwo Q' :=
  regularModTwoMap φ (fun p => (φ p.1, φ p.2))

/-- The canonical degree-one contraction commutes with every group homomorphism. -/
theorem finiteModTwoBarContractOne_natural
    (φ : Q →* Q') (c : FiniteModTwoBarChainOne Q) :
    finiteModTwoBarMapTwo φ (finiteModTwoBarContractOne c) =
      finiteModTwoBarContractOne (finiteModTwoBarMapOne φ c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, q⟩
      simp [finiteModTwoBarMapOne, finiteModTwoBarMapTwo]
      simpa [finiteModTwoBarMapOne, finiteModTwoBarMapTwo] using ih

/-- The degree-one presentation-to-bar comparison commutes with every quotient homomorphism. -/
theorem finiteMarkedToBarOne_natural
    (φ : Q →* Q') (m : I → Q) (c : RegularModTwoRelationModule Q I) :
    finiteModTwoBarMapOne φ (finiteMarkedToBarOne m c) =
      finiteMarkedToBarOne (fun i => φ (m i))
        (regularModTwoPushforward φ I c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, i⟩
      simp [finiteModTwoBarMapOne]
      simpa [finiteModTwoBarMapOne] using ih

/-- The degree-two Fox-to-bar comparison is quotient-natural on every relation chain. -/
theorem finiteFoxToBarTwo_natural
    (φ : Q →* Q') (m : I → Q) (w : rel → FreeGroup I)
    (c : RegularModTwoRelationModule Q rel) :
    finiteModTwoBarMapTwo φ (finiteFoxToBarTwo m w c) =
      finiteFoxToBarTwo (fun i => φ (m i)) w
        (regularModTwoPushforward φ rel c) := by
  change finiteModTwoBarMapTwo φ
      (finiteModTwoBarContractOne
        (finiteMarkedToBarOne m ((finiteLevelModTwoFoxBoundary m w).map c))) =
    finiteModTwoBarContractOne
      (finiteMarkedToBarOne (fun i => φ (m i))
        ((finiteLevelModTwoFoxBoundary (fun i => φ (m i)) w).map
          (regularModTwoPushforward φ rel c)))
  rw [
    finiteModTwoBarContractOne_natural,
    finiteMarkedToBarOne_natural,
    finiteLevelModTwoFoxBoundary_natural]

/-! ## The literal improved square quotient row -/

/-- The forward relation-to-bar-two map for the actual improved square presentation at an
open-normal quotient. -/
def sqOpenQuotientFoxToBarTwo (h : ℕ)
    (V : OpenNormalSubgroup (DSq h : Type)) :
    RegularModTwoRelationModule ((DSq h : Type) ⧸ V.toSubgroup) Unit →ₗ[ZMod 2]
      FiniteModTwoBarChainTwo ((DSq h : Type) ⧸ V.toSubgroup) :=
  finiteFoxToBarTwo (sqOpenQuotientMarking h V) (fun _ : Unit => sqDiscreteRelator h)

/-- The discrete improved square relator evaluates to one at every actual quotient marking. -/
theorem sqOpenQuotientMarking_sqDiscreteRelator
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type)) :
    FreeGroup.lift (sqOpenQuotientMarking h V) (sqDiscreteRelator h) = 1 := by
  rw [FreeGroup.lift_sqDiscreteRelator]
  change sqRelWord (fun i => QuotientGroup.mk' V.toSubgroup (sqGen h i)) = 1
  rw [← map_sqRelWord (QuotientGroup.mk' V.toSubgroup) (sqGen h), dsq_relation h, map_one]

/-- **Actual finite bar--Fox identity.** The bar boundary of the constructed two-chain is
the image of the literal improved square Fox row, for every relation chain. -/
theorem sqOpenQuotientFoxToBarTwo_boundary
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (c : RegularModTwoRelationModule ((DSq h : Type) ⧸ V.toSubgroup) Unit) :
    finiteModTwoBarBoundaryTwo (sqOpenQuotientFoxToBarTwo h V c) =
      finiteMarkedToBarOne (sqOpenQuotientMarking h V)
        ((sqFiniteLevelModTwoFoxBoundary h (sqOpenQuotientMarking h V)).map c) := by
  exact finiteFoxToBarTwo_boundary
    (sqOpenQuotientMarking h V) (fun _ : Unit => sqDiscreteRelator h)
    (fun _ => sqOpenQuotientMarking_sqDiscreteRelator h V) c

/-- The degree-one chain-map identity for the actual improved quotient marking. -/
theorem sqOpenQuotientMarkedToBarOne_boundary
    (h : ℕ) (V : OpenNormalSubgroup (DSq h : Type))
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ V.toSubgroup) (Fin (sqRank h))) :
    finiteModTwoBarBoundaryOne
        (finiteMarkedToBarOne (sqOpenQuotientMarking h V) c) =
      finiteMarkedBoundaryOne (sqOpenQuotientMarking h V) c :=
  finiteMarkedToBarOne_boundary (sqOpenQuotientMarking h V) c

/-- The actual improved-square forward comparison commutes with open-normal refinement. -/
theorem sqOpenQuotientFoxToBarTwo_natural
    (h : ℕ) {V W : OpenNormalSubgroup (DSq h : Type)}
    (hWV : W.toSubgroup ≤ V.toSubgroup)
    (c : RegularModTwoRelationModule
      ((DSq h : Type) ⧸ W.toSubgroup) Unit) :
    finiteModTwoBarMapTwo (openNormalQuotientProj hWV)
        (sqOpenQuotientFoxToBarTwo h W c) =
      sqOpenQuotientFoxToBarTwo h V
        (regularModTwoPushforward (openNormalQuotientProj hWV) Unit c) := by
  simpa only [sqOpenQuotientFoxToBarTwo,
    openNormalQuotientProj_sqOpenQuotientMarking] using
    finiteFoxToBarTwo_natural (openNormalQuotientProj hWV)
      (sqOpenQuotientMarking h W) (fun _ : Unit => sqDiscreteRelator h) c

end

end GQ2.Dyadic.Count
