/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import Mathlib.Algebra.Algebra.Unitization
import Mathlib.LinearAlgebra.Finsupp.Supported
import GQ2.Dyadic.Count.H3CompletedCubicPBWColumnSound

/-!
# A finite strictly filtered operator model for the cubic detector

This file constructs the finite ambient algebra in which the inhomogeneous cubic detector
lives.  Its underlying nilpotent algebra consists of endomorphisms of the PBW-normal words in
degrees zero through three which strictly raise the degree filtration.  Unitization supplies
the augmentation.  Four elements of its augmentation kernel have zero product for the formal
reason that four strict filtration raises leave the four-step space.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic GQ2.Dyadic.Count
open GQ2.Dyadic.SqCore

/-! ## The four-step PBW-normal space -/

/-- A PBW-normal word together with a degree in `0,1,2,3`. -/
abbrev SqCubicNormalIndex (h : ℕ) :=
  Σ n : Fin 4, SqQuadraticHomogeneousNormalWord h n.1

/-- The finite vector space on PBW-normal words of degree strictly below four. -/
abbrev SqCubicNormalSpace (h : ℕ) := SqCubicNormalIndex h →₀ ZMod 2

instance sqCubicNormalIndex_finite (h : ℕ) : Finite (SqCubicNormalIndex h) := by
  infer_instance

noncomputable instance sqCubicNormalIndex_fintype (h : ℕ) :
    Fintype (SqCubicNormalIndex h) := Fintype.ofFinite _

instance sqCubicNormalSpace_finite (h : ℕ) : Finite (SqCubicNormalSpace h) := by
  exact Finite.of_injective Finsupp.equivFunOnFinite
    Finsupp.equivFunOnFinite.injective

/-- The numerical degree of a four-step PBW index. -/
def sqCubicNormalIndexDegree {h : ℕ} (w : SqCubicNormalIndex h) : ℕ := w.1.1

/-- The descending filtration by words of degree at least `n`. -/
def sqCubicNormalFiltration (h n : ℕ) : Submodule (ZMod 2) (SqCubicNormalSpace h) :=
  Finsupp.supported (ZMod 2) (ZMod 2)
    {w | n ≤ sqCubicNormalIndexDegree w}

theorem sqCubicNormalFiltration_antitone (h : ℕ) {m n : ℕ} (hmn : m ≤ n) :
    sqCubicNormalFiltration h n ≤ sqCubicNormalFiltration h m := by
  intro f hf
  rw [sqCubicNormalFiltration, Finsupp.mem_supported] at hf ⊢
  intro w hw
  exact hmn.trans (hf hw)

@[simp] theorem sqCubicNormalFiltration_zero (h : ℕ) :
    sqCubicNormalFiltration h 0 = ⊤ := by
  apply le_antisymm le_top
  intro f hf
  rw [sqCubicNormalFiltration, Finsupp.mem_supported]
  intro w hw
  exact Nat.zero_le _

@[simp] theorem sqCubicNormalFiltration_four (h : ℕ) :
    sqCubicNormalFiltration h 4 = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [Submodule.mem_bot]
    apply Finsupp.ext
    intro w
    by_cases hw : w ∈ f.support
    · have hdeg : 4 ≤ sqCubicNormalIndexDegree w := by
        rw [sqCubicNormalFiltration, Finsupp.mem_supported] at hf
        exact hf hw
      change 4 ≤ w.1.1 at hdeg
      exact (Nat.not_lt_of_ge hdeg w.1.2).elim
    · simpa [Finsupp.mem_support_iff] using hw
  · exact bot_le

/-! ## Strictly filtration-raising endomorphisms -/

/-- An endomorphism strictly raises the degree filtration if it carries `F^n` into
`F^(n+1)` for every `n`. -/
def SqCubicStrictlyRaises {h : ℕ}
    (T : Module.End (ZMod 2) (SqCubicNormalSpace h)) : Prop :=
  ∀ n x, x ∈ sqCubicNormalFiltration h n →
    T x ∈ sqCubicNormalFiltration h (n + 1)

/-- The nonunital algebra of strictly filtration-raising endomorphisms. -/
def sqCubicStrictEnd (h : ℕ) :
    NonUnitalSubalgebra (ZMod 2)
      (Module.End (ZMod 2) (SqCubicNormalSpace h)) where
  carrier := {T | SqCubicStrictlyRaises T}
  zero_mem' := by
    intro n x hx
    exact Submodule.zero_mem _
  add_mem' := by
    intro T U hT hU n x hx
    exact Submodule.add_mem _ (hT n x hx) (hU n x hx)
  mul_mem' := by
    intro T U hT hU n x hx
    have hUx := hU n x hx
    have hTUx := hT (n + 1) (U x) hUx
    exact sqCubicNormalFiltration_antitone h (Nat.le_succ (n + 1)) hTUx
  smul_mem' := by
    intro a T hT n x hx
    exact Submodule.smul_mem _ a (hT n x hx)

/-- The finite augmented algebra used by the cubic operator detector. -/
abbrev SqCubicOperatorAlgebra (h : ℕ) :=
  Unitization (ZMod 2) (sqCubicStrictEnd h)

/-- Typeclass search does not recover the scalar ring from the subtype alone, so expose the
inherited nonunital ring instance explicitly. -/
noncomputable instance sqCubicStrictEnd_nonUnitalRing (h : ℕ) :
    NonUnitalRing (sqCubicStrictEnd h) :=
  @NonUnitalSubalgebra.toNonUnitalRing
    (ZMod 2) (Module.End (ZMod 2) (SqCubicNormalSpace h))
    inferInstance inferInstance inferInstance (sqCubicStrictEnd h)

instance sqCubicStrictEnd_finite (h : ℕ) : Finite (sqCubicStrictEnd h) := by
  exact Finite.of_injective
    (fun T : sqCubicStrictEnd h =>
      (T.1 : SqCubicNormalSpace h → SqCubicNormalSpace h))
    (by
      intro T U e
      apply Subtype.ext
      apply LinearMap.ext
      intro x
      exact congrFun e x)

instance sqCubicOperatorAlgebra_finite (h : ℕ) :
    Finite (SqCubicOperatorAlgebra h) := by
  exact Finite.of_injective Unitization.toProd Unitization.toProd_injective

/-- The scalar projection is the augmentation of the operator algebra. -/
def sqCubicOperatorAugmentation (h : ℕ) :
    SqCubicOperatorAlgebra h →ₐ[ZMod 2] ZMod 2 :=
  Unitization.fstHom (ZMod 2) (sqCubicStrictEnd h)

theorem sqCubicStrictEnd_product_four_zero (h : ℕ)
    (a b c d : sqCubicStrictEnd h) : a * b * c * d = 0 := by
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  have hx0 : x ∈ sqCubicNormalFiltration h 0 := by simp
  have hdx : (d : Module.End (ZMod 2) (SqCubicNormalSpace h)) x ∈
      sqCubicNormalFiltration h 1 := d.2 0 x hx0
  have hcdx : (c : Module.End (ZMod 2) (SqCubicNormalSpace h))
        ((d : Module.End (ZMod 2) (SqCubicNormalSpace h)) x) ∈
      sqCubicNormalFiltration h 2 := c.2 1 _ hdx
  have hbcdx : (b : Module.End (ZMod 2) (SqCubicNormalSpace h))
        ((c : Module.End (ZMod 2) (SqCubicNormalSpace h))
          ((d : Module.End (ZMod 2) (SqCubicNormalSpace h)) x)) ∈
      sqCubicNormalFiltration h 3 := b.2 2 _ hcdx
  have habcdx : (a : Module.End (ZMod 2) (SqCubicNormalSpace h))
        ((b : Module.End (ZMod 2) (SqCubicNormalSpace h))
          ((c : Module.End (ZMod 2) (SqCubicNormalSpace h))
            ((d : Module.End (ZMod 2) (SqCubicNormalSpace h)) x))) ∈
      sqCubicNormalFiltration h 4 := a.2 3 _ hbcdx
  rw [sqCubicNormalFiltration_four] at habcdx
  change ((a * b * c * d : sqCubicStrictEnd h) :
      Module.End (ZMod 2) (SqCubicNormalSpace h)) x = 0
  simpa [Module.End.mul_apply] using habcdx

/-- Four augmentation-zero elements of the unitized strict operator algebra have zero
product. -/
theorem sqCubicOperatorAugmentation_product_four_zero (h : ℕ)
    (a b c d : SqCubicOperatorAlgebra h)
    (ha : sqCubicOperatorAugmentation h a = 0)
    (hb : sqCubicOperatorAugmentation h b = 0)
    (hc : sqCubicOperatorAugmentation h c = 0)
    (hd : sqCubicOperatorAugmentation h d = 0) :
    a * b * c * d = 0 := by
  have ea : a = (a.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using ha
    · simp
  have eb : b = (b.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using hb
    · simp
  have ec : c = (c.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using hc
    · simp
  have ed : d = (d.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using hd
    · simp
  rw [ea, eb, ec, ed]
  simpa only [← Unitization.inr_mul, Unitization.inr_zero] using
    congrArg (fun z : sqCubicStrictEnd h =>
      (z : SqCubicOperatorAlgebra h))
      (sqCubicStrictEnd_product_four_zero h a.snd b.snd c.snd d.snd)

/-! ## Truncated homogeneous Diamond operators -/

/-- Insert a homogeneous normal word of degree `n < 4` into the four-step index. -/
def sqCubicNormalIndexOfHomogeneous (h n : ℕ) (hn : n < 4)
    (w : SqQuadraticHomogeneousNormalWord h n) : SqCubicNormalIndex h :=
  ⟨⟨n, hn⟩, w⟩

@[simp] theorem sqCubicNormalIndexDegree_ofHomogeneous (h n : ℕ) (hn : n < 4)
    (w : SqQuadraticHomogeneousNormalWord h n) :
    sqCubicNormalIndexDegree (sqCubicNormalIndexOfHomogeneous h n hn w) = n :=
  rfl

/-- Include one homogeneous PBW layer into the four-step space. -/
def sqCubicHomogeneousEmbed (h n : ℕ) (hn : n < 4) :
    SqQuadraticHomogeneousNormalSpace h n →ₗ[ZMod 2]
      SqCubicNormalSpace h :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2)
    (sqCubicNormalIndexOfHomogeneous h n hn)

@[simp] theorem sqCubicHomogeneousEmbed_single (h n : ℕ) (hn : n < 4)
    (w : SqQuadraticHomogeneousNormalWord h n) (a : ZMod 2) :
    sqCubicHomogeneousEmbed h n hn (Finsupp.single w a) =
      Finsupp.single (sqCubicNormalIndexOfHomogeneous h n hn w) a := by
  simp [sqCubicHomogeneousEmbed]

theorem sqCubicHomogeneousEmbed_mem_filtration (h m n : ℕ) (hn : n < 4)
    (hmn : m ≤ n) (f : SqQuadraticHomogeneousNormalSpace h n) :
    sqCubicHomogeneousEmbed h n hn f ∈ sqCubicNormalFiltration h m := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      rw [map_add, sqCubicHomogeneousEmbed_single]
      apply Submodule.add_mem
      · rw [sqCubicNormalFiltration, Finsupp.mem_supported]
        intro v hv
        have hvw : v = sqCubicNormalIndexOfHomogeneous h n hn w := by
          simpa [Finsupp.mem_support_iff, ha] using hv
        subst v
        exact hmn
      · exact ih

/-- The action of a marked letter on one four-step PBW basis vector, truncated after
degree three. -/
def sqCubicTruncatedLeftLetterOnIndex (h : ℕ) (i : Fin (sqRank h))
    (w : SqCubicNormalIndex h) : SqCubicNormalSpace h :=
  if hn : sqCubicNormalIndexDegree w < 3 then
    sqCubicHomogeneousEmbed h (sqCubicNormalIndexDegree w + 1) (by omega)
      (sqQuadraticHomogeneousProject h (sqCubicNormalIndexDegree w + 1)
        (sqNormalLeftLetter h i (Finsupp.single w.2.1 1)))
  else 0

/-- Linear extension of the truncated homogeneous Diamond action. -/
def sqCubicTruncatedLeftLetter (h : ℕ) (i : Fin (sqRank h)) :
    Module.End (ZMod 2) (SqCubicNormalSpace h) :=
  Finsupp.lsum (ZMod 2) fun w =>
    LinearMap.toSpanSingleton (ZMod 2) (SqCubicNormalSpace h)
      (sqCubicTruncatedLeftLetterOnIndex h i w)

@[simp] theorem sqCubicTruncatedLeftLetter_single (h : ℕ)
    (i : Fin (sqRank h)) (w : SqCubicNormalIndex h) (a : ZMod 2) :
    sqCubicTruncatedLeftLetter h i (Finsupp.single w a) =
      a • sqCubicTruncatedLeftLetterOnIndex h i w := by
  simp [sqCubicTruncatedLeftLetter]

theorem sqCubicTruncatedLeftLetterOnIndex_mem (h : ℕ)
    (i : Fin (sqRank h)) (w : SqCubicNormalIndex h) :
    sqCubicTruncatedLeftLetterOnIndex h i w ∈
      sqCubicNormalFiltration h (sqCubicNormalIndexDegree w + 1) := by
  rw [sqCubicTruncatedLeftLetterOnIndex]
  split_ifs with hn
  · exact sqCubicHomogeneousEmbed_mem_filtration h
      (sqCubicNormalIndexDegree w + 1) (sqCubicNormalIndexDegree w + 1)
      (by omega) le_rfl _
  · exact Submodule.zero_mem _

theorem sqCubicTruncatedLeftLetter_strictlyRaises (h : ℕ)
    (i : Fin (sqRank h)) :
    SqCubicStrictlyRaises (sqCubicTruncatedLeftLetter h i) := by
  intro n f hf
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      have hfw : f w = 0 := by
        simpa [Finsupp.mem_support_iff] using hw
      have hwmem : w ∈ (Finsupp.single w a + f).support := by
        simp [Finsupp.mem_support_iff, hfw, ha]
      have hwdeg : n ≤ sqCubicNormalIndexDegree w := by
        rw [sqCubicNormalFiltration, Finsupp.mem_supported] at hf
        exact hf hwmem
      have hfmem : f ∈ sqCubicNormalFiltration h n := by
        rw [sqCubicNormalFiltration, Finsupp.mem_supported] at hf ⊢
        intro v hv
        apply hf
        change v ∈ f.support at hv
        change v ∈ (Finsupp.single w a + f).support
        rw [Finsupp.mem_support_iff] at hv ⊢
        by_cases e : v = w
        · subst v
          exact (hw (Finsupp.mem_support_iff.mpr hv)).elim
        · simp [e, hv]
      rw [map_add]
      apply Submodule.add_mem
      · rw [sqCubicTruncatedLeftLetter_single]
        exact Submodule.smul_mem _ a
          (sqCubicNormalFiltration_antitone h
            (Nat.add_le_add_right hwdeg 1)
            (sqCubicTruncatedLeftLetterOnIndex_mem h i w))
      · exact ih hfmem

/-- The homogeneous truncated Diamond letter as an element of the strict nonunital algebra. -/
def sqCubicHomogeneousStrictLetter (h : ℕ) (i : Fin (sqRank h)) :
    sqCubicStrictEnd h :=
  ⟨sqCubicTruncatedLeftLetter h i,
    sqCubicTruncatedLeftLetter_strictlyRaises h i⟩

/-- The same marked letter in the unitized finite operator algebra. -/
def sqCubicHomogeneousOperatorLetter (h : ℕ) (i : Fin (sqRank h)) :
    SqCubicOperatorAlgebra h :=
  (sqCubicHomogeneousStrictLetter h i : SqCubicOperatorAlgebra h)

@[simp] theorem sqCubicHomogeneousOperatorLetter_augmentation (h : ℕ)
    (i : Fin (sqRank h)) :
    sqCubicOperatorAugmentation h (sqCubicHomogeneousOperatorLetter h i) = 0 := by
  simp [sqCubicHomogeneousOperatorLetter, sqCubicOperatorAugmentation]

/-- On a homogeneous layer below degree three, the truncated operator is exactly the
homogeneous projection of the Diamond left action. -/
theorem sqCubicTruncatedLeftLetter_embed (h n : ℕ) (hn : n < 3)
    (i : Fin (sqRank h)) (f : SqQuadraticHomogeneousNormalSpace h n) :
    sqCubicTruncatedLeftLetter h i
        (sqCubicHomogeneousEmbed h n (by omega) f) =
      sqCubicHomogeneousEmbed h (n + 1) (by omega)
        (sqQuadraticHomogeneousProject h (n + 1)
          (sqNormalLeftLetter h i (sqQuadraticHomogeneousInclude h n f))) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add w a f hw ha ih =>
      rw [map_add, map_add, map_add, map_add, ih,
        sqCubicHomogeneousEmbed_single,
        sqCubicTruncatedLeftLetter_single]
      have hidx : sqCubicNormalIndexDegree
          (sqCubicNormalIndexOfHomogeneous h n (by omega) w) = n := rfl
      rw [sqCubicTruncatedLeftLetterOnIndex, dif_pos (by simpa [hidx] using hn)]
      dsimp only [sqCubicNormalIndexDegree, sqCubicNormalIndexOfHomogeneous]
      have hinclude : sqQuadraticHomogeneousInclude h n
          (Finsupp.single w a) = Finsupp.single w.1 a := by
        simp [sqQuadraticHomogeneousInclude]
      rw [hinclude, map_add, map_add]
      apply congrArg₂ (· + ·)
      · have hsingle : sqNormalLeftLetter h i (Finsupp.single w.1 a) =
            a • sqNormalLeftLetter h i (Finsupp.single w.1 1) := by
          rw [← map_smul]
          simp
        rw [hsingle, map_smul, map_smul]
        congr 1
      · rfl

/-- The degree-zero empty PBW basis vector in the four-step space. -/
def sqCubicEmptyVector (h : ℕ) : SqCubicNormalSpace h :=
  sqCubicHomogeneousEmbed h 0 (by omega)
    (Finsupp.single (sqQuadraticHomogeneousEmpty h) 1)

/-- The degree-zero empty index. -/
def sqCubicEmptyIndex (h : ℕ) : SqCubicNormalIndex h :=
  sqCubicNormalIndexOfHomogeneous h 0 (by omega)
    (sqQuadraticHomogeneousEmpty h)

@[simp] theorem sqCubicEmptyVector_eq_single (h : ℕ) :
    sqCubicEmptyVector h = Finsupp.single (sqCubicEmptyIndex h) 1 := by
  simp [sqCubicEmptyVector, sqCubicEmptyIndex]

theorem sqCubicNormalIndex_eq_empty_of_degree_zero (h : ℕ)
    (w : SqCubicNormalIndex h) (hw : sqCubicNormalIndexDegree w = 0) :
    w = sqCubicEmptyIndex h := by
  rcases w with ⟨n, w⟩
  have hn : n = 0 := Fin.ext hw
  subst n
  have hl : w.1.1 = [] := List.eq_nil_of_length_eq_zero w.2
  apply Sigma.ext
  · rfl
  · apply heq_of_eq
    apply Subtype.ext
    apply Subtype.ext
    exact hl

theorem sqCubicEmptyVector_mem_filtration_zero (h : ℕ) :
    sqCubicEmptyVector h ∈ sqCubicNormalFiltration h 0 := by simp

/-- PBW normalization of a list, retained in its homogeneous degree. -/
def sqCubicListPBWNormal (h : ℕ) (l : List (Fin (sqRank h))) :
    SqQuadraticHomogeneousNormalSpace h l.length :=
  sqQuadraticHomogeneousProject h l.length
    (sqQuadraticNormalRepr h
      (quadraticWordEval (SqQuadraticAlgebra h)
        (sqQuadraticQuotientLetter h) l))

/-- The truncated homogeneous Diamond word operator sends the empty vector to the embedded
PBW normal form, for every word of length below four. -/
theorem sqCubicTruncatedWord_apply_empty (h : ℕ)
    (l : List (Fin (sqRank h))) (hl : l.length < 4) :
    quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicTruncatedLeftLetter h) l (sqCubicEmptyVector h) =
      sqCubicHomogeneousEmbed h l.length hl (sqCubicListPBWNormal h l) := by
  induction l with
  | nil =>
      change sqCubicEmptyVector h =
        sqCubicHomogeneousEmbed h 0 hl (sqCubicListPBWNormal h [])
      rw [sqCubicEmptyVector, sqCubicListPBWNormal]
      have hr := sqQuadraticNormalRepr_word h (sqQuadraticNormalEmpty h)
      change sqQuadraticNormalRepr h
          (quadraticWordEval (SqQuadraticAlgebra h)
            (sqQuadraticQuotientLetter h) []) = _ at hr
      rw [hr]
      congr 1
      have H0 := sqQuadraticWordPBWNormal_zero h PUnit.unit
      change sqQuadraticHomogeneousProject h 0
          (sqQuadraticNormalRepr h
            (quadraticWordEval (SqQuadraticAlgebra h)
              (sqQuadraticQuotientLetter h) [])) = _ at H0
      rw [hr] at H0
      exact H0.symm
  | cons i l ih =>
      simp only [List.length_cons] at hl
      have htail : l.length < 3 := by omega
      change sqCubicTruncatedLeftLetter h i
          (quadraticWordEval
            (Module.End (ZMod 2) (SqCubicNormalSpace h))
            (sqCubicTruncatedLeftLetter h) l (sqCubicEmptyVector h)) = _
      rw [ih (by omega), sqCubicTruncatedLeftLetter_embed h l.length htail]
      rw [sqCubicListPBWNormal]
      have hsupp := sqQuadraticNormalRepr_word_supported h l
      rw [sqQuadraticHomogeneousInclude_project_of_supported h l.length _ hsupp]
      change sqCubicHomogeneousEmbed h (l.length + 1) _
          (sqQuadraticHomogeneousProject h (l.length + 1)
            (sqNormalLeftLetter h i
              (sqQuadraticNormalRepr h
                (quadraticWordEval (SqQuadraticAlgebra h)
                  (sqQuadraticQuotientLetter h) l)))) = _
      rw [← sqQuadraticNormalRepr_letter_mul]
      rfl

/-- Recursive cubic words give the same PBW column when evaluated by the truncated
homogeneous Diamond operators. -/
theorem sqCubicTruncatedWord_apply_empty_recursive (h : ℕ)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicTruncatedLeftLetter h) (finiteGeneratorWordList 3 w)
        (sqCubicEmptyVector h) =
      sqCubicHomogeneousEmbed h 3 (by omega)
        (sqQuadraticWordPBWNormal h 3 w) := by
  rcases w with ⟨⟨⟨u, i⟩, j⟩, k⟩
  rcases u with ⟨⟩
  simpa [finiteGeneratorWordList, sqQuadraticWordPBWNormal,
    sqCubicListPBWNormal] using
    sqCubicTruncatedWord_apply_empty h [i, j, k] (by simp)

/-! ## Degree-two corrections do not change cubic columns -/

/-- An endomorphism raises the four-step filtration by at least `r`. -/
def SqCubicRaisesBy {h : ℕ}
    (T : Module.End (ZMod 2) (SqCubicNormalSpace h)) (r : ℕ) : Prop :=
  ∀ n x, x ∈ sqCubicNormalFiltration h n →
    T x ∈ sqCubicNormalFiltration h (n + r)

theorem SqCubicRaisesBy.add {h r : ℕ}
    {T U : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (hU : SqCubicRaisesBy U r) :
    SqCubicRaisesBy (T + U) r := by
  intro n x hx
  exact Submodule.add_mem _ (hT n x hx) (hU n x hx)

theorem SqCubicRaisesBy.sub {h r : ℕ}
    {T U : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (hU : SqCubicRaisesBy U r) :
    SqCubicRaisesBy (T - U) r := by
  intro n x hx
  exact Submodule.sub_mem _ (hT n x hx) (hU n x hx)

theorem SqCubicRaisesBy.smul {h r : ℕ}
    {T : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (a : ZMod 2) :
    SqCubicRaisesBy (a • T) r := by
  intro n x hx
  exact Submodule.smul_mem _ a (hT n x hx)

theorem SqCubicRaisesBy.mul {h r s : ℕ}
    {T U : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (hU : SqCubicRaisesBy U s) :
    SqCubicRaisesBy (T * U) (r + s) := by
  intro n x hx
  change T (U x) ∈ sqCubicNormalFiltration h (n + (r + s))
  have hUx := hU n x hx
  have hTUx := hT (n + s) (U x) hUx
  simpa [add_assoc, add_comm, add_left_comm] using hTUx

theorem sqCubicTruncatedLeftLetter_raises_one (h : ℕ)
    (i : Fin (sqRank h)) :
    SqCubicRaisesBy (sqCubicTruncatedLeftLetter h i) 1 :=
  sqCubicTruncatedLeftLetter_strictlyRaises h i

theorem SqCubicRaisesBy.strict {h r : ℕ}
    {T : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (hr : 1 ≤ r) :
    SqCubicStrictlyRaises T := by
  intro n x hx
  exact sqCubicNormalFiltration_antitone h
    (Nat.add_le_add_left hr n) (hT n x hx)

theorem SqCubicRaisesBy.eq_zero_of_four_le {h r : ℕ}
    {T : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (hr : 4 ≤ r) : T = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x ∈ sqCubicNormalFiltration h 0 := by simp
  have hTx := hT 0 x hx
  have hTx4 : T x ∈ sqCubicNormalFiltration h 4 :=
    sqCubicNormalFiltration_antitone h (by simpa using hr) hTx
  rw [sqCubicNormalFiltration_four] at hTx4
  exact hTx4

theorem SqCubicRaisesBy.apply_eq_zero_of_mem_one {h r : ℕ}
    {T : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T r) (hr : 3 ≤ r)
    (x : SqCubicNormalSpace h) (hx : x ∈ sqCubicNormalFiltration h 1) :
    T x = 0 := by
  have hTx := hT 1 x hx
  have hTx4 : T x ∈ sqCubicNormalFiltration h 4 :=
    sqCubicNormalFiltration_antitone h (by omega) hTx
  rw [sqCubicNormalFiltration_four] at hTx4
  exact hTx4

/-- A filtration-three endomorphism is determined by its value on the empty vector. -/
theorem sqCubicEnd_eq_of_raises_three
    {h : ℕ} {T U : Module.End (ZMod 2) (SqCubicNormalSpace h)}
    (hT : SqCubicRaisesBy T 3) (hU : SqCubicRaisesBy U 3)
    (he : T (sqCubicEmptyVector h) = U (sqCubicEmptyVector h)) :
    T = U := by
  apply Finsupp.lhom_ext
  intro w a
  by_cases hw : sqCubicNormalIndexDegree w = 0
  · rw [sqCubicNormalIndex_eq_empty_of_degree_zero h w hw,
      ← Finsupp.smul_single_one, ← sqCubicEmptyVector_eq_single,
      map_smul, map_smul, he]
  · have hw1 : 1 ≤ sqCubicNormalIndexDegree w := Nat.one_le_iff_ne_zero.mpr hw
    have hsingle : Finsupp.single w a ∈ sqCubicNormalFiltration h 1 := by
      rw [sqCubicNormalFiltration, Finsupp.mem_supported]
      intro v hv
      by_cases ha : a = 0
      · subst a
        simp at hv
      have hvw : v = w := by
        simpa [Finsupp.mem_support_iff, ha] using hv
      subst v
      exact hw1
    rw [hT.apply_eq_zero_of_mem_one (by omega) _ hsingle,
      hU.apply_eq_zero_of_mem_one (by omega) _ hsingle]

/-- A family of corrections which starts two degrees deeper than an ordinary marked
letter. -/
structure SqCubicDegreeTwoCorrection (h : ℕ) where
  operator : Fin (sqRank h) →
    Module.End (ZMod 2) (SqCubicNormalSpace h)
  raises_two : ∀ i, SqCubicRaisesBy (operator i) 2

/-- Add a degree-two correction to each truncated homogeneous Diamond letter. -/
def sqCubicCorrectedLeftLetter (h : ℕ) (D : SqCubicDegreeTwoCorrection h)
    (i : Fin (sqRank h)) : Module.End (ZMod 2) (SqCubicNormalSpace h) :=
  sqCubicTruncatedLeftLetter h i + D.operator i

theorem sqCubicCorrectedLeftLetter_raises_one (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    SqCubicRaisesBy (sqCubicCorrectedLeftLetter h D i) 1 := by
  apply SqCubicRaisesBy.add (sqCubicTruncatedLeftLetter_raises_one h i)
  intro n x hx
  exact sqCubicNormalFiltration_antitone h (by omega)
    (D.raises_two i n x hx)

/-- The corrected marked letter in the strict nonunital algebra. -/
def sqCubicCorrectedStrictLetter (h : ℕ) (D : SqCubicDegreeTwoCorrection h)
    (i : Fin (sqRank h)) : sqCubicStrictEnd h :=
  ⟨sqCubicCorrectedLeftLetter h D i,
    (sqCubicCorrectedLeftLetter_raises_one h D i).strict le_rfl⟩

/-- The corrected marked letter in the unitized operator algebra. -/
def sqCubicCorrectedOperatorLetter (h : ℕ) (D : SqCubicDegreeTwoCorrection h)
    (i : Fin (sqRank h)) : SqCubicOperatorAlgebra h :=
  (sqCubicCorrectedStrictLetter h D i : SqCubicOperatorAlgebra h)

@[simp] theorem sqCubicCorrectedOperatorLetter_augmentation (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    sqCubicOperatorAugmentation h (sqCubicCorrectedOperatorLetter h D i) = 0 := by
  simp [sqCubicCorrectedOperatorLetter, sqCubicOperatorAugmentation]

theorem sqCubicCorrectedLeftLetter_product_three (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i j k : Fin (sqRank h)) :
    sqCubicCorrectedLeftLetter h D i *
          sqCubicCorrectedLeftLetter h D j *
          sqCubicCorrectedLeftLetter h D k =
      sqCubicTruncatedLeftLetter h i *
          sqCubicTruncatedLeftLetter h j *
          sqCubicTruncatedLeftLetter h k := by
  let H := sqCubicTruncatedLeftLetter h
  let E := D.operator
  have hH (q : Fin (sqRank h)) : SqCubicRaisesBy (H q) 1 :=
    sqCubicTruncatedLeftLetter_raises_one h q
  have hE (q : Fin (sqRank h)) : SqCubicRaisesBy (E q) 2 := D.raises_two q
  have hEHH : E i * H j * H k = 0 :=
    ((hE i).mul (hH j) |>.mul (hH k)).eq_zero_of_four_le (by omega)
  have hHEH : H i * E j * H k = 0 :=
    ((hH i).mul (hE j) |>.mul (hH k)).eq_zero_of_four_le (by omega)
  have hHHE : H i * H j * E k = 0 :=
    ((hH i).mul (hH j) |>.mul (hE k)).eq_zero_of_four_le (by omega)
  have hEEH : E i * E j * H k = 0 :=
    ((hE i).mul (hE j) |>.mul (hH k)).eq_zero_of_four_le (by omega)
  have hEHE : E i * H j * E k = 0 :=
    ((hE i).mul (hH j) |>.mul (hE k)).eq_zero_of_four_le (by omega)
  have hHEE : H i * E j * E k = 0 :=
    ((hH i).mul (hE j) |>.mul (hE k)).eq_zero_of_four_le (by omega)
  have hEEE : E i * E j * E k = 0 :=
    ((hE i).mul (hE j) |>.mul (hE k)).eq_zero_of_four_le (by omega)
  change (H i + E i) * (H j + E j) * (H k + E k) = H i * H j * H k
  calc
    (H i + E i) * (H j + E j) * (H k + E k) =
        H i * H j * H k + H i * H j * E k +
          H i * E j * H k + H i * E j * E k +
          E i * H j * H k + E i * H j * E k +
          E i * E j * H k + E i * E j * E k := by noncomm_ring
    _ = H i * H j * H k := by
      rw [hEHH, hHEH, hHHE, hEEH, hEHE, hHEE, hEEE]
      simp

/-- Degree-two corrections leave every literal cubic PBW column unchanged. -/
theorem sqCubicCorrectedWord_apply_empty_recursive (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicCorrectedLeftLetter h D) (finiteGeneratorWordList 3 w)
        (sqCubicEmptyVector h) =
      sqCubicHomogeneousEmbed h 3 (by omega)
        (sqQuadraticWordPBWNormal h 3 w) := by
  rcases w with ⟨⟨⟨u, i⟩, j⟩, k⟩
  rcases u with ⟨⟩
  change (sqCubicCorrectedLeftLetter h D i *
      sqCubicCorrectedLeftLetter h D j *
      sqCubicCorrectedLeftLetter h D k) (sqCubicEmptyVector h) = _
  rw [sqCubicCorrectedLeftLetter_product_three]
  have H := sqCubicTruncatedWord_apply_empty_recursive h
    (((PUnit.unit, i), j), k)
  change (sqCubicTruncatedLeftLetter h i *
      sqCubicTruncatedLeftLetter h j *
      sqCubicTruncatedLeftLetter h k) (sqCubicEmptyVector h) = _ at H
  exact H

/-- A corrected word operator raises filtration by its word length. -/
theorem sqCubicCorrectedWord_raises (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    ∀ l : List (Fin (sqRank h)),
      SqCubicRaisesBy
        (quadraticWordEval
          (Module.End (ZMod 2) (SqCubicNormalSpace h))
          (sqCubicCorrectedLeftLetter h D) l) l.length := by
  intro l
  induction l with
  | nil =>
      intro n x hx
      simpa [quadraticWordEval] using hx
  | cons i l ih =>
      change SqCubicRaisesBy
        (sqCubicCorrectedLeftLetter h D i *
          quadraticWordEval
            (Module.End (ZMod 2) (SqCubicNormalSpace h))
            (sqCubicCorrectedLeftLetter h D) l) (i :: l).length
      simpa only [List.length_cons, Nat.add_comm] using
        (sqCubicCorrectedLeftLetter_raises_one h D i).mul ih

/-- A normal cubic word acts on the empty vector by its own embedded basis vector. -/
theorem sqCubicCorrectedNormalWord_apply_empty (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (v : SqQuadraticHomogeneousNormalWord h 3) :
    quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicCorrectedLeftLetter h D) v.1.1 (sqCubicEmptyVector h) =
      sqCubicHomogeneousEmbed h 3 (by omega) (Finsupp.single v 1) := by
  obtain ⟨w, hw⟩ := finiteGeneratorWordList_exists 3 v.1.1 v.2
  have H := sqCubicCorrectedWord_apply_empty_recursive h D w
  rw [hw] at H
  have hnormal : sqQuadraticWordPBWNormal h 3 w = Finsupp.single v 1 := by
    rw [sqQuadraticWordPBWNormal, hw, sqQuadraticNormalRepr_word h v.1]
    ext u
    by_cases hu : u = v
    · subst u
      simp [sqQuadraticHomogeneousProject]
    · have hu' : u.1 ≠ v.1 := by
        intro e
        apply hu
        exact Subtype.ext e
      simp [sqQuadraticHomogeneousProject, hu]
  rwa [hnormal] at H

/-- Linear evaluation of cubic normal words in corrected endomorphisms. -/
def sqCubicCorrectedNormalEndEval (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    SqQuadraticHomogeneousNormalSpace h 3 →ₗ[ZMod 2]
      Module.End (ZMod 2) (SqCubicNormalSpace h) :=
  Finsupp.lsum (ZMod 2) fun v =>
    LinearMap.toSpanSingleton (ZMod 2)
      (Module.End (ZMod 2) (SqCubicNormalSpace h))
      (quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicCorrectedLeftLetter h D) v.1.1)

@[simp] theorem sqCubicCorrectedNormalEndEval_single (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (v : SqQuadraticHomogeneousNormalWord h 3) (a : ZMod 2) :
    sqCubicCorrectedNormalEndEval h D (Finsupp.single v a) =
      a • quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicCorrectedLeftLetter h D) v.1.1 := by
  simp [sqCubicCorrectedNormalEndEval]

theorem sqCubicCorrectedNormalEndEval_raises_three (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (f : SqQuadraticHomogeneousNormalSpace h 3) :
    SqCubicRaisesBy (sqCubicCorrectedNormalEndEval h D f) 3 := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      intro n x hx
      exact Submodule.zero_mem _
  | single_add v a f hv ha ih =>
      rw [map_add, sqCubicCorrectedNormalEndEval_single]
      apply SqCubicRaisesBy.add
      · apply SqCubicRaisesBy.smul
        simpa [v.2] using sqCubicCorrectedWord_raises h D v.1.1
      · exact ih

theorem sqCubicCorrectedNormalEndEval_apply_empty (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (f : SqQuadraticHomogeneousNormalSpace h 3) :
    sqCubicCorrectedNormalEndEval h D f (sqCubicEmptyVector h) =
      sqCubicHomogeneousEmbed h 3 (by omega) f := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add v a f hv ha ih =>
      rw [map_add, LinearMap.add_apply,
        sqCubicCorrectedNormalEndEval_single, LinearMap.smul_apply,
        sqCubicCorrectedNormalWord_apply_empty, map_add, ih]
      apply congrArg₂ (· + ·)
      · have hs : Finsupp.single v a = a • Finsupp.single v 1 := by simp
        rw [hs, map_smul]
      · rfl

/-- **Finite cubic confluence.**  Every corrected literal cubic word operator equals the
linear combination of normal cubic word operators prescribed by the quadratic Diamond
normalizer.  The proof uses only the four-step filtration and the empty-vector regressions. -/
theorem sqCubicCorrectedCubicEndNormalization (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicCorrectedLeftLetter h D) (finiteGeneratorWordList 3 w) =
      sqCubicCorrectedNormalEndEval h D (sqQuadraticWordPBWNormal h 3 w) := by
  apply sqCubicEnd_eq_of_raises_three
  · simpa [finiteGeneratorWordList_length] using
      sqCubicCorrectedWord_raises h D (finiteGeneratorWordList 3 w)
  · exact sqCubicCorrectedNormalEndEval_raises_three h D _
  · rw [sqCubicCorrectedWord_apply_empty_recursive,
      sqCubicCorrectedNormalEndEval_apply_empty]

/-! ## Translation to the unitized finite algebra -/

theorem sqCubicCorrectedOperatorWord_fst_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (l : List (Fin (sqRank h))) (hl : l ≠ []) :
    (quadraticWordEval (SqCubicOperatorAlgebra h)
      (sqCubicCorrectedOperatorLetter h D) l).fst = 0 := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons i l ih =>
      change (sqCubicCorrectedOperatorLetter h D i *
        quadraticWordEval (SqCubicOperatorAlgebra h)
          (sqCubicCorrectedOperatorLetter h D) l).fst = 0
      rw [Unitization.fst_mul]
      have hi := sqCubicCorrectedOperatorLetter_augmentation h D i
      change (sqCubicCorrectedOperatorLetter h D i).fst = 0 at hi
      rw [hi, zero_mul]

theorem sqCubicCorrectedOperatorWord_snd (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (l : List (Fin (sqRank h))) (hl : l.length = 3) :
    ((quadraticWordEval (SqCubicOperatorAlgebra h)
        (sqCubicCorrectedOperatorLetter h D) l).snd.1 :
      Module.End (ZMod 2) (SqCubicNormalSpace h)) =
      quadraticWordEval
        (Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicCorrectedLeftLetter h D) l := by
  cases l with
  | nil => simp at hl
  | cons i l =>
      cases l with
      | nil => simp at hl
      | cons j l =>
          cases l with
          | nil => simp at hl
          | cons k l =>
              have hl0 : l = [] :=
                List.eq_nil_of_length_eq_zero (by simpa using hl)
              subst l
              simp only [quadraticWordEval, List.map_cons, List.prod_cons,
                List.map_nil, List.prod_nil, mul_one]
              simp [sqCubicCorrectedOperatorLetter,
                sqCubicCorrectedStrictLetter, Unitization.snd_mul]

theorem sqCubicCorrectedNormalOperatorLinearCombination_fst_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (f : SqQuadraticHomogeneousNormalSpace h 3) :
    (Finsupp.linearCombination (ZMod 2)
      (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
        quadraticWordEval (SqCubicOperatorAlgebra h)
          (sqCubicCorrectedOperatorLetter h D) v.1.1) f).fst = 0 := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add v a f hv ha ih =>
      rw [map_add, Unitization.fst_add, ih]
      simp only [Finsupp.linearCombination_single]
      rw [Unitization.fst_smul,
        sqCubicCorrectedOperatorWord_fst_zero h D v.1.1]
      · simp
      · intro e
        have hvlen := v.2
        rw [e] at hvlen
        simp at hvlen

theorem sqCubicCorrectedNormalOperatorLinearCombination_snd (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (f : SqQuadraticHomogeneousNormalSpace h 3) :
    ((Finsupp.linearCombination (ZMod 2)
        (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
          quadraticWordEval (SqCubicOperatorAlgebra h)
            (sqCubicCorrectedOperatorLetter h D) v.1.1) f).snd.1 :
      Module.End (ZMod 2) (SqCubicNormalSpace h)) =
      sqCubicCorrectedNormalEndEval h D f := by
  classical
  induction f using Finsupp.induction with
  | zero => simp [sqCubicCorrectedNormalEndEval]
  | single_add v a f hv ha ih =>
      rw [map_add, Unitization.snd_add, map_add]
      change
        ((Finsupp.linearCombination (ZMod 2)
          (fun u : SqQuadraticHomogeneousNormalWord h 3 =>
            quadraticWordEval (SqCubicOperatorAlgebra h)
              (sqCubicCorrectedOperatorLetter h D) u.1.1)
          (Finsupp.single v a)).snd.1 :
            Module.End (ZMod 2) (SqCubicNormalSpace h)) +
          ((Finsupp.linearCombination (ZMod 2)
            (fun u : SqQuadraticHomogeneousNormalWord h 3 =>
              quadraticWordEval (SqCubicOperatorAlgebra h)
                (sqCubicCorrectedOperatorLetter h D) u.1.1) f).snd.1 :
            Module.End (ZMod 2) (SqCubicNormalSpace h)) =
          sqCubicCorrectedNormalEndEval h D (Finsupp.single v a) +
            sqCubicCorrectedNormalEndEval h D f
      rw [ih, Finsupp.linearCombination_single,
        Unitization.snd_smul, sqCubicCorrectedNormalEndEval_single]
      apply congrArg₂ (· + ·)
      · apply congrArg (fun T => a • T)
        exact sqCubicCorrectedOperatorWord_snd h D v.1.1 v.2
      · rfl

/-- Cubic normalization in the actual unitized finite operator algebra. -/
theorem sqCubicCorrectedOperator_cubic_normalization (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (w : FiniteGeneratorWord (Fin (sqRank h)) 3) :
    quadraticWordEval (SqCubicOperatorAlgebra h)
        (sqCubicCorrectedOperatorLetter h D) (finiteGeneratorWordList 3 w) =
      Finsupp.linearCombination (ZMod 2)
        (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
          quadraticWordEval (SqCubicOperatorAlgebra h)
            (sqCubicCorrectedOperatorLetter h D) v.1.1)
        (sqQuadraticWordPBWNormal h 3 w) := by
  apply Unitization.ext
  · rw [sqCubicCorrectedOperatorWord_fst_zero h D]
    · exact sqCubicCorrectedNormalOperatorLinearCombination_fst_zero h D _ |>.symm
    · intro e
      have := finiteGeneratorWordList_length 3 w
      rw [e] at this
      simp at this
  · apply Subtype.ext
    exact (sqCubicCorrectedOperatorWord_snd h D _
      (finiteGeneratorWordList_length 3 w)).trans
        ((sqCubicCorrectedCubicEndNormalization h D w).trans
          (sqCubicCorrectedNormalOperatorLinearCombination_snd h D _).symm)

theorem sqCubicNormalIndexOfHomogeneous_injective (h n : ℕ) (hn : n < 4) :
    Function.Injective (sqCubicNormalIndexOfHomogeneous h n hn) := by
  intro u v e
  have huv := congrArg (fun z : SqCubicNormalIndex h => z.2.1.1) e
  apply Subtype.ext
  apply Subtype.ext
  exact huv

theorem sqCubicHomogeneousEmbed_injective (h n : ℕ) (hn : n < 4) :
    Function.Injective (sqCubicHomogeneousEmbed h n hn) := by
  intro f g e
  change Finsupp.mapDomain (sqCubicNormalIndexOfHomogeneous h n hn) f =
      Finsupp.mapDomain (sqCubicNormalIndexOfHomogeneous h n hn) g at e
  exact Finsupp.mapDomain_injective
    (sqCubicNormalIndexOfHomogeneous_injective h n hn) e

/-- Corrected normal cubic word values are independent in the finite operator algebra. -/
theorem sqCubicCorrectedOperator_normal_independent (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    LinearIndependent (ZMod 2)
      (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
        quadraticWordEval (SqCubicOperatorAlgebra h)
          (sqCubicCorrectedOperatorLetter h D) v.1.1) := by
  change Function.Injective (Finsupp.linearCombination (ZMod 2)
    (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
      quadraticWordEval (SqCubicOperatorAlgebra h)
        (sqCubicCorrectedOperatorLetter h D) v.1.1))
  intro f g hfg
  have hsnd := congrArg (fun a : SqCubicOperatorAlgebra h =>
    ((a.snd.1 : Module.End (ZMod 2) (SqCubicNormalSpace h))
      (sqCubicEmptyVector h))) hfg
  have heval (k : SqQuadraticHomogeneousNormalSpace h 3) :
      (((Finsupp.linearCombination (ZMod 2)
          (fun v : SqQuadraticHomogeneousNormalWord h 3 =>
            quadraticWordEval (SqCubicOperatorAlgebra h)
              (sqCubicCorrectedOperatorLetter h D) v.1.1) k).snd.1 :
        Module.End (ZMod 2) (SqCubicNormalSpace h))
          (sqCubicEmptyVector h)) =
        sqCubicHomogeneousEmbed h 3 (by omega) k := by
    rw [sqCubicCorrectedNormalOperatorLinearCombination_snd,
      sqCubicCorrectedNormalEndEval_apply_empty]
  have hemb : sqCubicHomogeneousEmbed h 3 (by omega) f =
      sqCubicHomogeneousEmbed h 3 (by omega) g := by
    exact (heval f).symm.trans (hsnd.trans (heval g))
  exact sqCubicHomogeneousEmbed_injective h 3 (by omega)
    hemb

/-! ## The exact finite inhomogeneous correction equation -/

theorem sqCubicCorrectedOperatorLetter_pow_four_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    (sqCubicCorrectedOperatorLetter h D i) ^ 4 = 0 :=
  pow_four_zero_of_augmentation_product_four_zero
    (sqCubicOperatorAugmentation h)
    (sqCubicOperatorAugmentation_product_four_zero h)
    (sqCubicCorrectedOperatorLetter h D i)
    (sqCubicCorrectedOperatorLetter_augmentation h D i)

/-- The corrected augmentation-one marking in the finite operator algebra. -/
def sqCubicCorrectedMarkedUnit (h : ℕ) (D : SqCubicDegreeTwoCorrection h)
    (i : Fin (sqRank h)) : (SqCubicOperatorAlgebra h)ˣ :=
  oneAddUnitOfPowFourZero
    (sqCubicCorrectedOperatorLetter h D i)
    (sqCubicCorrectedOperatorLetter_pow_four_zero h D i)

/-- The literal improved relator evaluated on the corrected finite marking. -/
def sqCubicCorrectedRelatorUnit (h : ℕ) (D : SqCubicDegreeTwoCorrection h) :
    (SqCubicOperatorAlgebra h)ˣ :=
  sqRelWord (sqCubicCorrectedMarkedUnit h D)

/-- The non-scalar endomorphism block of the corrected literal relator. -/
def sqCubicCorrectedRelatorEnd (h : ℕ) (D : SqCubicDegreeTwoCorrection h) :
    Module.End (ZMod 2) (SqCubicNormalSpace h) :=
  (sqCubicCorrectedRelatorUnit h D).val.snd.1

/-- A matrix entry of the corrected literal relator on the PBW-normal basis. -/
def sqCubicCorrectedRelatorBlock (h : ℕ) (D : SqCubicDegreeTwoCorrection h)
    (source target : SqCubicNormalIndex h) : ZMod 2 :=
  sqCubicCorrectedRelatorEnd h D
    (Finsupp.single source 1) target

@[simp] theorem sqCubicCorrectedMarkedUnit_augmentation (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    Units.map (sqCubicOperatorAugmentation h).toMonoidHom
        (sqCubicCorrectedMarkedUnit h D i) = 1 := by
  apply Units.ext
  simp [sqCubicCorrectedMarkedUnit,
    sqCubicCorrectedOperatorLetter_augmentation]

theorem sqRelWord_one {G : Type} [Group G] {h : ℕ} :
    sqRelWord (fun _ : Fin (sqRank h) => (1 : G)) = 1 := by
  rw [sqRelWord]
  have hh : GQ2.Dyadic.MarkedCore.handleWord
      (fun _ : Fin h => (1 : G)) (fun _ : Fin h => (1 : G)) = 1 :=
    GQ2.Dyadic.MarkedCore.handleWord_of_one _ _ (fun _ => rfl) (fun _ => rfl)
  rw [hh]
  simp [sqWord, conjP, commP]

@[simp] theorem sqCubicCorrectedRelatorUnit_fst (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    (sqCubicCorrectedRelatorUnit h D).val.fst = 1 := by
  let ε := Units.map (sqCubicOperatorAugmentation h).toMonoidHom
  have hmark : (λ i => ε (sqCubicCorrectedMarkedUnit h D i)) =
      (fun _ : Fin (sqRank h) => (1 : (ZMod 2)ˣ)) := by
    funext i
    exact sqCubicCorrectedMarkedUnit_augmentation h D i
  have hrel : ε (sqCubicCorrectedRelatorUnit h D) = 1 := by
    rw [sqCubicCorrectedRelatorUnit, map_sqRelWord, hmark, sqRelWord_one]
  have hval := congrArg Units.val hrel
  simpa [ε, sqCubicOperatorAugmentation] using hval

/-- The one remaining finite equation for a degree-two correction: the full literal improved
relator must die on the corrected unipotent marked letters. -/
def SqCubicInhomogeneousRelatorEquation (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) : Prop :=
  sqCubicCorrectedRelatorUnit h D = 1

/-- The literal relator equation is exactly the vanishing of its finite endomorphism block. -/
theorem sqCubicInhomogeneousRelatorEquation_iff_end_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    SqCubicInhomogeneousRelatorEquation h D ↔
      sqCubicCorrectedRelatorEnd h D = 0 := by
  constructor
  · intro hrel
    have hval := congrArg Units.val hrel
    exact congrArg (fun a : SqCubicOperatorAlgebra h =>
      (a.snd.1 : Module.End (ZMod 2) (SqCubicNormalSpace h))) hval
  · intro hend
    apply Units.ext
    apply Unitization.ext
    · exact sqCubicCorrectedRelatorUnit_fst h D
    · apply Subtype.ext
      exact hend

/-- Equivalently, every source column of the finite relator endomorphism vanishes. -/
theorem sqCubicInhomogeneousRelatorEquation_iff_columns_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    SqCubicInhomogeneousRelatorEquation h D ↔
      ∀ source : SqCubicNormalIndex h,
        sqCubicCorrectedRelatorEnd h D (Finsupp.single source 1) = 0 := by
  rw [sqCubicInhomogeneousRelatorEquation_iff_end_zero]
  constructor
  · intro hend source
    rw [hend]
    rfl
  · intro hcolumns
    apply Finsupp.lhom_ext
    intro source a
    rw [← Finsupp.smul_single_one, map_smul, hcolumns, smul_zero]
    rfl

/-- Fully scalar form: the correction problem is the simultaneous vanishing of the finite
PBW-basis matrix of the literal improved relator. -/
theorem sqCubicInhomogeneousRelatorEquation_iff_blocks_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    SqCubicInhomogeneousRelatorEquation h D ↔
      ∀ source target : SqCubicNormalIndex h,
        sqCubicCorrectedRelatorBlock h D source target = 0 := by
  rw [sqCubicInhomogeneousRelatorEquation_iff_columns_zero]
  constructor
  · intro hcolumns source target
    change sqCubicCorrectedRelatorEnd h D
      (Finsupp.single source 1) target = 0
    rw [hcolumns source]
    rfl
  · intro hblocks source
    apply Finsupp.ext
    intro target
    exact hblocks source target

/-! ## The rank-one `X`-column correction -/

/-- The degree-one PBW index represented by a marked letter. -/
def sqCubicLetterIndex (h : ℕ) (i : Fin (sqRank h)) : SqCubicNormalIndex h :=
  sqCubicNormalIndexOfHomogeneous h 1 (by omega)
    (sqQuadraticHomogeneousLetter h i)

@[simp] theorem sqCubicLetterIndex_degree (h : ℕ) (i : Fin (sqRank h)) :
    sqCubicNormalIndexDegree (sqCubicLetterIndex h i) = 1 :=
  rfl

theorem sqCubicLetterIndex_ne_empty (h : ℕ) (i : Fin (sqRank h)) :
    sqCubicLetterIndex h i ≠ sqCubicEmptyIndex h := by
  intro e
  have := congrArg sqCubicNormalIndexDegree e
  simp [sqCubicLetterIndex, sqCubicEmptyIndex] at this

@[simp] theorem sqCubicTruncatedLeftLetter_apply_empty (h : ℕ)
    (i : Fin (sqRank h)) :
    sqCubicTruncatedLeftLetter h i (sqCubicEmptyVector h) =
      Finsupp.single (sqCubicLetterIndex h i) 1 := by
  have H := sqCubicTruncatedWord_apply_empty h [i] (by simp)
  change sqCubicTruncatedLeftLetter h i (sqCubicEmptyVector h) = _ at H
  rw [H]
  change sqCubicHomogeneousEmbed h 1 _ (sqCubicListPBWNormal h [i]) = _
  have hone := sqQuadraticWordPBWNormal_one h i
  change sqCubicListPBWNormal h [i] =
      Finsupp.single (sqQuadraticHomogeneousLetter h i) 1 at hone
  rw [hone, sqCubicHomogeneousEmbed_single]
  rfl

/-- A rank-one endomorphism supported on the column of the degree-one letter `i`. -/
def sqCubicRankOneLetterColumn (h : ℕ) (i : Fin (sqRank h))
    (v : SqCubicNormalSpace h) :
    Module.End (ZMod 2) (SqCubicNormalSpace h) :=
  (LinearMap.toSpanSingleton (ZMod 2) (SqCubicNormalSpace h) v).comp
    (Finsupp.lapply (sqCubicLetterIndex h i))

@[simp] theorem sqCubicRankOneLetterColumn_apply (h : ℕ)
    (i : Fin (sqRank h)) (v x : SqCubicNormalSpace h) :
    sqCubicRankOneLetterColumn h i v x =
      x (sqCubicLetterIndex h i) • v :=
  rfl

@[simp] theorem sqCubicRankOneLetterColumn_own_basis (h : ℕ)
    (i : Fin (sqRank h)) (v : SqCubicNormalSpace h) :
    sqCubicRankOneLetterColumn h i v
        (Finsupp.single (sqCubicLetterIndex h i) 1) = v := by
  simp

@[simp] theorem sqCubicRankOneLetterColumn_empty (h : ℕ)
    (i : Fin (sqRank h)) (v : SqCubicNormalSpace h) :
    sqCubicRankOneLetterColumn h i v (sqCubicEmptyVector h) = 0 := by
  rw [sqCubicRankOneLetterColumn_apply, sqCubicEmptyVector_eq_single]
  simp [sqCubicLetterIndex_ne_empty]

theorem sqCubicRankOneLetterColumn_raises_two (h : ℕ)
    (i : Fin (sqRank h)) (v : SqCubicNormalSpace h)
    (hv : v ∈ sqCubicNormalFiltration h 3) :
    SqCubicRaisesBy (sqCubicRankOneLetterColumn h i v) 2 := by
  intro n x hx
  by_cases hn : n ≤ 1
  · exact sqCubicNormalFiltration_antitone h (by omega)
      (Submodule.smul_mem _ _ hv)
  · have hcoeff : x (sqCubicLetterIndex h i) = 0 := by
      by_contra hne
      have hsupp : sqCubicLetterIndex h i ∈ x.support :=
        Finsupp.mem_support_iff.mpr hne
      rw [sqCubicNormalFiltration, Finsupp.mem_supported] at hx
      have := hx hsupp
      change n ≤ sqCubicNormalIndexDegree (sqCubicLetterIndex h i) at this
      rw [sqCubicLetterIndex_degree] at this
      omega
    rw [sqCubicRankOneLetterColumn_apply, hcoeff, zero_smul]
    exact Submodule.zero_mem _

/-- A correction supported only at the marked generator `X` (index `1`), on the source
column represented by the degree-one letter `S` (index `0`). -/
def sqCubicXFromSColumnCorrection (h : ℕ) (v : SqCubicNormalSpace h)
    (hv : v ∈ sqCubicNormalFiltration h 3) : SqCubicDegreeTwoCorrection h where
  operator i := if i = 1 then sqCubicRankOneLetterColumn h 0 v else 0
  raises_two i := by
    split_ifs with hi
    · exact sqCubicRankOneLetterColumn_raises_two h 0 v hv
    · exact fun _ _ _ => Submodule.zero_mem _

@[simp] theorem sqCubicXFromSColumnCorrection_X (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    (sqCubicXFromSColumnCorrection h v hv).operator 1 =
      sqCubicRankOneLetterColumn h 0 v := by
  simp [sqCubicXFromSColumnCorrection]

theorem sqCubicXFromSColumnCorrection_ne_X (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3)
    (i : Fin (sqRank h)) (hi : i ≠ 1) :
    (sqCubicXFromSColumnCorrection h v hv).operator i = 0 := by
  simp [sqCubicXFromSColumnCorrection, hi]

@[simp] theorem sqCubicXFromSColumnCorrection_X_on_S (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    (sqCubicXFromSColumnCorrection h v hv).operator 1
        (Finsupp.single (sqCubicLetterIndex h 0) 1) = v := by
  rw [sqCubicXFromSColumnCorrection_X,
    sqCubicRankOneLetterColumn_own_basis]

/-- The zero degree-two correction, used to name the uncorrected cubic residual. -/
def sqCubicZeroDegreeTwoCorrection (h : ℕ) : SqCubicDegreeTwoCorrection h where
  operator := 0
  raises_two := fun _ _ _ _ => Submodule.zero_mem _

/-- The source-empty residual of the literal improved relator before the rank-one correction. -/
def sqCubicHomogeneousRelatorResidual (h : ℕ) : SqCubicNormalSpace h :=
  sqCubicCorrectedRelatorEnd h (sqCubicZeroDegreeTwoCorrection h)
    (sqCubicEmptyVector h)

/-! ## Literal perturbation at the `X` letter -/

set_option maxHeartbeats 4000000 in
/-- Universal filtered ring calculation for the only prefix of the improved square core which
contains `X`.  Here `e` has filtration degree at least two, while `s` and `x` have degree at
least one.  The inverse polynomial of `1 + x + e` therefore changes the conjugate/cube prefix
by exactly the derivative of the quadratic initial form, `e*s + s*e`. -/
theorem cubicConjugateCubePrefix_perturbation
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (aug : A →ₐ[ZMod 2] ZMod 2)
    (hfour : ∀ a b c d : A,
      aug a = 0 → aug b = 0 → aug c = 0 → aug d = 0 →
        a * b * c * d = 0)
    (s x e : A) (has : aug s = 0) (hax : aug x = 0) (hae : aug e = 0)
    (heab : ∀ a b : A, aug a = 0 → aug b = 0 → e * a * b = 0)
    (haeb : ∀ a b : A, aug a = 0 → aug b = 0 → a * e * b = 0)
    (habe : ∀ a b : A, aug a = 0 → aug b = 0 → a * b * e = 0)
    (hee : e * e = 0) :
    (1 + s + s ^ 2 + s ^ 3) *
        (1 + x + x ^ 2 + x ^ 3 + e + x * e + e * x) *
        (1 + s) * (1 + x + e) =
      (1 + s + s ^ 2 + s ^ 3) *
        (1 + x + x ^ 2 + x ^ 3) * (1 + s) * (1 + x) +
          e * s + s * e := by
  have hfourR (a b c d : A) (ha : aug a = 0) (hb : aug b = 0)
      (hc : aug c = 0) (hd : aug d = 0) : a * (b * (c * d)) = 0 := by
    simpa [mul_assoc] using hfour a b c d ha hb hc hd
  have heabR (a b : A) (ha : aug a = 0) (hb : aug b = 0) :
      e * (a * b) = 0 := by simpa [mul_assoc] using heab a b ha hb
  have haebR (a b : A) (ha : aug a = 0) (hb : aug b = 0) :
      a * (e * b) = 0 := by simpa [mul_assoc] using haeb a b ha hb
  have habeR (a b : A) (ha : aug a = 0) (hb : aug b = 0) :
      a * (b * e) = 0 := by simpa [mul_assoc] using habe a b ha hb
  have htwo (a : A) : 2 • a = 0 := ZModModule.char_nsmul_eq_zero 2 a
  have htwoZ (a : A) : (2 : ℤ) • a = 0 := by
    simpa [two_zsmul] using htwo a
  have hthreeZ (a : A) : (3 : ℤ) • a = a := by
    rw [show (3 : ℤ) = 2 + 1 by omega, add_zsmul, htwoZ, one_zsmul, zero_add]
  simp (discharger := simp [has, hax, hae]) only [add_mul, mul_add, mul_assoc,
    pow_zero, pow_succ, one_mul, mul_one, zero_mul, mul_zero,
    hfourR, heabR, haebR, habeR, hee]
  abel_nf
  simp only [htwoZ, hthreeZ, zero_add]

/-- Regard one degree-two correction block as an augmentation-zero element of the unitized
operator algebra. -/
def sqCubicCorrectionOperatorElement (h : ℕ) (D : SqCubicDegreeTwoCorrection h)
    (i : Fin (sqRank h)) : SqCubicOperatorAlgebra h :=
  (⟨D.operator i, (D.raises_two i).strict (by omega)⟩ : sqCubicStrictEnd h)

@[simp] theorem sqCubicCorrectionOperatorElement_augmentation (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    sqCubicOperatorAugmentation h (sqCubicCorrectionOperatorElement h D i) = 0 := by
  simp [sqCubicCorrectionOperatorElement, sqCubicOperatorAugmentation]

theorem sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    sqCubicCorrectedOperatorLetter h D i =
      sqCubicHomogeneousOperatorLetter h i +
        sqCubicCorrectionOperatorElement h D i := by
  apply Unitization.ext
  · simp [sqCubicCorrectedOperatorLetter, sqCubicHomogeneousOperatorLetter,
      sqCubicCorrectionOperatorElement]
  · apply Subtype.ext
    rfl

theorem sqCubicCorrectionOperatorElement_mul_two_kernel_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h))
    (a b : SqCubicOperatorAlgebra h)
    (ha : sqCubicOperatorAugmentation h a = 0)
    (hb : sqCubicOperatorAugmentation h b = 0) :
    sqCubicCorrectionOperatorElement h D i * a * b = 0 := by
  have ea : a = (a.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using ha
    · simp
  have eb : b = (b.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using hb
    · simp
  rw [ea, eb]
  change ((⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
      sqCubicStrictEnd h) : SqCubicOperatorAlgebra h) *
        (a.snd : SqCubicOperatorAlgebra h) *
          (b.snd : SqCubicOperatorAlgebra h) = 0
  have hz : (⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
        sqCubicStrictEnd h) * a.snd * b.snd = 0 := by
    apply Subtype.ext
    exact (((D.raises_two i).mul a.snd.2).mul b.snd.2).eq_zero_of_four_le (by omega)
  simpa only [← Unitization.inr_mul, Unitization.inr_zero] using
    congrArg (fun z : sqCubicStrictEnd h => (z : SqCubicOperatorAlgebra h)) hz

theorem sqCubicKernel_mul_correction_mul_kernel_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h))
    (a b : SqCubicOperatorAlgebra h)
    (ha : sqCubicOperatorAugmentation h a = 0)
    (hb : sqCubicOperatorAugmentation h b = 0) :
    a * sqCubicCorrectionOperatorElement h D i * b = 0 := by
  have ea : a = (a.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using ha
    · simp
  have eb : b = (b.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using hb
    · simp
  rw [ea, eb]
  change (a.snd : SqCubicOperatorAlgebra h) *
      ((⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
        sqCubicStrictEnd h) : SqCubicOperatorAlgebra h) *
          (b.snd : SqCubicOperatorAlgebra h) = 0
  have hz : a.snd *
        (⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
          sqCubicStrictEnd h) * b.snd = 0 := by
    apply Subtype.ext
    exact ((SqCubicRaisesBy.mul a.snd.2 (D.raises_two i)).mul b.snd.2)
      |>.eq_zero_of_four_le (by omega)
  simpa only [← Unitization.inr_mul, Unitization.inr_zero] using
    congrArg (fun z : sqCubicStrictEnd h => (z : SqCubicOperatorAlgebra h)) hz

theorem sqCubicTwoKernel_mul_correction_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h))
    (a b : SqCubicOperatorAlgebra h)
    (ha : sqCubicOperatorAugmentation h a = 0)
    (hb : sqCubicOperatorAugmentation h b = 0) :
    a * b * sqCubicCorrectionOperatorElement h D i = 0 := by
  have ea : a = (a.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using ha
    · simp
  have eb : b = (b.snd : SqCubicOperatorAlgebra h) := by
    apply Unitization.ext
    · simpa [sqCubicOperatorAugmentation] using hb
    · simp
  rw [ea, eb]
  change (a.snd : SqCubicOperatorAlgebra h) *
      (b.snd : SqCubicOperatorAlgebra h) *
        ((⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
          sqCubicStrictEnd h) : SqCubicOperatorAlgebra h) = 0
  have hz : a.snd * b.snd *
        (⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
          sqCubicStrictEnd h) = 0 := by
    apply Subtype.ext
    exact ((SqCubicRaisesBy.mul a.snd.2 b.snd.2).mul (D.raises_two i))
      |>.eq_zero_of_four_le (by omega)
  simpa only [← Unitization.inr_mul, Unitization.inr_zero] using
    congrArg (fun z : sqCubicStrictEnd h => (z : SqCubicOperatorAlgebra h)) hz

theorem sqCubicCorrectionOperatorElement_sq_zero (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) (i : Fin (sqRank h)) :
    sqCubicCorrectionOperatorElement h D i *
        sqCubicCorrectionOperatorElement h D i = 0 := by
  change ((⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
      sqCubicStrictEnd h) : SqCubicOperatorAlgebra h) *
        ((⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
          sqCubicStrictEnd h) : SqCubicOperatorAlgebra h) = 0
  have hz : (⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
        sqCubicStrictEnd h) *
      (⟨D.operator i, (D.raises_two i).strict (by omega)⟩ :
        sqCubicStrictEnd h) = 0 := by
    apply Subtype.ext
    exact ((D.raises_two i).mul (D.raises_two i)).eq_zero_of_four_le (by omega)
  simpa only [← Unitization.inr_mul, Unitization.inr_zero] using
    congrArg (fun z : sqCubicStrictEnd h => (z : SqCubicOperatorAlgebra h)) hz

/-- The inverse polynomial after adding a degree-two correction. -/
theorem cubicInversePolynomial_add_degreeTwo
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (aug : A →ₐ[ZMod 2] ZMod 2)
    (x e : A) (hax : aug x = 0) (hae : aug e = 0)
    (heab : ∀ a b : A, aug a = 0 → aug b = 0 → e * a * b = 0)
    (haeb : ∀ a b : A, aug a = 0 → aug b = 0 → a * e * b = 0)
    (habe : ∀ a b : A, aug a = 0 → aug b = 0 → a * b * e = 0)
    (hee : e * e = 0) :
    1 + (x + e) + (x + e) ^ 2 + (x + e) ^ 3 =
      1 + x + x ^ 2 + x ^ 3 + e + x * e + e * x := by
  have heabR (a b : A) (ha : aug a = 0) (hb : aug b = 0) :
      e * (a * b) = 0 := by simpa [mul_assoc] using heab a b ha hb
  have haebR (a b : A) (ha : aug a = 0) (hb : aug b = 0) :
      a * (e * b) = 0 := by simpa [mul_assoc] using haeb a b ha hb
  have habeR (a b : A) (ha : aug a = 0) (hb : aug b = 0) :
      a * (b * e) = 0 := by simpa [mul_assoc] using habe a b ha hb
  simp (discharger := simp [hax, hae]) only [add_mul, mul_add, mul_assoc,
    pow_zero, pow_succ, one_mul, zero_mul, mul_zero,
    heabR, haebR, habeR, hee]
  abel

theorem oneAddUnitOfPowFourZero_pow_four {A : Type} [Ring A]
    [Algebra (ZMod 2) A] (x : A) (hx : x ^ 4 = 0) :
    oneAddUnitOfPowFourZero x hx ^ 4 = 1 := by
  apply Units.ext
  change (1 + x) ^ 4 = 1
  calc
    (1 + x) ^ 4 = ((1 + x) ^ 2) ^ 2 := by
      rw [show 4 = 2 * 2 by omega, pow_mul]
    _ = (1 + x ^ 2) ^ 2 := by rw [one_add_sq_charTwo]
    _ = 1 + (x ^ 2) ^ 2 := one_add_sq_charTwo (x ^ 2)
    _ = 1 + x ^ 4 := by rw [← pow_mul]
    _ = 1 := by rw [hx, add_zero]

@[simp] theorem oneAddUnitOfPowFourZero_inv_val {A : Type} [Ring A]
    [Algebra (ZMod 2) A] (x : A) (hx : x ^ 4 = 0) :
    ((oneAddUnitOfPowFourZero x hx)⁻¹ : Aˣ).val = 1 + x + x ^ 2 + x ^ 3 :=
  rfl

theorem inv_cube_eq_self_of_pow_four_eq_one {G : Type} [Group G]
    (u : G) (hu : u ^ 4 = 1) : (u ^ 3)⁻¹ = u := by
  calc
    (u ^ 3)⁻¹ = u * (u ^ 4)⁻¹ := by group
    _ = u := by rw [hu, inv_one, mul_one]

/-- The two-factor prefix `(x^s)^{-1} x^{-3}` of the improved square core. -/
def sqCubicCorrectedCorePrefix (h : ℕ) (D : SqCubicDegreeTwoCorrection h) :
    (SqCubicOperatorAlgebra h)ˣ :=
  (conjP (sqCubicCorrectedMarkedUnit h D 1)
      (sqCubicCorrectedMarkedUnit h D 0))⁻¹ *
    ((sqCubicCorrectedMarkedUnit h D 1) ^ 3)⁻¹

set_option maxHeartbeats 4000000 in
theorem sqCubicCorrectedCorePrefix_val (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    (sqCubicCorrectedCorePrefix h D).val =
      (1 + sqCubicCorrectedOperatorLetter h D 0 +
          (sqCubicCorrectedOperatorLetter h D 0) ^ 2 +
          (sqCubicCorrectedOperatorLetter h D 0) ^ 3) *
        (1 + sqCubicCorrectedOperatorLetter h D 1 +
          (sqCubicCorrectedOperatorLetter h D 1) ^ 2 +
          (sqCubicCorrectedOperatorLetter h D 1) ^ 3) *
        (1 + sqCubicCorrectedOperatorLetter h D 0) *
        (1 + sqCubicCorrectedOperatorLetter h D 1) := by
  have hx4 := oneAddUnitOfPowFourZero_pow_four
    (sqCubicCorrectedOperatorLetter h D 1)
    (sqCubicCorrectedOperatorLetter_pow_four_zero h D 1)
  have hx4' : (sqCubicCorrectedMarkedUnit h D 1) ^ 4 = 1 := hx4
  rw [sqCubicCorrectedCorePrefix, conjP]
  simp only [mul_inv_rev, inv_inv]
  rw [inv_cube_eq_self_of_pow_four_eq_one _ hx4']
  simp only [Units.val_mul, sqCubicCorrectedMarkedUnit,
    oneAddUnitOfPowFourZero_val, oneAddUnitOfPowFourZero_inv_val]
  simp only [mul_assoc]

set_option maxHeartbeats 1000000 in
theorem sqCubicCorrectedCorePrefix_perturbation_of_letters (h : ℕ)
    (D D0 : SqCubicDegreeTwoCorrection h) (s x e : SqCubicOperatorAlgebra h)
    (hs : sqCubicCorrectedOperatorLetter h D 0 = s)
    (hx : sqCubicCorrectedOperatorLetter h D 1 = x + e)
    (hs0 : sqCubicCorrectedOperatorLetter h D0 0 = s)
    (hx0 : sqCubicCorrectedOperatorLetter h D0 1 = x)
    (has : sqCubicOperatorAugmentation h s = 0)
    (hax : sqCubicOperatorAugmentation h x = 0)
    (hae : sqCubicOperatorAugmentation h e = 0)
    (heab : ∀ a b : SqCubicOperatorAlgebra h,
      sqCubicOperatorAugmentation h a = 0 →
      sqCubicOperatorAugmentation h b = 0 → e * a * b = 0)
    (haeb : ∀ a b : SqCubicOperatorAlgebra h,
      sqCubicOperatorAugmentation h a = 0 →
      sqCubicOperatorAugmentation h b = 0 → a * e * b = 0)
    (habe : ∀ a b : SqCubicOperatorAlgebra h,
      sqCubicOperatorAugmentation h a = 0 →
      sqCubicOperatorAugmentation h b = 0 → a * b * e = 0)
    (hee : e * e = 0) :
    (sqCubicCorrectedCorePrefix h D).val =
      (sqCubicCorrectedCorePrefix h D0).val + e * s + s * e := by
  rw [sqCubicCorrectedCorePrefix_val, sqCubicCorrectedCorePrefix_val,
    hs, hx, hs0, hx0]
  rw [cubicInversePolynomial_add_degreeTwo
    (sqCubicOperatorAugmentation h) x e hax hae heab haeb habe hee]
  simpa only [add_assoc] using cubicConjugateCubePrefix_perturbation
    (sqCubicOperatorAugmentation h)
    (sqCubicOperatorAugmentation_product_four_zero h)
    s x e has hax hae heab haeb habe hee

theorem sqCubicXFromSCorePrefix_perturbation (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    (sqCubicCorrectedCorePrefix h
      (sqCubicXFromSColumnCorrection h v hv)).val =
      (sqCubicCorrectedCorePrefix h (sqCubicZeroDegreeTwoCorrection h)).val +
        sqCubicCorrectionOperatorElement h
            (sqCubicXFromSColumnCorrection h v hv) 1 *
          sqCubicHomogeneousOperatorLetter h 0 +
        sqCubicHomogeneousOperatorLetter h 0 *
          sqCubicCorrectionOperatorElement h
            (sqCubicXFromSColumnCorrection h v hv) 1 := by
  apply sqCubicCorrectedCorePrefix_perturbation_of_letters h
    (sqCubicXFromSColumnCorrection h v hv)
    (sqCubicZeroDegreeTwoCorrection h)
    (sqCubicHomogeneousOperatorLetter h 0)
    (sqCubicHomogeneousOperatorLetter h 1)
    (sqCubicCorrectionOperatorElement h
      (sqCubicXFromSColumnCorrection h v hv) 1)
  · have he0 : sqCubicCorrectionOperatorElement h
        (sqCubicXFromSColumnCorrection h v hv) 0 = 0 := by
      apply Unitization.ext
      · simp [sqCubicCorrectionOperatorElement]
      · apply Subtype.ext
        apply sqCubicXFromSColumnCorrection_ne_X h v hv 0
        intro e01
        have hv1 : ((1 : Fin (sqRank h)) : Nat) = 1 := by
          change 1 % sqRank h = 1
          apply Nat.mod_eq_of_lt
          rw [sqRank]
          omega
        have he := congrArg Fin.val e01
        rw [hv1] at he
        simp at he
    rw [sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction, he0,
      add_zero]
  · exact sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction h
      (sqCubicXFromSColumnCorrection h v hv) 1
  · have hD0 : sqCubicCorrectionOperatorElement h
        (sqCubicZeroDegreeTwoCorrection h) 0 = 0 := by
      apply Unitization.ext
      · simp [sqCubicCorrectionOperatorElement]
      · apply Subtype.ext
        rfl
    rw [sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction, hD0,
      add_zero]
  · have hD0 : sqCubicCorrectionOperatorElement h
        (sqCubicZeroDegreeTwoCorrection h) 1 = 0 := by
      apply Unitization.ext
      · simp [sqCubicCorrectionOperatorElement]
      · apply Subtype.ext
        rfl
    rw [sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction, hD0,
      add_zero]
  · exact sqCubicHomogeneousOperatorLetter_augmentation h 0
  · exact sqCubicHomogeneousOperatorLetter_augmentation h 1
  · exact sqCubicCorrectionOperatorElement_augmentation h
      (sqCubicXFromSColumnCorrection h v hv) 1
  · intro a b ha hb
    exact sqCubicCorrectionOperatorElement_mul_two_kernel_zero h
      (sqCubicXFromSColumnCorrection h v hv) 1 a b ha hb
  · intro a b ha hb
    exact sqCubicKernel_mul_correction_mul_kernel_zero h
      (sqCubicXFromSColumnCorrection h v hv) 1 a b ha hb
  · intro a b ha hb
    exact sqCubicTwoKernel_mul_correction_zero h
      (sqCubicXFromSColumnCorrection h v hv) 1 a b ha hb
  · exact sqCubicCorrectionOperatorElement_sq_zero h
      (sqCubicXFromSColumnCorrection h v hv) 1

/-! ## Propagation through the unchanged suffix -/

/-- The factors of the literal relator following the conjugate/cube prefix. -/
def sqCubicCorrectedRelatorSuffix (h : ℕ) (D : SqCubicDegreeTwoCorrection h) :
    (SqCubicOperatorAlgebra h)ˣ :=
  (sqCubicCorrectedMarkedUnit h D 2) ^ 2 *
    commP (sqCubicCorrectedMarkedUnit h D 2)
      (conjP (sqCubicCorrectedMarkedUnit h D 2)
        (sqCubicCorrectedMarkedUnit h D 0)) *
    MarkedCore.handleWord
      (fun j => sqCubicCorrectedMarkedUnit h D (sqHandleIdxU j))
      (fun j => sqCubicCorrectedMarkedUnit h D (sqHandleIdxV j))

/-- The literal improved relator factors into the perturbed prefix and a common suffix. -/
theorem sqCubicCorrectedRelatorUnit_eq_prefix_mul_suffix (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    sqCubicCorrectedRelatorUnit h D =
      sqCubicCorrectedCorePrefix h D * sqCubicCorrectedRelatorSuffix h D := by
  simp only [sqCubicCorrectedRelatorUnit, sqRelWord, sqWord,
    sqCubicCorrectedCorePrefix, sqCubicCorrectedRelatorSuffix, mul_assoc]

@[simp] theorem sqCubicZeroCorrectionOperatorElement (h : ℕ)
    (i : Fin (sqRank h)) :
    sqCubicCorrectionOperatorElement h (sqCubicZeroDegreeTwoCorrection h) i = 0 := by
  apply Unitization.ext
  · simp [sqCubicCorrectionOperatorElement]
  · apply Subtype.ext
    rfl

theorem sqCubicXFromSCorrectionOperatorElement_ne_X (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3)
    (i : Fin (sqRank h)) (hi : i ≠ 1) :
    sqCubicCorrectionOperatorElement h
      (sqCubicXFromSColumnCorrection h v hv) i = 0 := by
  apply Unitization.ext
  · simp [sqCubicCorrectionOperatorElement]
  · apply Subtype.ext
    exact sqCubicXFromSColumnCorrection_ne_X h v hv i hi

theorem sqCubicXFromSCorrectedMarkedUnit_ne_X (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3)
    (i : Fin (sqRank h)) (hi : i ≠ 1) :
    sqCubicCorrectedMarkedUnit h (sqCubicXFromSColumnCorrection h v hv) i =
      sqCubicCorrectedMarkedUnit h (sqCubicZeroDegreeTwoCorrection h) i := by
  apply Units.ext
  simp only [sqCubicCorrectedMarkedUnit, oneAddUnitOfPowFourZero_val]
  rw [sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction,
    sqCubicXFromSCorrectionOperatorElement_ne_X h v hv i hi, add_zero,
    sqCubicCorrectedOperatorLetter_eq_homogeneous_add_correction,
    sqCubicZeroCorrectionOperatorElement, add_zero]

private theorem sqCubicFin_two_ne_one (h : ℕ) :
    (2 : Fin (sqRank h)) ≠ 1 := by
  intro e
  have he := congrArg Fin.val e
  have h2 : ((2 : Fin (sqRank h)) : Nat) = 2 := by
    change 2 % sqRank h = 2
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  have h1 : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  rw [h2, h1] at he
  omega

private theorem sqCubicFin_zero_ne_one (h : ℕ) :
    (0 : Fin (sqRank h)) ≠ 1 := by
  intro e
  have he := congrArg Fin.val e
  have h1 : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  rw [h1] at he
  simp at he

private theorem sqCubicHandleU_ne_one {h : ℕ} (j : Fin h) :
    sqHandleIdxU j ≠ (1 : Fin (sqRank h)) := by
  intro e
  have he := congrArg Fin.val e
  have h1 : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  rw [h1] at he
  change 3 + 2 * (j : Nat) = 1 at he
  omega

private theorem sqCubicHandleV_ne_one {h : ℕ} (j : Fin h) :
    sqHandleIdxV j ≠ (1 : Fin (sqRank h)) := by
  intro e
  have he := congrArg Fin.val e
  have h1 : ((1 : Fin (sqRank h)) : Nat) = 1 := by
    change 1 % sqRank h = 1
    apply Nat.mod_eq_of_lt
    rw [sqRank]
    omega
  rw [h1] at he
  change 4 + 2 * (j : Nat) = 1 at he
  omega

/-- The rank-one correction changes only `X`, hence leaves the entire relator suffix fixed. -/
theorem sqCubicXFromSRelatorSuffix_eq_zero (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    sqCubicCorrectedRelatorSuffix h (sqCubicXFromSColumnCorrection h v hv) =
      sqCubicCorrectedRelatorSuffix h (sqCubicZeroDegreeTwoCorrection h) := by
  have hy := sqCubicXFromSCorrectedMarkedUnit_ne_X h v hv 2
    (sqCubicFin_two_ne_one h)
  have hs := sqCubicXFromSCorrectedMarkedUnit_ne_X h v hv 0
    (sqCubicFin_zero_ne_one h)
  have hu : (fun j : Fin h => sqCubicCorrectedMarkedUnit h
        (sqCubicXFromSColumnCorrection h v hv) (sqHandleIdxU j)) =
      (fun j : Fin h => sqCubicCorrectedMarkedUnit h
        (sqCubicZeroDegreeTwoCorrection h) (sqHandleIdxU j)) := by
    funext j
    exact sqCubicXFromSCorrectedMarkedUnit_ne_X h v hv _
      (sqCubicHandleU_ne_one j)
  have hv' : (fun j : Fin h => sqCubicCorrectedMarkedUnit h
        (sqCubicXFromSColumnCorrection h v hv) (sqHandleIdxV j)) =
      (fun j : Fin h => sqCubicCorrectedMarkedUnit h
        (sqCubicZeroDegreeTwoCorrection h) (sqHandleIdxV j)) := by
    funext j
    exact sqCubicXFromSCorrectedMarkedUnit_ne_X h v hv _
      (sqCubicHandleV_ne_one j)
  simp only [sqCubicCorrectedRelatorSuffix]
  rw [hy, hs, hu, hv']

theorem right_mul_eq_self_of_augmentation_one
    {A : Type} [Ring A] [Algebra (ZMod 2) A]
    (aug : A →ₐ[ZMod 2] ZMod 2) (d z : A)
    (hz : aug z = 1)
    (hd : ∀ a : A, aug a = 0 → d * a = 0) :
    d * z = d := by
  have hz0 : aug (z - 1) = 0 := by simp [hz]
  calc
    d * z = d * (1 + (z - 1)) := by
      congr 1
      abel
    _ = d * 1 + d * (z - 1) := by rw [mul_add]
    _ = d := by rw [hd _ hz0, mul_one, add_zero]

@[simp] theorem sqCubicCorrectedRelatorSuffix_augmentation (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) :
    sqCubicOperatorAugmentation h (sqCubicCorrectedRelatorSuffix h D).val = 1 := by
  have hunit : Units.map (sqCubicOperatorAugmentation h).toMonoidHom
      (sqCubicCorrectedRelatorSuffix h D) = 1 := Subsingleton.elim _ _
  exact congrArg Units.val hunit

/-- A degree-three prefix perturbation is unchanged by multiplication by the common
augmentation-one suffix. -/
theorem sqCubicPrefixDelta_mul_suffix (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h)
    (s : SqCubicOperatorAlgebra h)
    (hs : sqCubicOperatorAugmentation h s = 0) :
    let e := sqCubicCorrectionOperatorElement h D 1
    let z := (sqCubicCorrectedRelatorSuffix h D).val
    (e * s + s * e) * z = e * s + s * e := by
  dsimp only
  apply right_mul_eq_self_of_augmentation_one
    (sqCubicOperatorAugmentation h)
  · exact sqCubicCorrectedRelatorSuffix_augmentation h D
  · intro a ha
    rw [add_mul,
      sqCubicCorrectionOperatorElement_mul_two_kernel_zero h D 1 s a hs ha,
      sqCubicKernel_mul_correction_mul_kernel_zero h D 1 s a hs ha,
      add_zero]

/-- The named degree-three change produced by the rank-one `X`-from-`S` correction. -/
def sqCubicXFromSPrefixDelta (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    SqCubicOperatorAlgebra h :=
  sqCubicCorrectionOperatorElement h
      (sqCubicXFromSColumnCorrection h v hv) 1 *
    sqCubicHomogeneousOperatorLetter h 0 +
  sqCubicHomogeneousOperatorLetter h 0 *
    sqCubicCorrectionOperatorElement h
      (sqCubicXFromSColumnCorrection h v hv) 1

theorem sqCubicXFromSCorePrefix_perturbation_delta (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    (sqCubicCorrectedCorePrefix h
      (sqCubicXFromSColumnCorrection h v hv)).val =
      (sqCubicCorrectedCorePrefix h
        (sqCubicZeroDegreeTwoCorrection h)).val +
      sqCubicXFromSPrefixDelta h v hv := by
  calc
    (sqCubicCorrectedCorePrefix h
        (sqCubicXFromSColumnCorrection h v hv)).val =
      (sqCubicCorrectedCorePrefix h
          (sqCubicZeroDegreeTwoCorrection h)).val +
        sqCubicCorrectionOperatorElement h
            (sqCubicXFromSColumnCorrection h v hv) 1 *
          sqCubicHomogeneousOperatorLetter h 0 +
        sqCubicHomogeneousOperatorLetter h 0 *
          sqCubicCorrectionOperatorElement h
            (sqCubicXFromSColumnCorrection h v hv) 1 :=
      sqCubicXFromSCorePrefix_perturbation h v hv
    _ = (sqCubicCorrectedCorePrefix h
          (sqCubicZeroDegreeTwoCorrection h)).val +
        sqCubicXFromSPrefixDelta h v hv := by
      rw [sqCubicXFromSPrefixDelta, add_assoc]

theorem sqCubicCorrectedRelatorUnit_val_perturbation_of
    (h : ℕ) (D D0 : SqCubicDegreeTwoCorrection h)
    (delta : SqCubicOperatorAlgebra h)
    (hprefix : (sqCubicCorrectedCorePrefix h D).val =
      (sqCubicCorrectedCorePrefix h D0).val + delta)
    (hsuffix : sqCubicCorrectedRelatorSuffix h D =
      sqCubicCorrectedRelatorSuffix h D0)
    (hdelta : delta * (sqCubicCorrectedRelatorSuffix h D).val = delta) :
    (sqCubicCorrectedRelatorUnit h D).val =
      (sqCubicCorrectedRelatorUnit h D0).val + delta := by
  rw [sqCubicCorrectedRelatorUnit_eq_prefix_mul_suffix,
    sqCubicCorrectedRelatorUnit_eq_prefix_mul_suffix,
    Units.val_mul, Units.val_mul,
    ← hsuffix, hprefix, add_mul, hdelta]

/-- The full literal relator changes by the same named degree-three term as its prefix. -/
theorem sqCubicXFromSRelatorUnit_val_perturbation (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    (sqCubicCorrectedRelatorUnit h
      (sqCubicXFromSColumnCorrection h v hv)).val =
      (sqCubicCorrectedRelatorUnit h
        (sqCubicZeroDegreeTwoCorrection h)).val +
      sqCubicXFromSPrefixDelta h v hv := by
  apply sqCubicCorrectedRelatorUnit_val_perturbation_of h
  · exact sqCubicXFromSCorePrefix_perturbation_delta h v hv
  · exact sqCubicXFromSRelatorSuffix_eq_zero h v hv
  · exact sqCubicPrefixDelta_mul_suffix h
      (sqCubicXFromSColumnCorrection h v hv)
      (sqCubicHomogeneousOperatorLetter h 0)
      (sqCubicHomogeneousOperatorLetter_augmentation h 0)

/-- On the empty PBW column, the named perturbation has the prescribed value `v`. -/
theorem sqCubicXFromSPrefixDelta_snd_apply_empty (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    ((sqCubicXFromSPrefixDelta h v hv).snd.1 :
      Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicEmptyVector h) = v := by
  rw [sqCubicXFromSPrefixDelta, Unitization.snd_add]
  simp only [sqCubicCorrectionOperatorElement,
    sqCubicHomogeneousOperatorLetter, Unitization.snd_mul,
    Unitization.fst_inr, Unitization.snd_inr, zero_smul, zero_add]
  change
    ((sqCubicXFromSColumnCorrection h v hv).operator 1 *
        sqCubicTruncatedLeftLetter h 0 +
      sqCubicTruncatedLeftLetter h 0 *
        (sqCubicXFromSColumnCorrection h v hv).operator 1)
      (sqCubicEmptyVector h) = v
  rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply,
    sqCubicTruncatedLeftLetter_apply_empty,
    sqCubicXFromSColumnCorrection_X_on_S,
    sqCubicXFromSColumnCorrection_X,
    sqCubicRankOneLetterColumn_empty, map_zero, add_zero]

theorem sqCubicXFromSPrefixDelta_snd_raises_three (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    SqCubicRaisesBy
      ((sqCubicXFromSPrefixDelta h v hv).snd.1 :
        Module.End (ZMod 2) (SqCubicNormalSpace h)) 3 := by
  rw [sqCubicXFromSPrefixDelta, Unitization.snd_add]
  simp only [sqCubicCorrectionOperatorElement,
    sqCubicHomogeneousOperatorLetter, Unitization.snd_mul,
    Unitization.fst_inr, Unitization.snd_inr, zero_smul, zero_add]
  apply SqCubicRaisesBy.add
  · change SqCubicRaisesBy
      ((sqCubicXFromSColumnCorrection h v hv).operator 1 *
        sqCubicTruncatedLeftLetter h 0) 3
    simpa using (sqCubicXFromSColumnCorrection h v hv).raises_two 1 |>.mul
      (sqCubicTruncatedLeftLetter_raises_one h 0)
  · change SqCubicRaisesBy
      (sqCubicTruncatedLeftLetter h 0 *
        (sqCubicXFromSColumnCorrection h v hv).operator 1) 3
    simpa [add_comm] using (sqCubicTruncatedLeftLetter_raises_one h 0).mul
      ((sqCubicXFromSColumnCorrection h v hv).raises_two 1)

theorem sqCubicXFromSRelatorEnd_eq_add_delta (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    sqCubicCorrectedRelatorEnd h (sqCubicXFromSColumnCorrection h v hv) =
      sqCubicCorrectedRelatorEnd h (sqCubicZeroDegreeTwoCorrection h) +
        ((sqCubicXFromSPrefixDelta h v hv).snd.1 :
          Module.End (ZMod 2) (SqCubicNormalSpace h)) := by
  apply LinearMap.ext
  intro x
  have H := congrArg
    (fun a : SqCubicOperatorAlgebra h =>
      (a.snd.1 : Module.End (ZMod 2) (SqCubicNormalSpace h)) x)
    (sqCubicXFromSRelatorUnit_val_perturbation h v hv)
  exact H.trans (by rfl)

/-- The corrected literal relator's empty column is the old residual plus the prescribed
rank-one target. -/
theorem sqCubicXFromSRelatorEnd_apply_empty (h : ℕ)
    (v : SqCubicNormalSpace h) (hv : v ∈ sqCubicNormalFiltration h 3) :
    sqCubicCorrectedRelatorEnd h (sqCubicXFromSColumnCorrection h v hv)
        (sqCubicEmptyVector h) =
      sqCubicHomogeneousRelatorResidual h + v := by
  rw [sqCubicXFromSRelatorEnd_eq_add_delta h v hv, LinearMap.add_apply,
    sqCubicXFromSPrefixDelta_snd_apply_empty]
  rfl

/-- At the homogeneous residual itself, the concrete perturbation contributes exactly that
residual on the empty column. -/
theorem sqCubicResidualPrefixDelta_snd_apply_empty (h : ℕ)
    (hres : sqCubicHomogeneousRelatorResidual h ∈
      sqCubicNormalFiltration h 3) :
    ((sqCubicXFromSPrefixDelta h (sqCubicHomogeneousRelatorResidual h) hres).snd.1 :
      Module.End (ZMod 2) (SqCubicNormalSpace h))
        (sqCubicEmptyVector h) = sqCubicHomogeneousRelatorResidual h :=
  sqCubicXFromSPrefixDelta_snd_apply_empty h _ hres

theorem sqCubicResidualCorrection_relatorEnd_apply_empty (h : ℕ)
    (hres : sqCubicHomogeneousRelatorResidual h ∈
      sqCubicNormalFiltration h 3) :
    sqCubicCorrectedRelatorEnd h
        (sqCubicXFromSColumnCorrection h
          (sqCubicHomogeneousRelatorResidual h) hres)
      (sqCubicEmptyVector h) = 0 := by
  rw [sqCubicXFromSRelatorEnd_apply_empty]
  have htwo : 2 • sqCubicHomogeneousRelatorResidual h = 0 :=
    ZModModule.char_nsmul_eq_zero 2 _
  simpa [two_smul] using htwo

theorem sqCubicHomogeneousRelatorResidual_mem_three_of_raises_three (h : ℕ)
    (hhom : SqCubicRaisesBy
      (sqCubicCorrectedRelatorEnd h (sqCubicZeroDegreeTwoCorrection h)) 3) :
    sqCubicHomogeneousRelatorResidual h ∈ sqCubicNormalFiltration h 3 := by
  exact hhom 0 (sqCubicEmptyVector h) (by simp)

/-- Once the homogeneous literal relator is known to start in degree three, the rank-one
residual correction makes the entire relator endomorphism vanish. -/
theorem sqCubicResidualCorrection_relatorEnd_zero_of_homogeneous_raises_three
    (h : ℕ)
    (hres : sqCubicHomogeneousRelatorResidual h ∈
      sqCubicNormalFiltration h 3)
    (hhom : SqCubicRaisesBy
      (sqCubicCorrectedRelatorEnd h (sqCubicZeroDegreeTwoCorrection h)) 3) :
    sqCubicCorrectedRelatorEnd h
      (sqCubicXFromSColumnCorrection h
        (sqCubicHomogeneousRelatorResidual h) hres) = 0 := by
  apply sqCubicEnd_eq_of_raises_three
  · rw [sqCubicXFromSRelatorEnd_eq_add_delta h
      (sqCubicHomogeneousRelatorResidual h) hres]
    exact hhom.add
      (sqCubicXFromSPrefixDelta_snd_raises_three h
        (sqCubicHomogeneousRelatorResidual h) hres)
  · exact fun _ _ _ => Submodule.zero_mem _
  · exact sqCubicResidualCorrection_relatorEnd_apply_empty h hres

theorem sqCubicResidualCorrection_relatorEquation_of_homogeneous_raises_three
    (h : ℕ)
    (hres : sqCubicHomogeneousRelatorResidual h ∈
      sqCubicNormalFiltration h 3)
    (hhom : SqCubicRaisesBy
      (sqCubicCorrectedRelatorEnd h (sqCubicZeroDegreeTwoCorrection h)) 3) :
    SqCubicInhomogeneousRelatorEquation h
      (sqCubicXFromSColumnCorrection h
        (sqCubicHomogeneousRelatorResidual h) hres) := by
  rw [sqCubicInhomogeneousRelatorEquation_iff_end_zero]
  exact sqCubicResidualCorrection_relatorEnd_zero_of_homogeneous_raises_three
    h hres hhom

/-- An explicit finite inhomogeneous correction consists only of filtration-degree-two
operator blocks together with the single literal relator equation.  Cubic confluence,
nilpotence, and PBW independence are consequences, not fields of this structure. -/
structure SqCubicInhomogeneousCorrection (h : ℕ) where
  correction : SqCubicDegreeTwoCorrection h
  relatorEquation : SqCubicInhomogeneousRelatorEquation h correction

/-- The homogeneous degree-three start supplies the explicit residual correction package. -/
def sqCubicResidualInhomogeneousCorrectionOfRaisesThree (h : ℕ)
    (hhom : SqCubicRaisesBy
      (sqCubicCorrectedRelatorEnd h (sqCubicZeroDegreeTwoCorrection h)) 3) :
    SqCubicInhomogeneousCorrection h :=
  let hres := sqCubicHomogeneousRelatorResidual_mem_three_of_raises_three h hhom
  ⟨sqCubicXFromSColumnCorrection h (sqCubicHomogeneousRelatorResidual h) hres,
    sqCubicResidualCorrection_relatorEquation_of_homogeneous_raises_three
      h hres hhom⟩

theorem nonempty_sqCubicInhomogeneousCorrection_iff (h : ℕ) :
    Nonempty (SqCubicInhomogeneousCorrection h) ↔
      ∃ D : SqCubicDegreeTwoCorrection h,
        SqCubicInhomogeneousRelatorEquation h D := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.correction, C.relatorEquation⟩
  · rintro ⟨D, hD⟩
    exact ⟨⟨D, hD⟩⟩

/-- The finite correction equation constructs the full algebra detector certificate. -/
def SqCubicInhomogeneousCorrection.toMagnusAlgebraCertificate
    {h : ℕ} (C : SqCubicInhomogeneousCorrection h) :
    SqCubicMagnusAlgebraCertificate h (SqCubicOperatorAlgebra h) where
  augmentation := sqCubicOperatorAugmentation h
  letter := sqCubicCorrectedOperatorLetter h C.correction
  letter_augmentation := sqCubicCorrectedOperatorLetter_augmentation h C.correction
  augmentation_product_four_zero :=
    sqCubicOperatorAugmentation_product_four_zero h
  relator := C.relatorEquation
  cubic_normalization :=
    sqCubicCorrectedOperator_cubic_normalization h C.correction
  normal_independent :=
    sqCubicCorrectedOperator_normal_independent h C.correction

/-- The exact finite correction equation gives an explicit nonempty cubic Magnus detector. -/
theorem nonempty_sqCubicMagnusAlgebraCertificate_of_inhomogeneousCorrection
    {h : ℕ} (C : SqCubicInhomogeneousCorrection h) :
    Nonempty (SqCubicMagnusAlgebraCertificate h (SqCubicOperatorAlgebra h)) :=
  ⟨C.toMagnusAlgebraCertificate⟩

/-- Consequently the finite correction equation proves the unconditional completed cubic
Magnus--Labute kernel identity. -/
theorem sqCompletedMonomialPBWKernelIdentity_three_of_inhomogeneousCorrection
    {h : ℕ} (C : SqCubicInhomogeneousCorrection h) :
    SqCompletedMonomialPBWKernelIdentity h 3 :=
  C.toMagnusAlgebraCertificate.completedCubicKernelIdentity_of_columnSound
    (sqCompletedCubicPBWColumnSound h)

end

end GQ2.ContCoh
