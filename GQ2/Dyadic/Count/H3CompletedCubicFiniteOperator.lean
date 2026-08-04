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

/-- The one remaining finite equation for a degree-two correction: the full literal improved
relator must die on the corrected unipotent marked letters. -/
def SqCubicInhomogeneousRelatorEquation (h : ℕ)
    (D : SqCubicDegreeTwoCorrection h) : Prop :=
  sqRelWord (fun i => oneAddUnitOfPowFourZero
    (sqCubicCorrectedOperatorLetter h D i)
    (sqCubicCorrectedOperatorLetter_pow_four_zero h D i)) = 1

/-- An explicit finite inhomogeneous correction consists only of filtration-degree-two
operator blocks together with the single literal relator equation.  Cubic confluence,
nilpotence, and PBW independence are consequences, not fields of this structure. -/
structure SqCubicInhomogeneousCorrection (h : ℕ) where
  correction : SqCubicDegreeTwoCorrection h
  relatorEquation : SqCubicInhomogeneousRelatorEquation h correction

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
