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

end

end GQ2.ContCoh
