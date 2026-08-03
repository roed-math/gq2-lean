/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
module

public import GQ2.Cohomology
public import GQ2.DevissageInduction

@[expose] public section

/-!
# Coefficient dévissage for continuous degree-two comparison

`ContCoh` currently defines continuous cohomology only in degrees `0`, `1`, and `2`.  It has
coefficient maps `mapCoeff0`, `mapCoeff1`, and `mapCoeff2`, but it has no coefficient-SES
object, connecting morphisms, or long exact sequence.  This file isolates the smallest algebraic
theorem needed to pass a degree-two comparison from the ends of a coefficient short exact
sequence to its middle.

The relevant four-term window is

`H¹(A'') → H²(A') → H²(A) → H²(A'')`.

For continuous cohomology the last arrow is surjective precisely when the subsequent connecting
map to `H³(A')` vanishes.  Since `H³` is not defined in the current API, the sharp CD-2 input is
recorded directly as surjectivity of that `H²` coefficient map.  The theorem
`fourTermComparison_bijective` is a diagram chase: exactness of the two rows, commutativity,
bijectivity at the other three vertical maps, and this one right-surjectivity hypothesis imply
bijectivity of the middle `H²` comparison.

The second result, `finiteTwoModuleProperty_of_simple`, is the coefficient composition-series
induction independently of any cohomology theory.  Together the two results reduce a
simple-coefficient `H²` comparison campaign to three concrete missing constructions:

* the continuous coefficient connecting map `H¹(A'') → H²(A')` and exactness at the next two
  terms;
* compatibility of that connecting map with the comparison map;
* right-surjectivity of `H²(A) → H²(A'')` (for example from `cd₂`, equivalently vanishing of the
  relevant `H³(A')` obstruction).

No Tate-duality bundle or field-theoretic equivalence is used here.
-/

namespace GQ2

namespace ContCoh

/-! ## Representative formula for the degree-two coefficient map -/

section CoefficientRepresentative

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]

omit [IsTopologicalGroup G] [ContinuousSMul G M] [ContinuousSMul G N] in
/-- `mapCoeff2` computes on classes: the image of `H2mk z` is `H2mk` of the
pushed-forward cocycle (definitional). -/
theorem mapCoeff2_H2mk_coeff (f : N →+ M) (hf : Continuous f)
    (hcompat : ∀ (g : G) (n : N), f (g • n) = g • f n) (z : Z2 G N) :
    mapCoeff2 f hf hcompat (H2mk G N z)
      = H2mk G M (Z2comap (ContinuousMonoidHom.id G) f hf
          (fun g n ↦ hcompat g n) z) :=
  rfl

end CoefficientRepresentative

/-! ## Finite discrete coefficient short exact sequences -/

section CoefficientSES

variable {G A' A A'' : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DiscreteTopology A'] [Finite A'] [DistribMulAction G A'] [ContinuousSMul G A']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup A''] [TopologicalSpace A''] [IsTopologicalAddGroup A'']
  [DiscreteTopology A''] [Finite A''] [DistribMulAction G A''] [ContinuousSMul G A'']

/-- A short exact sequence of finite discrete `G`-modules, bundling exactly the data needed
by both the continuous and word coefficient long exact sequences. -/
structure FiniteDiscreteCoeffSES where
  f : A' →+ A
  g : A →+ A''
  f_equivariant : ∀ (c : G) (a : A'), f (c • a) = c • f a
  g_equivariant : ∀ (c : G) (a : A), g (c • a) = c • g a
  f_injective : Function.Injective f
  g_surjective : Function.Surjective g
  range_eq_ker : f.range = g.ker

namespace FiniteDiscreteCoeffSES

variable (S : FiniteDiscreteCoeffSES (G := G) (A' := A') (A := A) (A'' := A''))

/-- Coefficient maps in a finite discrete sequence are automatically continuous. -/
theorem continuous_f : Continuous S.f := continuous_of_discreteTopology

/-- Coefficient maps in a finite discrete sequence are automatically continuous. -/
theorem continuous_g : Continuous S.g := continuous_of_discreteTopology

/-- Consecutive coefficient maps in the sequence compose to zero. -/
theorem comp_zero (a : A') : S.g (S.f a) = 0 :=
  AddMonoidHom.mem_ker.mp (S.range_eq_ker ▸ AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)

/-- The induced consecutive continuous `H²` coefficient maps compose to zero. -/
theorem mapCoeff2_comp_apply (x : H2 G A') :
    mapCoeff2 S.g S.continuous_g S.g_equivariant
        (mapCoeff2 S.f S.continuous_f S.f_equivariant x) = 0 := by
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := A') x
  rw [mapCoeff2_H2mk_coeff, mapCoeff2_H2mk_coeff]
  have hz : Z2comap (ContinuousMonoidHom.id G) S.g S.continuous_g
      (fun c a ↦ S.g_equivariant c a)
      (Z2comap (ContinuousMonoidHom.id G) S.f S.continuous_f
        (fun c a ↦ S.f_equivariant c a) z) = 0 := by
    apply Subtype.ext
    funext p
    exact S.comp_zero (z.1 p)
  rw [hz, map_zero]

/-! ### The continuous cochain snake -/

/-- A chosen set-theoretic lift along the surjective coefficient map. -/
noncomputable def liftCoeff (a'' : A'') : A := (S.g_surjective a'').choose

@[simp] theorem g_liftCoeff (a'' : A'') : S.g (S.liftCoeff a'') = a'' :=
  (S.g_surjective a'').choose_spec

/-- A total set-theoretic inverse to `f` on `ker g`, extended by zero off the kernel. -/
noncomputable def kernelLift (a : A) : A' :=
  by
    classical
    exact if ha : S.g a = 0 then
      (AddMonoidHom.mem_range.mp
        (S.range_eq_ker ▸ AddMonoidHom.mem_ker.mpr ha)).choose
    else 0

theorem f_kernelLift_of_mem_ker {a : A} (ha : S.g a = 0) :
    S.f (S.kernelLift a) = a := by
  classical
  rw [kernelLift, dif_pos ha]
  exact (AddMonoidHom.mem_range.mp
    (S.range_eq_ker ▸ AddMonoidHom.mem_ker.mpr ha)).choose_spec

/-- The chosen continuous lift of a continuous one-cocycle.  It is not generally additive. -/
noncomputable def snakeLift1 (z : Z1 G A'') : G → A :=
  fun c ↦ S.liftCoeff (z.1 c)

@[simp] theorem g_snakeLift1 (z : Z1 G A'') (c : G) :
    S.g (S.snakeLift1 z c) = z.1 c :=
  S.g_liftCoeff (z.1 c)

theorem snakeLift1_continuous (z : Z1 G A'') : Continuous (S.snakeLift1 z) :=
  continuous_of_discreteTopology.comp (mem_Z1_iff.mp z.2).1

/-- The boundary of the chosen lift lands pointwise in `ker g`. -/
theorem snakeBoundary_g_zero (z : Z1 G A'') (p : G × G) :
    S.g (dOne G A (S.snakeLift1 z) p) = 0 := by
  change S.g (p.1 • S.snakeLift1 z p.2 - S.snakeLift1 z (p.1 * p.2) +
    S.snakeLift1 z p.1) = 0
  rw [map_add, map_sub, S.g_equivariant, S.g_snakeLift1, S.g_snakeLift1,
    S.g_snakeLift1, (mem_Z1_iff.mp z.2).2 p.1 p.2]
  abel

/-- The `A'`-valued two-cochain extracted by the continuous snake. -/
noncomputable def snakeZFun (z : Z1 G A'') : G × G → A' :=
  fun p ↦ S.kernelLift (dOne G A (S.snakeLift1 z) p)

theorem f_snakeZFun (z : Z1 G A'') (p : G × G) :
    S.f (S.snakeZFun z p) = dOne G A (S.snakeLift1 z) p :=
  S.f_kernelLift_of_mem_ker (S.snakeBoundary_g_zero z p)

theorem snakeBoundary_continuous (z : Z1 G A'') :
    Continuous (dOne G A (S.snakeLift1 z)) := by
  let hc := S.snakeLift1_continuous z
  exact ((continuous_fst.smul (hc.comp continuous_snd)).sub
    (hc.comp (continuous_fst.mul continuous_snd))).add (hc.comp continuous_fst)

theorem snakeZFun_continuous (z : Z1 G A'') : Continuous (S.snakeZFun z) :=
  continuous_of_discreteTopology.comp (S.snakeBoundary_continuous z)

/-- The cochain extracted by the snake is a continuous two-cocycle. -/
theorem snakeZFun_mem (z : Z1 G A'') : S.snakeZFun z ∈ Z2 G A' := by
  refine AddSubgroup.mem_inf.mpr ⟨S.snakeZFun_continuous z, ?_⟩
  rw [AddMonoidHom.mem_ker]
  funext t
  apply S.f_injective
  change S.f (dTwo G A' (S.snakeZFun z) t) = S.f (0 : A')
  rw [map_zero]
  change S.f (t.1 • S.snakeZFun z (t.2.1, t.2.2) -
    S.snakeZFun z (t.1 * t.2.1, t.2.2) +
    S.snakeZFun z (t.1, t.2.1 * t.2.2) - S.snakeZFun z (t.1, t.2.1)) = 0
  rw [map_sub, map_add, map_sub, S.f_equivariant, S.f_snakeZFun,
    S.f_snakeZFun, S.f_snakeZFun, S.f_snakeZFun]
  change dTwo G A (dOne G A (S.snakeLift1 z)) t = 0
  rw [← AddMonoidHom.comp_apply, dTwo_comp_dOne, AddMonoidHom.zero_apply]
  rfl

/-- The canonical continuous snake cocycle attached to a continuous one-cocycle. -/
noncomputable def snakeZ (z : Z1 G A'') : Z2 G A' :=
  ⟨S.snakeZFun z, S.snakeZFun_mem z⟩

@[simp] theorem snakeZ_apply (z : Z1 G A'') (p : G × G) :
    (S.snakeZ z).1 p = S.snakeZFun z p := rfl

theorem f_snakeZ (z : Z1 G A'') (p : G × G) :
    S.f ((S.snakeZ z).1 p) = dOne G A (S.snakeLift1 z) p :=
  S.f_snakeZFun z p

end FiniteDiscreteCoeffSES

end CoefficientSES

/-! ## The four-term comparison chase -/

section FourTerm

variable {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : Type*}
  [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂] [AddCommGroup Y₃]

/-- A four-term five-lemma window tailored to degree-two coefficient dévissage.

Think of the top row as continuous cohomology
`H¹(A'') → H²(A') → H²(A) → H²(A'')`, the bottom row as a comparison complex, and `m₂` as
the desired comparison on `A`.  The hypothesis `ha₂` is the explicit form of the only
degree-three input: `H²(A) → H²(A'')` must be onto. -/
theorem fourTermComparison_bijective
    (a₀ : X₀ →+ X₁) (a₁ : X₁ →+ X₂) (a₂ : X₂ →+ X₃)
    (b₀ : Y₀ →+ Y₁) (b₁ : Y₁ →+ Y₂) (b₂ : Y₂ →+ Y₃)
    (m₀ : X₀ →+ Y₀) (m₁ : X₁ →+ Y₁) (m₂ : X₂ →+ Y₂) (m₃ : X₃ →+ Y₃)
    (sq₀ : ∀ x, m₁ (a₀ x) = b₀ (m₀ x))
    (sq₁ : ∀ x, m₂ (a₁ x) = b₁ (m₁ x))
    (sq₂ : ∀ x, m₃ (a₂ x) = b₂ (m₂ x))
    (htop₁ : ∀ x : X₁, a₁ x = 0 ↔ x ∈ a₀.range)
    (htop₂ : ∀ x : X₂, a₂ x = 0 ↔ x ∈ a₁.range)
    (hbot₁ : ∀ y : Y₁, b₁ y = 0 ↔ y ∈ b₀.range)
    (hbot₂ : ∀ y : Y₂, b₂ y = 0 ↔ y ∈ b₁.range)
    (ha₂ : Function.Surjective a₂)
    (hm₀ : Function.Bijective m₀) (hm₁ : Function.Bijective m₁)
    (hm₃ : Function.Bijective m₃) :
    Function.Bijective m₂ := by
  constructor
  · exact FoxH.four_lemma_inj a₀ a₁ a₂ b₀ b₁ b₂ m₀ m₁ m₂ m₃
      sq₀ sq₁ sq₂ htop₁ htop₂ (fun y hy ↦ (hbot₁ y).mp hy)
      hm₀.2 hm₁.1 hm₃.1
  · intro y₂
    obtain ⟨x₃, hx₃⟩ := hm₃.2 (b₂ y₂)
    obtain ⟨x₂, hx₂⟩ := ha₂ x₃
    have hdiff : b₂ (y₂ - m₂ x₂) = 0 := by
      rw [map_sub, ← sq₂, hx₂, hx₃, sub_self]
    obtain ⟨y₁, hy₁⟩ := AddMonoidHom.mem_range.mp ((hbot₂ _).mp hdiff)
    obtain ⟨x₁, hx₁⟩ := hm₁.2 y₁
    refine ⟨x₂ + a₁ x₁, ?_⟩
    rw [map_add, sq₁, hx₁, hy₁]
    abel

end FourTerm

/-! ## The explicit degree-three tail hypothesis -/

section ContinuousTail

variable {G A A'' : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup A''] [TopologicalSpace A''] [IsTopologicalAddGroup A'']
  [DistribMulAction G A''] [ContinuousSMul G A'']

/-- The exact CD-2 tail condition needed for a coefficient quotient `A → A''`: the induced
map on `H²` is onto.  In a long exact sequence this is equivalent to vanishing of the following
connecting map into `H³` on the image, and follows from `H³(G,A') = 0`.

It is named independently because the present continuous-cohomology API stops at degree two. -/
def H2RightExactAt (g : A →+ A'') (hg : Continuous g)
    (hgeq : ∀ (c : G) (a : A), g (c • a) = c • g a) : Prop :=
  Function.Surjective (mapCoeff2 g hg hgeq)

end ContinuousTail

section ContinuousLESTail

variable {G A' A A'' : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A'] [TopologicalSpace A'] [IsTopologicalAddGroup A']
  [DistribMulAction G A'] [ContinuousSMul G A']
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup A''] [TopologicalSpace A''] [IsTopologicalAddGroup A'']
  [DistribMulAction G A''] [ContinuousSMul G A'']

/-- The exact continuous-cohomology tail needed by degree-two comparison dévissage.

The coefficient maps themselves already exist in `ContCoh`.  Constructing this package from a
short exact coefficient sequence is the irreducible missing continuous-LES lemma.  The first
two fields are obtainable by a degree-`1`/`2` cochain snake construction.  The final field is
the genuine cohomological-dimension input and cannot be proved from the degree-`≤ 2` complex
alone. -/
structure H2LongExactTail
    (f : A' →+ A) (g : A →+ A'')
    (hf : Continuous f) (hg : Continuous g)
    (hfeq : ∀ (c : G) (a : A'), f (c • a) = c • f a)
    (hgeq : ∀ (c : G) (a : A), g (c • a) = c • g a) where
  /-- The coefficient connecting map `H¹(G,A'') → H²(G,A')`. -/
  delta1 : H1 G A'' →+ H2 G A'
  /-- Exactness at `H²(G,A')`. -/
  exact_left : ∀ x : H2 G A',
    mapCoeff2 f hf hfeq x = 0 ↔ x ∈ delta1.range
  /-- Exactness at `H²(G,A)`. -/
  exact_middle : ∀ x : H2 G A,
    mapCoeff2 g hg hgeq x = 0 ↔ x ∈ (mapCoeff2 f hf hfeq).range
  /-- The CD-2/H³-vanishing tail, in the only form used by the diagram chase. -/
  right_exact : H2RightExactAt g hg hgeq

end ContinuousLESTail

/-! ## Composition-series induction for an arbitrary coefficient property -/

universe u v

variable {C : Type u} [Group C]

/-- A property of finite `C`-modules in one fixed universe.  Typical instances bundle the
three direct Tate cup bijectivities, or a continuous-to-word `H²` comparison together with the
independent word Stokes theorem. -/
abbrev FiniteTwoModuleProperty :=
  ∀ (A : Type v) [AddCommGroup A] [DistribMulAction C A] [Finite A], Prop

/-- Any property of finite exponent-two modules that holds for the zero module and simple
modules and is closed under stable subquotient extensions holds for every finite exponent-two
module.

This is the reusable coefficient dévissage shell.  For direct Tate perfectness or the `L`
source-to-word `H²` comparison, `hstep` is exactly where `fourTermComparison_bijective` and the
continuous coefficient LES are consumed. -/
theorem finiteTwoModuleProperty_of_simple
    (P : FiniteTwoModuleProperty (C := C))
    (hzero : ∀ (A : Type v) [AddCommGroup A] [DistribMulAction C A] [Finite A]
      [Subsingleton A], P A)
    (hsimple : ∀ (A : Type v) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) → FoxH.IsSimpleModTwo C A → P A)
    (hstep : ∀ (A : Type v) [AddCommGroup A] [DistribMulAction C A] [Finite A]
      (_hA₂ : ∀ a : A, a + a = 0) (W : AddSubgroup A)
      (hWstable : ∀ (c : C) (w : A), w ∈ W → c • w ∈ W)
      (_hWbot : W ≠ ⊥) (_hWtop : W ≠ ⊤),
      letI : DistribMulAction C ↥W := FoxH.stableSubAction W hWstable
      letI : DistribMulAction C (A ⧸ W) := FoxH.stableQuotAction W hWstable
      P ↥W → P (A ⧸ W) → P A)
    {A : Type v} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : P A := by
  suffices h : ∀ (n : ℕ) (B : Type v) [AddCommGroup B] [DistribMulAction C B] [Finite B],
      Nat.card B = n → (∀ b : B, b + b = 0) → P B by
    exact h (Nat.card A) A rfl hA₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
      intro B instAdd instAct instFin hcard hB₂
      rcases subsingleton_or_nontrivial B with hsub | hnt
      · letI : Subsingleton B := hsub
        exact hzero B
      · by_cases hsimp : FoxH.IsSimpleModTwo C B
        · exact hsimple B hB₂ hsimp
        · rw [FoxH.IsSimpleModTwo] at hsimp
          push Not at hsimp
          obtain ⟨W, hWstable, hWbot, hWtop⟩ := hsimp hnt
          letI := FoxH.stableSubAction W hWstable
          letI := FoxH.stableQuotAction W hWstable
          have hW₂ : ∀ w : ↥W, w + w = 0 := FoxH.two_torsion_sub W hB₂
          have hQ₂ : ∀ q : B ⧸ W, q + q = 0 := FoxH.two_torsion_quot W hB₂
          have hltW : Nat.card ↥W < n := hcard ▸ FoxH.card_lt_of_ne_top W hWtop
          have hltQ : Nat.card (B ⧸ W) < n :=
            hcard ▸ FoxH.card_quot_lt_of_ne_bot W hWbot
          have ihW : P ↥W := IH _ hltW ↥W rfl hW₂
          have ihQ : P (B ⧸ W) := IH _ hltQ (B ⧸ W) rfl hQ₂
          exact hstep B hB₂ W hWstable hWbot hWtop ihW ihQ

end ContCoh

end GQ2
