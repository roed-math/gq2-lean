/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Eval
public import GQ2.MixedBilinear
public import GQ2.DevissageInduction

@[expose] public section

/-!
# Dyadic campaign, ticket WW3: the second-order (Stokes) layer for reflected words

Three deliverables (board WW3 spec; plan §3 A1; packet §5 and Lem. `lem:composition`):

1. **The `PWord` denotation into `HeisLift A C`** (`heisGen`, `heisEvalZ`): the reflected word
   evaluated in the Heisenberg lift, whose central coordinate obeys the packet's second-order
   rule `β(uv) = β(u) + β(v) + D^∨(u)(ū·D(v))` — literally `HeisLift.mul_z` read through the
   evaluation (`heisEvalZ_mul_z`).  The **no-cross-term headline** (`HeisLift.mul_z_of_jetZero`):
   a factor with zero first jet contributes no cross term on either side — the entire
   "shadow copies cancel in char 2" step that the WMP lane consumes.

2. **The natural chain map** `η_A : C•(A) → Hom(C•(A^∨), 𝔽₂)[−2]` (`heisEta0/1/2`) over the
   generic word complex `heisD0`/`heisD1` of an arbitrary relator family, with the chain
   conditions (`heisEta_comm₀₁`, `heisEta_comm₁₂`) proved from the frozen `n`-generic Stokes
   layer `GQ2.FoxH.lemma_5_7_left/right` under the **endpoint condition** `IsStokesEndpoint`
   (the traced mod-2 exponent vector of the relator family vanishes — the degree-`n` form of
   `GQ2.FoxH.expMod2_tame_add_wildValueExpR_odd`).

3. **Packet Lem. 5.1** (`lem:composition`), the composition-series extension
   (`stokes_quasiIso_of_simple`): if `η_V` is a quasi-isomorphism for every simple module `V`,
   it is one for every finite elementary module — including **nonsplit** coefficients.  Proved
   by **mapping cones** (the packet's "equivalently" clause): the cone of the ladder is a
   four-term complex, quasi-isomorphism = cone acyclicity (`stokesQuasiIso_iff_cone`), and
   acyclicity propagates along a short exact sequence of cones by one generic exactness chase
   (`stokes_chase`) — dimension equalities are never used, exactly as the packet's warning
   demands.  This file does the dévissage **once, generically**: the frozen `ℚ₂` chain cloned a
   2394-line dévissage per word (`GQ2/Devissage` → `GQ2/Roe/Devissage`); the five branch lanes
   instantiate this engine instead (wl-recon §4.1, risk R5).

Scalar lane: the cup–Bockstein extraction hooks (`stokesGram`) in the marked local Hilbert
matrix comparison shape (`GQ2/Roe/TrivialSelfDual.lean`'s `scalarGramR`-by-`decide` pattern).

## Design notes

* The denotation **reuses `PWord.evalZ`** at the lifted marking rather than a new recursion:
  the Heisenberg product/inverse laws *are* the packet's second-order Fox rules, so the rules
  hold definitionally and every F2 naturality theorem applies verbatim.
* Every `PWord` evaluation factors through the free group (`heisToFree`,
  `evalZ_eq_lift_heisToFree`), so the frozen `Fin n`-generic layer (`stokesEval`,
  `lemma_5_7_left/right`, `GQ2/MixedBilinear.lean`) transports to any finite alphabet along
  `FreeGroup.freeGroupCongr` — reuse, not re-proof.
* The word-complex layer is stated over an arbitrary `[Fintype ι] [DecidableEq ι]` alphabet and
  an arbitrary `[Fintype ρ]` relator family, so one engine serves all five branch families at
  every degree `n` (`ι := Generator n`, `ρ := Fin 2`).
* Quasi-isomorphism is stated in **relative (quotient-free) form** (`StokesQuasiIso`): six
  clauses equivalent to bijectivity of `H⁰(η), H¹(η), H²(η)`, phrased without quotient types.
  The cone is internal machinery; consumers see the six clauses.
* The `𝔽₂`-dual side rides on the frozen elementary-dual pack
  (`GQ2/Devissage/ElemDualPack.lean`: `dualMap`, `dualMap_injective/surjective`,
  `dual_ses_exact`) and the composition-series driver on the frozen stable-action
  infrastructure (`GQ2/DevissageInduction.lean`).
* `HeisLift` has a `ZMod 2` centre; nothing here speaks about `ℤ/4`-centre lifts (the twisted
  path and the `κ_q⁰` normalization are WW4's, per S1.T).

Module-style: all three imports are module-style.
-/

namespace GQ2.Dyadic

open GQ2.FoxH

/-! ## The no-cross-term (shadow-cancellation) toolkit

`class2.py`'s bilinear-λ argument, at the `HeisLift` level: the central cocycle
`(p·q).z = p.z + q.z + p.l(p.g • q.a)` loses its cross term as soon as the relevant first jet
vanishes.  A factor with **zero first jet** (`p.a = 0` and `p.l = 0`) is centrally transparent
in products on *either* side; consequently the jet-zero elements form a subgroup on which `.z`
is additive, and a shadow copy cancels its twin in char 2.  The WMP lane consumes exactly this
(`R̂^pc = Sh_M(R_lin^pc)` has zero first jet, so `β(R_lin·R̂) = β(R_lin) + β(R̂)`). -/

section ZeroJet

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- No cross term when the **left** factor has zero dual jet. -/
theorem heisMul_z_of_l_eq_zero (p q : HeisLift A C) (hl : p.l = 0) :
    (p * q).z = p.z + q.z := by
  rw [HeisLift.mul_z, hl, ElemDual.zero_apply, add_zero]

/-- No cross term when the **right** factor has zero primal jet. -/
theorem heisMul_z_of_a_eq_zero (p q : HeisLift A C) (ha : q.a = 0) :
    (p * q).z = p.z + q.z := by
  rw [HeisLift.mul_z, ha, smul_zero, map_zero, add_zero]

/-- **The no-cross-term headline** (`class2.py`'s bilinear-λ argument): a factor with zero
first jet — both `D(u) = 0` and `D^∨(u) = 0` — contributes no cross term to the central
coordinate of a product, on either side.  This is the entire "shadow copies cancel in char 2"
step; the WMP lane consumes it for the hat copy `R̂^pc`. -/
theorem heisMul_z_of_jetZero (p q : HeisLift A C) (ha : p.a = 0) (hl : p.l = 0) :
    (p * q).z = p.z + q.z ∧ (q * p).z = q.z + p.z :=
  ⟨heisMul_z_of_l_eq_zero p q hl, heisMul_z_of_a_eq_zero q p ha⟩

/-- The jet-zero elements form a subgroup of `H(A) ⋊ C` (arbitrary central value and base). -/
def heisJetZero (A C : Type*) [Group C] [AddCommGroup A] [DistribMulAction C A] :
    Subgroup (HeisLift A C) where
  carrier := {p | p.a = 0 ∧ p.l = 0}
  one_mem' := ⟨rfl, rfl⟩
  mul_mem' := fun {p q} hp hq =>
    ⟨by rw [HeisLift.mul_a, hp.1, hq.1, smul_zero, add_zero],
     by rw [HeisLift.mul_l, hp.2, hq.2, smul_zero, add_zero]⟩
  inv_mem' := fun {p} hp =>
    ⟨by rw [HeisLift.inv_a, hp.1, smul_zero, neg_zero],
     by rw [HeisLift.inv_l, hp.2, smul_zero, neg_zero]⟩

@[simp] theorem mem_heisJetZero {p : HeisLift A C} :
    p ∈ heisJetZero A C ↔ p.a = 0 ∧ p.l = 0 := Iff.rfl

/-- On the jet-zero subgroup the central coordinate is **additive**: a product of shadow
factors has central value the sum of the factors' central values. -/
theorem heisJetZero_mul_z {p q : HeisLift A C} (hp : p ∈ heisJetZero A C) :
    (p * q).z = p.z + q.z :=
  heisMul_z_of_l_eq_zero p q hp.2

/-- **Shadow copies cancel in char 2**: a jet-zero element and its copy multiply to central
value zero.  (The value type's central slot is `ZMod 2`, so `z + z = 0`.) -/
theorem heisJetZero_sq_z {p : HeisLift A C} (hp : p ∈ heisJetZero A C) : (p * p).z = 0 := by
  rw [heisJetZero_mul_z hp, CharTwo.add_self_eq_zero]

end ZeroJet

/-! ## The second-order denotation of a reflected word -/

section Denotation

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The **Heisenberg-lifted generator marking**: each letter `i` goes to
`(xᵢ, yᵢ, 0; μᵢ) ∈ H(A) ⋊ C` — base value `μ i`, primal offset `x i`, dual offset `y i`,
central value `0`.  The `PWord` twin of `GQ2.FoxH.stokesEval`'s generator substitution. -/
def heisGen (μ : X → C) (x : X → A) (y : X → ElemDual A) : X → HeisLift A C :=
  fun i => ⟨x i, y i, 0, μ i⟩

omit [Group C] [DistribMulAction C A] in
@[simp] theorem heisGen_apply (μ : X → C) (x : X → A) (y : X → ElemDual A) (i : X) :
    heisGen μ x y i = ⟨x i, y i, 0, μ i⟩ := rfl

/-- **The second-order (Stokes) denotation** of a reflected word: `PWord.evalZ` at the
Heisenberg-lifted marking.  No new recursion is introduced: the Heisenberg multiplication *is*
the second-order rule, so the packet's finite Fox calculus holds definitionally
(`heisEvalZ_mul_z`, `heisEvalZ_inv_z`) and all F2 naturality theorems apply verbatim. -/
noncomputable def heisEvalZ (μ : X → C) (x : X → A) (y : X → ElemDual A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : PWord X → HeisLift A C :=
  PWord.evalZ (heisGen μ x y) E E₂

variable (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

@[simp] theorem heisEvalZ_gen (i : X) :
    heisEvalZ μ x y E E₂ (.gen i) = ⟨x i, y i, 0, μ i⟩ := rfl

@[simp] theorem heisEvalZ_mul (u v : PWord X) :
    heisEvalZ μ x y E E₂ (.mul u v)
      = heisEvalZ μ x y E E₂ u * heisEvalZ μ x y E E₂ v := rfl

@[simp] theorem heisEvalZ_inv (u : PWord X) :
    heisEvalZ μ x y E E₂ (.inv u) = (heisEvalZ μ x y E E₂ u)⁻¹ := rfl

/-- **The second-order product rule** (packet §5, display `β(uv) = β(u) + β(v) + D^∨(u)(ū·D(v))`):
the central coordinate of a product denotation is the sum of the central coordinates plus the
mixed cross term — the dual first derivative of `u` evaluated at the `ū`-translate of the primal
first derivative of `v`. -/
theorem heisEvalZ_mul_z (u v : PWord X) :
    (heisEvalZ μ x y E E₂ (.mul u v)).z
      = (heisEvalZ μ x y E E₂ u).z + (heisEvalZ μ x y E E₂ v).z
        + (heisEvalZ μ x y E E₂ u).l
            ((heisEvalZ μ x y E E₂ u).g • (heisEvalZ μ x y E E₂ v).a) := rfl

/-- The second-order inverse rule `β(u⁻¹) = β(u) + D^∨(u)(D(u))` (the sign is absorbed by
char 2). -/
theorem heisEvalZ_inv_z (u : PWord X) :
    (heisEvalZ μ x y E E₂ (.inv u)).z
      = (heisEvalZ μ x y E E₂ u).z
        + (heisEvalZ μ x y E E₂ u).l ((heisEvalZ μ x y E E₂ u).a) := rfl

/-- The no-cross-term headline at the word level: if `u` denotes a jet-zero element, the
central coordinate is additive on `u·v`. -/
theorem heisEvalZ_mul_z_of_jetZero (u v : PWord X)
    (hu : heisEvalZ μ x y E E₂ u ∈ heisJetZero A C) :
    (heisEvalZ μ x y E E₂ (.mul u v)).z
      = (heisEvalZ μ x y E E₂ u).z + (heisEvalZ μ x y E E₂ v).z :=
  heisJetZero_mul_z hu

end Denotation

/-! ## The free-group bridge

Every `evalZ` denotation factors through the free group on the alphabet: resolving the
profinite exponents first (`heisToFree`) and then substituting is the same as substituting
directly.  This is the reuse mechanism for the frozen `n`-generic Stokes layer: the second-order
denotation of a reflected word *is* `stokesEval` of its resolved free word. -/

section FreeBridge

variable {X : Type*}

/-- The **resolved free word** of a reflected word: profinite and `2`-adic exponents are
resolved to integers by `E`, `E₂`, and the word is read in `FreeGroup X`. -/
def heisToFree (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : PWord X → FreeGroup X :=
  PWord.evalZ FreeGroup.of E E₂

/-- **The bridge**: any `evalZ` denotation is the free-group substitution of the resolved
word. -/
theorem evalZ_eq_lift_heisToFree {G : Type*} [Group G] (μ : X → G) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    PWord.evalZ μ E E₂ w = FreeGroup.lift μ (heisToFree E E₂ w) := by
  have h := PWord.map_evalZ (FreeGroup.lift μ) FreeGroup.of E E₂ w
  rw [heisToFree, h]
  congr 1
  funext g
  rw [FreeGroup.lift_apply_of]

/-- The second-order denotation is `FreeGroup.lift` of the lifted marking at the resolved
word — the `PWord` form of `GQ2.FoxH.stokesEval`. -/
theorem heisEvalZ_eq_lift {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    heisEvalZ μ x y E E₂ w = FreeGroup.lift (heisGen μ x y) (heisToFree E E₂ w) :=
  evalZ_eq_lift_heisToFree _ E E₂ w

end FreeBridge

/-! ## The word-level Stokes layer over an arbitrary alphabet

The frozen layer (`GQ2/FoxHeisenberg/Heisenberg.lean`, `GQ2/MixedBilinear.lean`) is stated over
`Fin n`.  The campaign's alphabet is `Generator n` (and the engine below serves any finite
alphabet), so this section provides the word-level toolkit over an arbitrary `ι`:

* the small coordinate lemmas (`heisWord_g`, additivity, independence, vanishing) are mirrored
  directly — their statements are alphabet-indexed, and the `FreeGroup.induction_on` proofs are
  index-agnostic;
* the two **long** theorems, Lemma 5.7 left/right, are **transported** from the frozen
  `lemma_5_7_left`/`lemma_5_7_right` along `FreeGroup.freeGroupCongr` — reuse, not re-proof. -/

section WordLayer

variable {ι : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The base coordinate of a word-level Stokes evaluation is the underlying word value
(`GQ2.FoxH.stokesEval_g`, alphabet-generic form). -/
theorem heisWord_g (c : ι → C) (x : ι → A) (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x y) r).g = FreeGroup.lift c r := by
  have h : (HeisLift.gHom).comp (FreeGroup.lift (heisGen c x y)) = FreeGroup.lift c :=
    FreeGroup.ext_hom _ _ fun i => rfl
  exact DFunLike.congr_fun h r

/-- With zero primal offsets, the `.a`- and `.z`-coordinates vanish
(`GQ2.FoxH.stokesEval_zero`). -/
theorem heisWord_zero_prim (c : ι → C) (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c 0 y) r).a = 0 ∧ (FreeGroup.lift (heisGen c 0 y) r).z = 0 := by
  refine FreeGroup.induction_on r ⟨rfl, rfl⟩
    (fun i => ⟨by simp [FreeGroup.lift_apply_of], by simp [FreeGroup.lift_apply_of]⟩)
    (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · rw [map_inv]
    exact ⟨by rw [HeisLift.inv_a, ih.1, smul_zero, neg_zero],
      by rw [HeisLift.inv_z, ih.2, ih.1, map_zero, add_zero]⟩
  · rw [map_mul]
    exact ⟨by rw [HeisLift.mul_a, ih₁.1, ih₂.1, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih₁.2, ih₂.2, ih₂.1, smul_zero, map_zero, add_zero, add_zero]⟩

/-- With zero dual offsets, the `.l`- and `.z`-coordinates vanish
(`GQ2.FoxH.stokesEval_zero_r`). -/
theorem heisWord_zero_dual (c : ι → C) (x : ι → A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x 0) r).l = 0 ∧ (FreeGroup.lift (heisGen c x 0) r).z = 0 := by
  refine FreeGroup.induction_on r ⟨rfl, rfl⟩
    (fun i => ⟨by simp [FreeGroup.lift_apply_of], by simp [FreeGroup.lift_apply_of]⟩)
    (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · rw [map_inv]
    exact ⟨by rw [HeisLift.inv_l, ih.1, smul_zero, neg_zero],
      by rw [HeisLift.inv_z, ih.2, ih.1, ElemDual.zero_apply, add_zero]⟩
  · rw [map_mul]
    exact ⟨by rw [HeisLift.mul_l, ih₁.1, ih₂.1, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih₁.2, ih₂.2, ih₁.1, ElemDual.zero_apply, add_zero, add_zero]⟩

/-- The `.a`-coordinate is independent of the dual offsets (`GQ2.FoxH.stokesEval_a_indep`). -/
theorem heisWord_a_indep (c : ι → C) (x : ι → A) (y y' : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x y) r).a = (FreeGroup.lift (heisGen c x y') r).a := by
  refine FreeGroup.induction_on r rfl (fun i => rfl) (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · rw [map_inv, map_inv, HeisLift.inv_a, HeisLift.inv_a, heisWord_g, heisWord_g, ih]
  · rw [map_mul, map_mul, HeisLift.mul_a, HeisLift.mul_a, heisWord_g, heisWord_g, ih₁, ih₂]

/-- The `.l`-coordinate is independent of the primal offsets (`GQ2.FoxH.stokesEval_l_indep`). -/
theorem heisWord_l_indep (c : ι → C) (x x' : ι → A) (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x y) r).l = (FreeGroup.lift (heisGen c x' y) r).l := by
  refine FreeGroup.induction_on r rfl (fun i => rfl) (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · rw [map_inv, map_inv, HeisLift.inv_l, HeisLift.inv_l, heisWord_g, heisWord_g, ih]
  · rw [map_mul, map_mul, HeisLift.mul_l, HeisLift.mul_l, heisWord_g, heisWord_g, ih₁, ih₂]

/-- The `.a`-coordinate is additive in the primal offsets (`GQ2.FoxH.stokesEval_a_add`). -/
theorem heisWord_a_add (c : ι → C) (x x' : ι → A) (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c (x + x') y) r).a
      = (FreeGroup.lift (heisGen c x y) r).a + (FreeGroup.lift (heisGen c x' y) r).a := by
  refine FreeGroup.induction_on r (by simp) (fun i => ?_) (fun i ih => ?_)
    (fun r₁ r₂ ih₁ ih₂ => ?_)
  · simp [FreeGroup.lift_apply_of, Pi.add_apply]
  · rw [map_inv, map_inv, map_inv, HeisLift.inv_a, HeisLift.inv_a, HeisLift.inv_a,
      heisWord_g, heisWord_g, heisWord_g, ih, smul_add, neg_add]
  · rw [map_mul, map_mul, map_mul, HeisLift.mul_a, HeisLift.mul_a, HeisLift.mul_a,
      heisWord_g, heisWord_g, heisWord_g, ih₁, ih₂, smul_add]
    abel

/-- The `.l`-coordinate is additive in the dual offsets (`GQ2.FoxH.stokesEval_l_add`). -/
theorem heisWord_l_add (c : ι → C) (x : ι → A) (y y' : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x (y + y')) r).l
      = (FreeGroup.lift (heisGen c x y) r).l + (FreeGroup.lift (heisGen c x y') r).l := by
  refine FreeGroup.induction_on r (by simp) (fun i => ?_) (fun i ih => ?_)
    (fun r₁ r₂ ih₁ ih₂ => ?_)
  · simp [FreeGroup.lift_apply_of, Pi.add_apply]
  · rw [map_inv, map_inv, map_inv, HeisLift.inv_l, HeisLift.inv_l, HeisLift.inv_l,
      heisWord_g, heisWord_g, heisWord_g, ih, smul_add, neg_add]
  · rw [map_mul, map_mul, map_mul, HeisLift.mul_l, HeisLift.mul_l, HeisLift.mul_l,
      heisWord_g, heisWord_g, heisWord_g, ih₁, ih₂, smul_add]
    abel

/-- The `.z`-coordinate is additive in the primal offsets
(`GQ2.FoxH.stokesEval_z_add_left`). -/
theorem heisWord_z_add_left (c : ι → C) (x x' : ι → A) (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c (x + x') y) r).z
      = (FreeGroup.lift (heisGen c x y) r).z + (FreeGroup.lift (heisGen c x' y) r).z := by
  refine FreeGroup.induction_on r (by simp) (fun i => ?_) (fun i ih => ?_)
    (fun r₁ r₂ ih₁ ih₂ => ?_)
  · simp [FreeGroup.lift_apply_of]
  · simp only [map_inv, HeisLift.inv_z, FreeGroup.lift_apply_of, heisGen_apply,
      Pi.add_apply, map_add, zero_add]
  · have hl : (FreeGroup.lift (heisGen c (x + x') y) r₁).l
        = (FreeGroup.lift (heisGen c x y) r₁).l := heisWord_l_indep c (x + x') x y r₁
    have hl' : (FreeGroup.lift (heisGen c x' y) r₁).l
        = (FreeGroup.lift (heisGen c x y) r₁).l := heisWord_l_indep c x' x y r₁
    simp only [map_mul, HeisLift.mul_z, ih₁, ih₂, heisWord_a_add, smul_add, map_add, hl, hl',
      heisWord_g]
    abel

/-- The `.z`-coordinate is additive in the dual offsets
(`GQ2.FoxH.stokesEval_z_add_right`). -/
theorem heisWord_z_add_right (c : ι → C) (x : ι → A) (y y' : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x (y + y')) r).z
      = (FreeGroup.lift (heisGen c x y) r).z + (FreeGroup.lift (heisGen c x y') r).z := by
  refine FreeGroup.induction_on r (by simp) (fun i => ?_) (fun i ih => ?_)
    (fun r₁ r₂ ih₁ ih₂ => ?_)
  · simp [FreeGroup.lift_apply_of]
  · simp only [map_inv, HeisLift.inv_z, FreeGroup.lift_apply_of, heisGen_apply,
      Pi.add_apply, ElemDual.add_apply, zero_add]
  · have ha : (FreeGroup.lift (heisGen c x (y + y')) r₂).a
        = (FreeGroup.lift (heisGen c x y) r₂).a := heisWord_a_indep c x (y + y') y r₂
    have ha' : (FreeGroup.lift (heisGen c x y') r₂).a
        = (FreeGroup.lift (heisGen c x y) r₂).a := heisWord_a_indep c x y' y r₂
    simp only [map_mul, HeisLift.mul_z, ih₁, ih₂, heisWord_l_add, ElemDual.add_apply, ha, ha',
      heisWord_g]
    abel

end WordLayer

/-! ### The mod-2 exponent vector and the transported Lemma 5.7 -/

section EpsTransport

variable {ι : Type*} [DecidableEq ι] {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A]

/-- The per-generator mod-2 total exponent over an arbitrary alphabet
(`GQ2.FoxH.expMod2`, alphabet-generic twin). -/
def heisEps (i : ι) : FreeGroup ι →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if j = i then 1 else 0)

omit [DecidableEq ι] in
/-- Transport of a free-group substitution along an alphabet equivalence. -/
private theorem lift_symm_congr {m : ℕ} (e : ι ≃ Fin m) {G : Type*} [Group G] (f : ι → G)
    (r : FreeGroup ι) :
    FreeGroup.lift (fun j => f (e.symm j)) (FreeGroup.freeGroupCongr e r)
      = FreeGroup.lift f r := by
  have h : (FreeGroup.lift (fun j => f (e.symm j))).comp
        (FreeGroup.freeGroupCongr e).toMonoidHom = FreeGroup.lift f := by
    apply FreeGroup.ext_hom
    intro i
    simp
  exact DFunLike.congr_fun h r

omit [DecidableEq ι] in
/-- Transport of the word-level Stokes evaluation along an alphabet equivalence: the
`heisGen`-substitution over `ι` is the frozen `stokesEval` over `Fin m` at the transported
data. -/
private theorem lift_heisGen_congr {m : ℕ} (e : ι ≃ Fin m) (c : ι → C) (x : ι → A)
    (y : ι → ElemDual A) (r : FreeGroup ι) :
    FreeGroup.lift (heisGen c x y) r
      = stokesEval (fun j => c (e.symm j)) (fun j => x (e.symm j)) (fun j => y (e.symm j))
          (FreeGroup.freeGroupCongr e r) := by
  have h : (stokesEval (fun j => c (e.symm j)) (fun j => x (e.symm j))
        (fun j => y (e.symm j))).comp (FreeGroup.freeGroupCongr e).toMonoidHom
      = FreeGroup.lift (heisGen c x y) := by
    apply FreeGroup.ext_hom
    intro i
    simp [stokesEval]
  exact (DFunLike.congr_fun h r).symm

/-- `heisEps` is the frozen `expMod2` read through the alphabet equivalence. -/
private theorem heisEps_eq_expMod2 {m : ℕ} (e : ι ≃ Fin m) (i : ι) (r : FreeGroup ι) :
    heisEps i r = expMod2 (e i) (FreeGroup.freeGroupCongr e r) := by
  have h : (expMod2 (e i)).comp (FreeGroup.freeGroupCongr e).toMonoidHom = heisEps i := by
    apply FreeGroup.ext_hom
    intro j
    simp [expMod2, heisEps]
  exact (DFunLike.congr_fun h r).symm

variable [Fintype ι]

/-- **Lemma 5.7, left (coboundary) form, alphabet-generic** — transported from the frozen
`GQ2.FoxH.lemma_5_7_left`: for a word `r` with trivial lower value, evaluating at the generic
coboundary `x = d⁰a = ((cᵢ−1)a)ᵢ` gives
`β_r(d⁰a, y) = L^{A^∨}_r(y)(a) + Σᵢ εᵢ(r)·yᵢ(cᵢa)`. -/
theorem heisWord_lemma_5_7_left (c : ι → C) (r : FreeGroup ι)
    (hr : FreeGroup.lift c r = 1) (a : A) (y : ι → ElemDual A) :
    (FreeGroup.lift (heisGen c (fun i => c i • a - a) y) r).z
      = (FreeGroup.lift (heisGen c 0 y) r).l a
        + ∑ i, Multiplicative.toAdd (heisEps i r) * (y i (c i • a)) := by
  set e := Fintype.equivFin ι
  have hr' : FreeGroup.lift (fun j => c (e.symm j)) (FreeGroup.freeGroupCongr e r) = 1 :=
    (lift_symm_congr e c r).trans hr
  have h57 := lemma_5_7_left (fun j => c (e.symm j)) (FreeGroup.freeGroupCongr e r) hr' a
    (fun j => y (e.symm j))
  have hsum : ∑ i, Multiplicative.toAdd (heisEps i r) * (y i (c i • a))
      = ∑ j, Multiplicative.toAdd (expMod2 j (FreeGroup.freeGroupCongr e r))
          * (y (e.symm j) (c (e.symm j) • a)) := by
    rw [← Equiv.sum_comp e
      (fun j => Multiplicative.toAdd (expMod2 j (FreeGroup.freeGroupCongr e r))
        * (y (e.symm j) (c (e.symm j) • a)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← heisEps_eq_expMod2 e, e.symm_apply_apply]
  rw [lift_heisGen_congr e c (fun i => c i • a - a) y r, lift_heisGen_congr e c 0 y r, hsum]
  exact h57

/-- **Lemma 5.7, right (dual-coboundary) form, alphabet-generic** — transported from the
frozen `GQ2.FoxH.lemma_5_7_right`:
`β_r(x, d⁰λ) = λ(L^A_r(x)) + Σᵢ εᵢ(r)·λ(xᵢ)`. -/
theorem heisWord_lemma_5_7_right (c : ι → C) (r : FreeGroup ι)
    (hr : FreeGroup.lift c r = 1) (x : ι → A) (lam : ElemDual A) :
    (FreeGroup.lift (heisGen c x (fun i => c i • lam - lam)) r).z
      = lam ((FreeGroup.lift (heisGen c x 0) r).a)
        + ∑ i, Multiplicative.toAdd (heisEps i r) * (lam (x i)) := by
  set e := Fintype.equivFin ι
  have hr' : FreeGroup.lift (fun j => c (e.symm j)) (FreeGroup.freeGroupCongr e r) = 1 :=
    (lift_symm_congr e c r).trans hr
  have h57 := lemma_5_7_right (fun j => c (e.symm j)) (FreeGroup.freeGroupCongr e r) hr'
    (fun j => x (e.symm j)) lam
  have hsum : ∑ i, Multiplicative.toAdd (heisEps i r) * (lam (x i))
      = ∑ j, Multiplicative.toAdd (expMod2 j (FreeGroup.freeGroupCongr e r))
          * (lam (x (e.symm j))) := by
    rw [← Equiv.sum_comp e
      (fun j => Multiplicative.toAdd (expMod2 j (FreeGroup.freeGroupCongr e r))
        * (lam (x (e.symm j))))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← heisEps_eq_expMod2 e, e.symm_apply_apply]
  rw [lift_heisGen_congr e c x (fun i => c i • lam - lam) r, lift_heisGen_congr e c x 0 r, hsum]
  exact h57

end EpsTransport

end GQ2.Dyadic
