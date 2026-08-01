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

## Axiom prints (recorded at commit time)

Every headline prints **exactly the standard three** (`propext`, `Classical.choice`,
`Quot.sound`) — verified via `#print axioms` for `stokesDuality_of_simple`,
`stokesDuality_of_ses`, `stokesConeAcyclic_of_ses`, `stokesQuasiIso_iff_coneAcyclic`,
`heisWord_lemma_5_7_left`, `heisWord_lemma_5_7_right`, `heisEta1_comp_d0`,
`heisEta2_comp_d1`, `StokesDuality.pairing_vanish_left`, `stress_endpoint_gammaA`,
`stress_jetZero_nonvacuous`.  No sorries, no new axioms, kernel `decide` only (the one
`decide` sits in a stress pin).  The one `local instance` is the trivial action of the
stress section (the known doesn't-export idiom; nothing consumes it).

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

/-! ## Powers, commutators and conjugates of trivial-base lifts

Three closed forms for `HeisLift`-values whose base acts trivially on the coefficient module —
the per-factor engine of every second-order row, one degree up from the Fox-level `trivAct`
toolkit of `GQ2/Dyadic/Word/Fox.lean`.  The commutator form needs **no** 2-torsion (the offsets
cancel exactly); only the power form's simplifications do. -/

section TrivialBase

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- A trivially-acting base acts trivially on the elementary dual as well
(the contragredient of the identity). -/
theorem smul_elemDual_of_trivial {g : C} (hg : ∀ a : A, g • a = a) (lam : ElemDual A) :
    g • lam = lam := by
  refine ElemDual.ext fun a => ?_
  rw [ElemDual.smul_apply]
  exact congrArg lam (inv_smul_eq_iff.mpr (hg a).symm)

private theorem elemDual_nsmul_apply (k : ℕ) (f : ElemDual A) (a : A) :
    (k • f) a = k • f a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ElemDual.add_apply, ih]

/-- **The power law for a trivial-base Heisenberg lift**:
`p^n = (n·a, n·λ, n·z + C(n,2)·λ(a); gⁿ)`.  The binomial coefficient is the whole
second-order content of a power — the `q(c₀)`-production mechanism of a leading even
wild power. -/
theorem heisPow_of_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (n : ℕ) :
    p ^ n = ⟨n • p.a, n • p.l, n • p.z + (n.choose 2) • p.l p.a, p.g ^ n⟩ := by
  have hgpow : ∀ (m : ℕ) (a : A), (p.g ^ m) • a = a := by
    intro m
    induction m with
    | zero => intro a; rw [pow_zero, one_smul]
    | succ m ih => intro a; rw [pow_succ, mul_smul, hp, ih]
  induction n with
  | zero =>
      refine HeisLift.ext ?_ ?_ ?_ ?_ <;> simp
  | succ n ih =>
      have hgn : ∀ a : A, (p.g ^ n) • a = a := hgpow n
      rw [pow_succ, ih]
      refine HeisLift.ext ?_ ?_ ?_ ?_
      · show n • p.a + (p.g ^ n) • p.a = (n + 1) • p.a
        rw [hgn, succ_nsmul]
      · show n • p.l + (p.g ^ n) • p.l = (n + 1) • p.l
        rw [smul_elemDual_of_trivial hgn, succ_nsmul]
      · show n • p.z + (n.choose 2) • p.l p.a + p.z + (n • p.l) ((p.g ^ n) • p.a)
          = (n + 1) • p.z + ((n + 1).choose 2) • p.l p.a
        rw [hgn, elemDual_nsmul_apply, Nat.choose_succ_succ n 1, Nat.choose_one_right]
        simp only [add_nsmul, succ_nsmul]
        abel
      · show p.g ^ n * p.g = p.g ^ (n + 1)
        rw [pow_succ]

/-- **The commutator of two trivial-base Heisenberg lifts is jet-zero central** with
value the mixed pairing `λ_p(a_q) + λ_q(a_p)` — an identity-operator hyperbolic plane.
No 2-torsion hypothesis: the offsets cancel exactly, only the `ZMod 2` centre folds
signs.  This is each handle pair's entire second-order content. -/
theorem heisCommR_of_trivial (p r : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hr : ∀ a : A, r.g • a = a) :
    commR p r = ⟨0, 0, p.l r.a + r.l p.a, commR p.g r.g⟩ := by
  have hpi : ∀ a : A, p.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hp a).symm
  have hri : ∀ a : A, r.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hr a).symm
  rw [commR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hp, hpi, hri]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_elemDual_of_trivial hp, smul_elemDual_of_trivial hpi, smul_elemDual_of_trivial hri]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.inv_z,
      HeisLift.inv_a, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      hp, hpi, hri, smul_elemDual_of_trivial hpi, smul_elemDual_of_trivial hri]
    simp only [ElemDual.add_apply, ElemDual.neg_apply, map_neg]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add, add_zero]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

/-- **The conjugate of a trivial-base lift by an arbitrary lift**:
`p^s = (s⁻¹·a_p, s⁻¹·λ_p, z_p + λ_s(a_p) + λ_p(a_s); p.g^{s.g})`.  Both `s`-offsets
survive only through the symmetric mixed pairing; the base operator `s.g⁻¹` twists the
jet — the second-order source of the `S`-operators in a boundary block. -/
theorem heisConjR_of_trivial (p s : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    conjR p s = ⟨s.g⁻¹ • p.a, s.g⁻¹ • p.l, p.z + s.l p.a + p.l s.a, conjR p.g s.g⟩ := by
  rw [conjR]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · simp only [HeisLift.mul_a, HeisLift.inv_a, HeisLift.mul_g, HeisLift.inv_g, mul_smul, hp]
    abel
  · simp only [HeisLift.mul_l, HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul,
      smul_elemDual_of_trivial hp]
    abel
  · simp only [HeisLift.mul_z, HeisLift.mul_l, HeisLift.inv_z,
      HeisLift.inv_l, HeisLift.mul_g, HeisLift.inv_g, mul_smul, hp]
    simp only [ElemDual.add_apply, ElemDual.neg_apply, ElemDual.smul_apply,
      inv_inv, smul_inv_smul]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, zero_add]
    rw [sub_eq_add_neg, CharTwo.neg_eq]
  · simp only [HeisLift.mul_g, HeisLift.inv_g]
    rfl

end TrivialBase

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

/-! ### The remaining constructor rules

The same definitional facts as `heisEvalZ_gen`/`_mul`/`_inv`, one per remaining `PWord`
constructor, so that factor-by-factor computations of a branch word's second-order row stay
`rw`-driven. -/

theorem heisEvalZ_one : heisEvalZ μ x y E E₂ .one = 1 := rfl

theorem heisEvalZ_conj (u g : PWord X) :
    heisEvalZ μ x y E E₂ (.conj u g)
      = conjR (heisEvalZ μ x y E E₂ u) (heisEvalZ μ x y E E₂ g) := rfl

theorem heisEvalZ_comm (u v : PWord X) :
    heisEvalZ μ x y E E₂ (.comm u v)
      = commR (heisEvalZ μ x y E E₂ u) (heisEvalZ μ x y E E₂ v) := rfl

theorem heisEvalZ_zpow (u : PWord X) (k : ℤ) :
    heisEvalZ μ x y E E₂ (.zpow u k) = heisEvalZ μ x y E E₂ u ^ k := rfl

theorem heisEvalZ_profPow (u : PWord X) (γ : Zhat) :
    heisEvalZ μ x y E E₂ (.profPow u γ) = heisEvalZ μ x y E E₂ u ^ E γ := rfl

theorem heisEvalZ_prodList (l : List (PWord X)) :
    heisEvalZ μ x y E E₂ (PWord.prodList l) = (l.map (heisEvalZ μ x y E E₂)).prod :=
  PWord.evalZ_prodList _ _ _ l

/-- Products of jet-zero denotations are jet-zero with **additive** central coordinate —
the "⊕" of the second-order block structure, at the list level. -/
theorem heisEvalZ_prodList_jetZero {l : List (PWord X)}
    (hl : ∀ w ∈ l, heisEvalZ μ x y E E₂ w ∈ heisJetZero A C) :
    heisEvalZ μ x y E E₂ (PWord.prodList l) ∈ heisJetZero A C ∧
      (heisEvalZ μ x y E E₂ (PWord.prodList l)).z
        = (l.map fun w => (heisEvalZ μ x y E E₂ w).z).sum := by
  induction l with
  | nil => exact ⟨one_mem _, rfl⟩
  | cons w ws ih =>
      have hw := hl w List.mem_cons_self
      have ihs := ih fun u hu => hl u (List.mem_cons_of_mem _ hu)
      rw [PWord.prodList_cons]
      refine ⟨mul_mem hw ihs.1, ?_⟩
      rw [heisEvalZ_mul, heisJetZero_mul_z hw, ihs.2, List.map_cons, List.sum_cons]

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

/-! ## Coordinate identification, naturality, and the adjunction

Three inductions tying the two Heisenberg evaluations over a coefficient map together; they are
the naturality engine of the dévissage ladder. -/

section Naturality

variable {ι : Type*} {C : Type*} [Group C] {A A' : Type*} [AddCommGroup A]
  [DistribMulAction C A] [AddCommGroup A'] [DistribMulAction C A']

/-- **Coordinate identification**: the dual coordinate of the `A`-evaluation *is* the primal
coordinate of the `A^∨`-evaluation — both compute the Fox derivative with coefficients in
`A^∨` under the contragredient action. -/
theorem heisWord_l_eq_dual_a (c : ι → C) (x : ι → A) (y : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c x y) r).l
      = (FreeGroup.lift (heisGen (A := ElemDual A) c y 0) r).a := by
  refine FreeGroup.induction_on r rfl (fun i => rfl) (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · rw [map_inv, map_inv, HeisLift.inv_l, HeisLift.inv_a, heisWord_g, heisWord_g, ih]
  · rw [map_mul, map_mul, HeisLift.mul_l, HeisLift.mul_a, heisWord_g, heisWord_g, ih₁, ih₂]

/-- **Naturality of the primal coordinate** in the coefficient module, along a `C`-equivariant
map (`GQ2.FoxH.WordLift.map`-functoriality, read on the Heisenberg `.a`-coordinate). -/
theorem heisWord_a_map (c : ι → C) (f : A' →+ A)
    (hf : ∀ (g : C) (a : A'), f (g • a) = g • f a) (x : ι → A') (y : ι → ElemDual A')
    (y' : ι → ElemDual A) (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c (fun i => f (x i)) y') r).a
      = f ((FreeGroup.lift (heisGen c x y) r).a) := by
  refine FreeGroup.induction_on r (by simp) (fun i => by simp [FreeGroup.lift_apply_of])
    (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · rw [map_inv, map_inv, HeisLift.inv_a, HeisLift.inv_a, heisWord_g, heisWord_g, ih,
      ← hf, map_neg]
  · rw [map_mul, map_mul, HeisLift.mul_a, HeisLift.mul_a, heisWord_g, heisWord_g, ih₁, ih₂,
      map_add, hf]

/-- **The adjunction aux**: over a `C`-equivariant `f : A' →+ A`, the evaluation at primal
offsets `f∘x` with dual offsets `y` (in `H(A) ⋊ C`) and the evaluation at primal offsets `x`
with dual offsets `f^∨∘y` (in `H(A') ⋊ C`) correspond coordinatewise: primal coordinates match
through `f`, dual coordinates through `f^∨ = dualMap f`, and the central coordinates are
**equal**. -/
private theorem heisWord_adjoint_aux (c : ι → C) (f : A' →+ A)
    (hf : ∀ (g : C) (a : A'), f (g • a) = g • f a) (x : ι → A') (y : ι → ElemDual A)
    (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c (fun i => f (x i)) y) r).a
        = f ((FreeGroup.lift (heisGen c x (fun i => dualMap f (y i))) r).a)
    ∧ (FreeGroup.lift (heisGen c x (fun i => dualMap f (y i))) r).l
        = dualMap f ((FreeGroup.lift (heisGen c (fun i => f (x i)) y) r).l)
    ∧ (FreeGroup.lift (heisGen c (fun i => f (x i)) y) r).z
        = (FreeGroup.lift (heisGen c x (fun i => dualMap f (y i))) r).z := by
  have hfd := dualMap_equivariant (C := C) f hf
  refine FreeGroup.induction_on r ⟨by simp, by simp, rfl⟩
    (fun i => ⟨by simp [FreeGroup.lift_apply_of], by simp [FreeGroup.lift_apply_of],
      by simp [FreeGroup.lift_apply_of]⟩)
    (fun i ih => ?_) (fun r₁ r₂ ih₁ ih₂ => ?_)
  · obtain ⟨iha, ihl, ihz⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · rw [map_inv, map_inv, HeisLift.inv_a, HeisLift.inv_a, heisWord_g, heisWord_g, iha,
        ← hf, map_neg]
    · rw [map_inv, map_inv, HeisLift.inv_l, HeisLift.inv_l, heisWord_g, heisWord_g, ihl,
        ← hfd, map_neg]
    · rw [map_inv, map_inv, HeisLift.inv_z, HeisLift.inv_z, ihz, iha, ihl, dualMap_apply]
  · obtain ⟨iha₁, ihl₁, ihz₁⟩ := ih₁
    obtain ⟨iha₂, ihl₂, ihz₂⟩ := ih₂
    refine ⟨?_, ?_, ?_⟩
    · rw [map_mul, map_mul, HeisLift.mul_a, HeisLift.mul_a, heisWord_g, heisWord_g, iha₁,
        iha₂, map_add, hf]
    · rw [map_mul, map_mul, HeisLift.mul_l, HeisLift.mul_l, heisWord_g, heisWord_g, ihl₁,
        ihl₂, map_add, hfd]
    · rw [map_mul, map_mul, HeisLift.mul_z, HeisLift.mul_z, ihz₁, ihz₂, heisWord_g,
        heisWord_g, iha₂, ihl₁, ← hf, dualMap_apply]

/-- **The Stokes adjunction**: moving the coefficient map from the primal to the dual offsets
does not change the central coordinate — `β_r(f∘x, y) = β_r(x, f^∨∘y)`.  This is the
naturality square of the middle chain-map component. -/
theorem heisWord_z_adjoint (c : ι → C) (f : A' →+ A)
    (hf : ∀ (g : C) (a : A'), f (g • a) = g • f a) (x : ι → A') (y : ι → ElemDual A)
    (r : FreeGroup ι) :
    (FreeGroup.lift (heisGen c (fun i => f (x i)) y) r).z
      = (FreeGroup.lift (heisGen c x (fun i => dualMap f (y i))) r).z :=
  (heisWord_adjoint_aux c f hf x y r).2.2

end Naturality

/-! ## The generic word complex and the chain map `η`

For a lower marking `c : ι → C` satisfying a relator family `w : ρ → FreeGroup ι`, the word
complex `C•(A)` is the three-term complex

  `A --heisD0--> (ι → A) --heisD1--> (ρ → A)`

(packet displays (30)/(31), degree-generic), and the chain map of packet Lem. 5.1

  `η_A : C•(A) → Hom(C•(A^∨), 𝔽₂)[−2]`

has components `heisEta0/1/2` — evaluation pairings at the ends, the **traced Stokes pairing**
`Σ_k β_{w k}(x, y)` in the middle.  The chain conditions are the two Lemma 5.7 forms summed
over the family; the ε-corrections cancel exactly under the **endpoint condition**
(`IsStokesEndpoint`), the degree-`n` form of the `ℚ₂` chain's
`expMod2_tame_add_wildValueExpR_odd`. -/

section WordComplex

variable {ι ρ : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A]

/-- **`d⁰`**: simultaneous infinitesimal conjugation `v ↦ ((cᵢ − 1)v)ᵢ`. -/
def heisD0 (c : ι → C) : A →+ (ι → A) :=
  AddMonoidHom.mk' (fun v i => c i • v - v) (by
    intro v v'
    funext i
    simp only [smul_add, Pi.add_apply]
    abel)

@[simp] theorem heisD0_apply (c : ι → C) (v : A) (i : ι) :
    heisD0 c v i = c i • v - v := rfl

/-- **`d¹`**: the evaluated first-derivative (Fox) row of the relator family — the
`.a`-coordinate of the Heisenberg evaluation at primal offsets `x`. -/
noncomputable def heisD1 (c : ι → C) (w : ρ → FreeGroup ι) : (ι → A) →+ (ρ → A) :=
  AddMonoidHom.mk'
    (fun x k => (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (w k)).a)
    (by
      intro x x'
      funext k
      exact heisWord_a_add c x x' (0 : ι → ElemDual A) (w k))

@[simp] theorem heisD1_apply (c : ι → C) (w : ρ → FreeGroup ι) (x : ι → A) (k : ρ) :
    heisD1 c w x k = (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (w k)).a := rfl

/-- The zero-offset evaluation of a dying relator is the identity of the Heisenberg lift. -/
private theorem lift_heisGen_zero_zero (c : ι → C) {r : FreeGroup ι}
    (hr : FreeGroup.lift c r = 1) :
    FreeGroup.lift (heisGen c (0 : ι → A) (0 : ι → ElemDual A)) r = 1 := by
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · exact (heisWord_zero_prim c (0 : ι → ElemDual A) r).1
  · exact (heisWord_zero_dual c (0 : ι → A) r).1
  · exact (heisWord_zero_prim c (0 : ι → ElemDual A) r).2
  · rw [heisWord_g]; exact hr

/-- **The word complex is a complex**: `d¹ ∘ d⁰ = 0` at a marking killing the relator family.
Proof by the conjugation model: the coboundary-offset marking is the `conjPa`-conjugate of the
zero-offset marking, whose evaluation is `1`. -/
theorem heisD1_comp_heisD0 (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (v : A) :
    heisD1 (A := A) c w (heisD0 c v) = 0 := by
  have hconj : FreeGroup.lift (heisGen c (fun i => c i • v - v) (0 : ι → ElemDual A))
      = (conjPa v).comp (FreeGroup.lift (heisGen c (0 : ι → A) (0 : ι → ElemDual A))) := by
    apply FreeGroup.ext_hom
    intro i
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of, FreeGroup.lift_apply_of]
    show (⟨c i • v - v, 0, 0, c i⟩ : HeisLift A C)
      = (⟨v, 0, 0, 1⟩ : HeisLift A C)⁻¹ * ⟨0, 0, 0, c i⟩ * ⟨v, 0, 0, 1⟩
    rw [HeisLift.conj_gen]
    ext <;> simp
  funext k
  show (FreeGroup.lift (heisGen c (fun i => c i • v - v) (0 : ι → ElemDual A)) (w k)).a = 0
  rw [hconj, MonoidHom.comp_apply, lift_heisGen_zero_zero c (hr k), map_one, HeisLift.one_a]

variable [Fintype ι] [DecidableEq ι] [Fintype ρ]

/-- **The endpoint condition** (display (40), degree-generic): the traced mod-2 exponent
vector of the relator family vanishes in every generator slot.  For the `ℚ₂` pair
`(r_t, r_R)` this is the frozen `GQ2.FoxH.expMod2_tame_add_wildValueExpR_odd`; each branch
family discharges it by `decide` on the resolved words. -/
def IsStokesEndpoint (w : ρ → FreeGroup ι) : Prop :=
  ∀ i : ι, ∑ k, Multiplicative.toAdd (heisEps i (w k)) = 0

/-- **`η⁰`**: the evaluation pairing `a ↦ (ξ ↦ Σ_k ξ_k(a))` into the dual of the top dual
term. -/
noncomputable def heisEta0 : A →+ ElemDual (ρ → ElemDual A) :=
  AddMonoidHom.mk'
    (fun a => (AddMonoidHom.mk' (fun ξ : ρ → ElemDual A => ∑ k, ξ k a)
      (fun ξ ξ' => by
        simp only [Pi.add_apply, ElemDual.add_apply]
        exact Finset.sum_add_distrib) : ElemDual (ρ → ElemDual A)))
    (fun a a' => by
      ext ξ
      show (∑ k, ξ k (a + a')) = (∑ k, ξ k a) + ∑ k, ξ k a'
      simp only [map_add]
      exact Finset.sum_add_distrib)

@[simp] theorem heisEta0_apply (a : A) (ξ : ρ → ElemDual A) :
    heisEta0 a ξ = ∑ k, ξ k a := rfl

/-- **`η¹`, the traced Stokes pairing**: `x ↦ (y ↦ Σ_k β_{w k}(x, y))` — the degree-generic
form of the `ℚ₂` traced mixed coordinate `GQ2.FoxH.mixedB`. -/
noncomputable def heisEta1 (c : ι → C) (w : ρ → FreeGroup ι) :
    (ι → A) →+ ElemDual (ι → ElemDual A) :=
  AddMonoidHom.mk'
    (fun x => (AddMonoidHom.mk'
      (fun y : ι → ElemDual A => ∑ k, (FreeGroup.lift (heisGen c x y) (w k)).z)
      (fun y y' => by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun k _ => heisWord_z_add_right c x y y' (w k)) :
        ElemDual (ι → ElemDual A)))
    (fun x x' => by
      ext y
      show (∑ k, (FreeGroup.lift (heisGen c (x + x') y) (w k)).z)
        = (∑ k, (FreeGroup.lift (heisGen c x y) (w k)).z)
          + ∑ k, (FreeGroup.lift (heisGen c x' y) (w k)).z
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => heisWord_z_add_left c x x' y (w k))

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem heisEta1_apply (c : ι → C) (w : ρ → FreeGroup ι) (x : ι → A)
    (y : ι → ElemDual A) :
    heisEta1 c w x y = ∑ k, (FreeGroup.lift (heisGen c x y) (w k)).z := rfl

/-- **`η²`**: the traced biduality pairing `v ↦ (λ ↦ λ(Σ_k v_k))`. -/
noncomputable def heisEta2 : (ρ → A) →+ ElemDual (ElemDual A) :=
  AddMonoidHom.mk'
    (fun v => (AddMonoidHom.mk' (fun lam : ElemDual A => lam (∑ k, v k))
      (fun lam mu => rfl) : ElemDual (ElemDual A)))
    (fun v v' => by
      ext lam
      show lam (∑ k, (v + v') k) = lam (∑ k, v k) + lam (∑ k, v' k)
      simp only [Pi.add_apply]
      rw [Finset.sum_add_distrib, map_add])

@[simp] theorem heisEta2_apply (v : ρ → A) (lam : ElemDual A) :
    heisEta2 v lam = lam (∑ k, v k) := rfl

/-- **The first chain condition** (Lemma 5.7 left, traced): under the endpoint condition,
`η¹(d⁰a) = η⁰(a) ∘ d¹_{A^∨}` — the ε-corrections of the family cancel. -/
theorem heisEta1_comp_d0 (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) (a : A)
    (y : ι → ElemDual A) :
    heisEta1 c w (heisD0 c a) y = heisEta0 a (heisD1 (A := ElemDual A) c w y) := by
  show (∑ k, (FreeGroup.lift (heisGen c (fun i => c i • a - a) y) (w k)).z)
    = ∑ k, (FreeGroup.lift (heisGen (A := ElemDual A) c y 0) (w k)).a a
  have h57 : ∀ k, (FreeGroup.lift (heisGen c (fun i => c i • a - a) y) (w k)).z
      = (FreeGroup.lift (heisGen (A := ElemDual A) c y 0) (w k)).a a
        + ∑ i, Multiplicative.toAdd (heisEps i (w k)) * (y i (c i • a)) := fun k => by
    rw [heisWord_lemma_5_7_left c (w k) (hr k) a y, heisWord_l_eq_dual_a]
  rw [Finset.sum_congr rfl fun k _ => h57 k, Finset.sum_add_distrib, Finset.sum_comm]
  have hzero : ∀ i : ι,
      (∑ k, Multiplicative.toAdd (heisEps i (w k)) * (y i (c i • a))) = 0 := fun i => by
    rw [← Finset.sum_mul, hend i, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero, add_zero]

/-- **The second chain condition** (Lemma 5.7 right, traced): under the endpoint condition,
`η²(d¹x) = η¹(x) ∘ d⁰_{A^∨}`. -/
theorem heisEta2_comp_d1 (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) (x : ι → A)
    (lam : ElemDual A) :
    heisEta2 (heisD1 c w x) lam = heisEta1 c w x (heisD0 (A := ElemDual A) c lam) := by
  show lam (∑ k, (FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (w k)).a)
    = ∑ k, (FreeGroup.lift (heisGen c x (fun i => c i • lam - lam)) (w k)).z
  have h57 : ∀ k, (FreeGroup.lift (heisGen c x (fun i => c i • lam - lam)) (w k)).z
      = lam ((FreeGroup.lift (heisGen c x (0 : ι → ElemDual A)) (w k)).a)
        + ∑ i, Multiplicative.toAdd (heisEps i (w k)) * (lam (x i)) := fun k =>
    heisWord_lemma_5_7_right c (w k) (hr k) x lam
  rw [Finset.sum_congr rfl fun k _ => h57 k, Finset.sum_add_distrib, Finset.sum_comm, map_sum]
  have hzero : ∀ i : ι,
      (∑ k, Multiplicative.toAdd (heisEps i (w k)) * (lam (x i))) = 0 := fun i => by
    rw [← Finset.sum_mul, hend i, zero_mul]
  rw [Finset.sum_congr rfl fun i _ => hzero i, Finset.sum_const_zero, add_zero]

end WordComplex

/-! ## The mapping-cone engine (packet Lem. 5.1, `lem:composition`)

Pure additive homological algebra for **three-term complexes** `X₀ → X₁ → X₂`, done once and
generically: the frozen `ℚ₂` development hand-rolled this against the fixed word complex
(`GQ2/Devissage/*`, cloned per word); the branch lanes instantiate this engine instead.

* `StokesQuasiIso` — quasi-isomorphism of a ladder in **relative (quotient-free) form**: six
  clauses, equivalent to bijectivity of `H⁰(φ), H¹(φ), H²(φ)` but phrased without quotient
  types.
* `stokesConeDm/D0/D1` — the mapping cone of the ladder, a four-term complex
  `X₀ → X₁ × Y₀ → X₂ × Y₁ → Y₂` (cochain convention `d(x, y) = (−dx, φx + dy)`).
* `StokesConeAcyclic` and the equivalence `stokesQuasiIso_iff_coneAcyclic` — the packet's
  "equivalently, the mapping cones" clause.
* `stokes_chase`/`stokes_chase_left`/`stokes_chase_right` — the exactness chases, and
  `stokes_coneAcyclic_of_ses` — acyclicity propagates along a degreewise short exact sequence
  of four-term complexes.  **No dimension count appears anywhere** (packet warning). -/

section ConeEngine

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Type*}
  [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]

/-- **Relative (quotient-free) quasi-isomorphism** of a ladder
`(φ₀, φ₁, φ₂) : (X₀ → X₁ → X₂) ⟶ (Y₀ → Y₁ → Y₂)` of three-term complexes: injectivity and
surjectivity of the three induced cohomology maps, phrased on representatives.  (`h0_inj` says
`H⁰(φ)` is injective, `h1_surj` that every `Y`-1-cocycle is a `φ`-image of an `X`-1-cocycle up
to a coboundary, and so on.) -/
structure StokesQuasiIso (dX₀ : X₀ →+ X₁) (dX₁ : X₁ →+ X₂) (dY₀ : Y₀ →+ Y₁) (dY₁ : Y₁ →+ Y₂)
    (φ₀ : X₀ →+ Y₀) (φ₁ : X₁ →+ Y₁) (φ₂ : X₂ →+ Y₂) : Prop where
  h0_inj : ∀ x₀, dX₀ x₀ = 0 → φ₀ x₀ = 0 → x₀ = 0
  h0_surj : ∀ y₀, dY₀ y₀ = 0 → ∃ x₀, dX₀ x₀ = 0 ∧ φ₀ x₀ = y₀
  h1_inj : ∀ x₁, dX₁ x₁ = 0 → (∃ y₀, dY₀ y₀ = φ₁ x₁) → ∃ x₀, dX₀ x₀ = x₁
  h1_surj : ∀ y₁, dY₁ y₁ = 0 → ∃ x₁ y₀, dX₁ x₁ = 0 ∧ φ₁ x₁ + dY₀ y₀ = y₁
  h2_inj : ∀ x₂, (∃ y₁, dY₁ y₁ = φ₂ x₂) → ∃ x₁, dX₁ x₁ = x₂
  h2_surj : ∀ y₂, ∃ x₂ y₁, φ₂ x₂ + dY₁ y₁ = y₂

/-- The cone differential in degree `−1`: `v ↦ (−d v, φ v)`. -/
def stokesConeDm (dX₀ : X₀ →+ X₁) (φ₀ : X₀ →+ Y₀) : X₀ →+ X₁ × Y₀ :=
  (-dX₀).prod φ₀

@[simp] theorem stokesConeDm_apply (dX₀ : X₀ →+ X₁) (φ₀ : X₀ →+ Y₀) (v : X₀) :
    stokesConeDm dX₀ φ₀ v = (-dX₀ v, φ₀ v) := rfl

/-- The cone differential in degree `0`: `(x, y) ↦ (−d x, φ x + d y)`. -/
def stokesConeD0 (dX₁ : X₁ →+ X₂) (dY₀ : Y₀ →+ Y₁) (φ₁ : X₁ →+ Y₁) : X₁ × Y₀ →+ X₂ × Y₁ :=
  ((-dX₁).comp (AddMonoidHom.fst X₁ Y₀)).prod
    ((φ₁.comp (AddMonoidHom.fst X₁ Y₀)) + (dY₀.comp (AddMonoidHom.snd X₁ Y₀)))

@[simp] theorem stokesConeD0_apply (dX₁ : X₁ →+ X₂) (dY₀ : Y₀ →+ Y₁) (φ₁ : X₁ →+ Y₁)
    (p : X₁ × Y₀) : stokesConeD0 dX₁ dY₀ φ₁ p = (-dX₁ p.1, φ₁ p.1 + dY₀ p.2) := rfl

/-- The cone differential in degree `1`: `(x, y) ↦ φ x + d y`. -/
def stokesConeD1 (dY₁ : Y₁ →+ Y₂) (φ₂ : X₂ →+ Y₂) : X₂ × Y₁ →+ Y₂ :=
  (φ₂.comp (AddMonoidHom.fst X₂ Y₁)) + (dY₁.comp (AddMonoidHom.snd X₂ Y₁))

@[simp] theorem stokesConeD1_apply (dY₁ : Y₁ →+ Y₂) (φ₂ : X₂ →+ Y₂) (q : X₂ × Y₁) :
    stokesConeD1 dY₁ φ₂ q = φ₂ q.1 + dY₁ q.2 := rfl

/-- The cone is a complex in low degree (from the first ladder square). -/
theorem stokesConeD0_comp_Dm (dX₀ : X₀ →+ X₁) (dX₁ : X₁ →+ X₂) (dY₀ : Y₀ →+ Y₁)
    (φ₀ : X₀ →+ Y₀) (φ₁ : X₁ →+ Y₁) (hdX : ∀ v, dX₁ (dX₀ v) = 0)
    (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v)) (v : X₀) :
    stokesConeD0 dX₁ dY₀ φ₁ (stokesConeDm dX₀ φ₀ v) = 0 := by
  show (-dX₁ (-dX₀ v), φ₁ (-dX₀ v) + dY₀ (φ₀ v)) = 0
  rw [Prod.mk_eq_zero]
  constructor
  · rw [map_neg, hdX, neg_zero, neg_zero]
  · rw [map_neg, hφ₀, neg_add_cancel]

/-- The cone is a complex in top degree (from the second ladder square). -/
theorem stokesConeD1_comp_D0 (dX₁ : X₁ →+ X₂) (dY₀ : Y₀ →+ Y₁) (dY₁ : Y₁ →+ Y₂)
    (φ₁ : X₁ →+ Y₁) (φ₂ : X₂ →+ Y₂) (hdY : ∀ y, dY₁ (dY₀ y) = 0)
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) (p : X₁ × Y₀) :
    stokesConeD1 dY₁ φ₂ (stokesConeD0 dX₁ dY₀ φ₁ p) = 0 := by
  show φ₂ (-dX₁ p.1) + dY₁ (φ₁ p.1 + dY₀ p.2) = 0
  rw [map_neg, map_add, hdY, hφ₁, add_zero, neg_add_cancel]

/-- **Acyclicity of the mapping cone**: exactness at all four spots of
`0 → X₀ → X₁ × Y₀ → X₂ × Y₁ → Y₂ → 0`. -/
structure StokesConeAcyclic (dX₀ : X₀ →+ X₁) (dX₁ : X₁ →+ X₂) (dY₀ : Y₀ →+ Y₁)
    (dY₁ : Y₁ →+ Y₂) (φ₀ : X₀ →+ Y₀) (φ₁ : X₁ →+ Y₁) (φ₂ : X₂ →+ Y₂) : Prop where
  inj : ∀ v, stokesConeDm dX₀ φ₀ v = 0 → v = 0
  ex0 : ∀ p, stokesConeD0 dX₁ dY₀ φ₁ p = 0 → ∃ v, stokesConeDm dX₀ φ₀ v = p
  ex1 : ∀ q, stokesConeD1 dY₁ φ₂ q = 0 → ∃ p, stokesConeD0 dX₁ dY₀ φ₁ p = q
  surj : ∀ y₂, ∃ q, stokesConeD1 dY₁ φ₂ q = y₂

variable {dX₀ : X₀ →+ X₁} {dX₁ : X₁ →+ X₂} {dY₀ : Y₀ →+ Y₁} {dY₁ : Y₁ →+ Y₂}
  {φ₀ : X₀ →+ Y₀} {φ₁ : X₁ →+ Y₁} {φ₂ : X₂ →+ Y₂}

/-- Quasi-isomorphism implies cone acyclicity (needs the ladder squares). -/
theorem StokesQuasiIso.coneAcyclic (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v))
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x))
    (h : StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂) :
    StokesConeAcyclic dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ := by
  constructor
  · intro v hv
    rw [stokesConeDm_apply, Prod.mk_eq_zero, neg_eq_zero] at hv
    exact h.h0_inj v hv.1 hv.2
  · rintro ⟨x₁, y₀⟩ hp
    rw [stokesConeD0_apply, Prod.mk_eq_zero, neg_eq_zero] at hp
    obtain ⟨hx₁, hsum⟩ := hp
    have hy : dY₀ (-y₀) = φ₁ x₁ := by
      rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]
      exact hsum
    obtain ⟨v, hv⟩ := h.h1_inj x₁ hx₁ ⟨-y₀, hy⟩
    -- correct the `Y₀`-slot inside the `d⁰`-fibre
    have hw : dY₀ (y₀ + φ₀ v) = 0 := by
      rw [map_add, hφ₀, hv, ← hy, map_neg]
      abel
    obtain ⟨u, hu0, huw⟩ := h.h0_surj (y₀ + φ₀ v) hw
    refine ⟨u - v, ?_⟩
    show (-dX₀ (u - v), φ₀ (u - v)) = (x₁, y₀)
    rw [Prod.mk.injEq]
    constructor
    · rw [map_sub, hu0, hv, zero_sub, neg_neg]
    · rw [map_sub, huw]
      abel
  · rintro ⟨x₂, y₁⟩ hq
    rw [stokesConeD1_apply] at hq
    have hy : dY₁ (-y₁) = φ₂ x₂ := by
      rw [map_neg, neg_eq_iff_add_eq_zero, add_comm]
      exact hq
    obtain ⟨x₁, hx₁⟩ := h.h2_inj x₂ ⟨-y₁, hy⟩
    have hker : dY₁ (y₁ + φ₁ x₁) = 0 := by
      rw [map_add, hφ₁, hx₁, ← hy, map_neg]
      abel
    obtain ⟨x₁', y₀, hx₁', hsum⟩ := h.h1_surj (y₁ + φ₁ x₁) hker
    refine ⟨(x₁' - x₁, y₀), ?_⟩
    show (-dX₁ (x₁' - x₁), φ₁ (x₁' - x₁) + dY₀ y₀) = (x₂, y₁)
    rw [Prod.mk.injEq]
    constructor
    · rw [map_sub, hx₁', hx₁, zero_sub, neg_neg]
    · rw [map_sub, sub_add_eq_add_sub, hsum]
      abel
  · intro y₂
    obtain ⟨x₂, y₁, hq⟩ := h.h2_surj y₂
    exact ⟨(x₂, y₁), hq⟩

/-- Cone acyclicity implies quasi-isomorphism (no hypotheses needed). -/
theorem StokesConeAcyclic.quasiIso (h : StokesConeAcyclic dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂) :
    StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ := by
  constructor
  · intro x₀ hd hφ
    refine h.inj x₀ ?_
    show (-dX₀ x₀, φ₀ x₀) = 0
    rw [hd, hφ, neg_zero]
    rfl
  · intro y₀ hy
    obtain ⟨v, hv⟩ := h.ex0 (0, y₀) (by
      show (-dX₁ 0, φ₁ 0 + dY₀ y₀) = 0
      rw [map_zero, map_zero, neg_zero, zero_add, hy]
      rfl)
    have hv1 : -dX₀ v = 0 := congrArg Prod.fst hv
    have hv2 : φ₀ v = y₀ := congrArg Prod.snd hv
    exact ⟨v, by rw [← neg_eq_zero]; exact hv1, hv2⟩
  · rintro x₁ hx ⟨y₀, hy⟩
    obtain ⟨v, hv⟩ := h.ex0 (x₁, -y₀) (by
      show (-dX₁ x₁, φ₁ x₁ + dY₀ (-y₀)) = 0
      rw [hx, neg_zero, map_neg, ← hy, add_neg_cancel]
      rfl)
    have hv1 : -dX₀ v = x₁ := congrArg Prod.fst hv
    exact ⟨-v, by rw [map_neg]; exact hv1⟩
  · intro y₁ hy
    obtain ⟨p, hp⟩ := h.ex1 (0, y₁) (by
      show φ₂ 0 + dY₁ y₁ = 0
      rw [map_zero, zero_add, hy])
    have hp1 : -dX₁ p.1 = 0 := congrArg Prod.fst hp
    have hp2 : φ₁ p.1 + dY₀ p.2 = y₁ := congrArg Prod.snd hp
    exact ⟨p.1, p.2, by rw [← neg_eq_zero]; exact hp1, hp2⟩
  · rintro x₂ ⟨y₁, hy⟩
    obtain ⟨p, hp⟩ := h.ex1 (x₂, -y₁) (by
      show φ₂ x₂ + dY₁ (-y₁) = 0
      rw [map_neg, ← hy, add_neg_cancel])
    have hp1 : -dX₁ p.1 = x₂ := congrArg Prod.fst hp
    exact ⟨-p.1, by rw [map_neg]; exact hp1⟩
  · intro y₂
    obtain ⟨q, hq⟩ := h.surj y₂
    exact ⟨q.1, q.2, hq⟩

/-- **Quasi-isomorphism = cone acyclicity** — the packet's "equivalently, the mapping cones"
clause, for three-term complexes. -/
theorem stokesQuasiIso_iff_coneAcyclic (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v))
    (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x)) :
    StokesQuasiIso dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ ↔
      StokesConeAcyclic dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ :=
  ⟨fun h => h.coneAcyclic hφ₀ hφ₁, fun h => h.quasiIso⟩

end ConeEngine

/-! ### The exactness chases -/

section Chase

/-- **The dévissage chase** (interior spot): in a commuting ladder of short exact columns over
three consecutive degrees, exactness of the two outer rows at the middle degree forces
exactness of the middle row.  Only the `ker ⊆ im` half of column exactness enters. -/
theorem stokes_chase
    {K₀ K₁ K₂ L₀ L₁ L₂ M₀ M₁ M₂ : Type*}
    [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup K₂]
    [AddCommGroup L₀] [AddCommGroup L₁] [AddCommGroup L₂]
    [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    (dK : K₀ →+ K₁) (dK' : K₁ →+ K₂) (dL : L₀ →+ L₁) (dL' : L₁ →+ L₂)
    (dM : M₀ →+ M₁) (dM' : M₁ →+ M₂)
    (f₀ : K₀ →+ L₀) (f₁ : K₁ →+ L₁) (f₂ : K₂ →+ L₂)
    (g₀ : L₀ →+ M₀) (g₁ : L₁ →+ M₁) (g₂ : L₂ →+ M₂)
    (hf₀ : ∀ v, dL (f₀ v) = f₁ (dK v)) (hf₁ : ∀ v, dL' (f₁ v) = f₂ (dK' v))
    (hg₀ : ∀ y, dM (g₀ y) = g₁ (dL y)) (hg₁ : ∀ y, dM' (g₁ y) = g₂ (dL' y))
    (hf₂inj : Function.Injective f₂) (hg₀surj : Function.Surjective g₀)
    (hcol : ∀ y : L₁, g₁ y = 0 → ∃ x, f₁ x = y)
    (hdL : ∀ y, dL' (dL y) = 0)
    (hK : ∀ x : K₁, dK' x = 0 → ∃ v, dK v = x)
    (hM : ∀ z : M₁, dM' z = 0 → ∃ u, dM u = z) :
    ∀ y : L₁, dL' y = 0 → ∃ p, dL p = y := by
  intro y hy
  obtain ⟨u, hu⟩ := hM (g₁ y) (by rw [hg₁, hy, map_zero])
  obtain ⟨p₀, hp₀⟩ := hg₀surj u
  obtain ⟨x, hx⟩ := hcol (y - dL p₀) (by rw [map_sub, ← hg₀, hp₀, hu, sub_self])
  have hdx : dK' x = 0 :=
    hf₂inj (by rw [← hf₁, hx, map_sub, hy, hdL, zero_sub, neg_zero, map_zero])
  obtain ⟨v, hv⟩ := hK x hdx
  refine ⟨p₀ + f₀ v, ?_⟩
  rw [map_add, hf₀, hv, hx]
  abel

/-- The left-end chase: injectivity of the first differential propagates. -/
theorem stokes_chase_left
    {K₀ K₁ L₀ L₁ M₀ M₁ : Type*}
    [AddCommGroup K₀] [AddCommGroup K₁] [AddCommGroup L₀] [AddCommGroup L₁]
    [AddCommGroup M₀] [AddCommGroup M₁]
    (dK : K₀ →+ K₁) (dL : L₀ →+ L₁) (dM : M₀ →+ M₁)
    (f₀ : K₀ →+ L₀) (f₁ : K₁ →+ L₁) (g₀ : L₀ →+ M₀) (g₁ : L₁ →+ M₁)
    (hf₀ : ∀ v, dL (f₀ v) = f₁ (dK v)) (hg₀ : ∀ y, dM (g₀ y) = g₁ (dL y))
    (hf₁inj : Function.Injective f₁)
    (hcol : ∀ y : L₀, g₀ y = 0 → ∃ x, f₀ x = y)
    (hK : ∀ x : K₀, dK x = 0 → x = 0) (hM : ∀ z : M₀, dM z = 0 → z = 0) :
    ∀ y : L₀, dL y = 0 → y = 0 := by
  intro y hy
  obtain ⟨x, hx⟩ := hcol y (hM (g₀ y) (by rw [hg₀, hy, map_zero]))
  have hdk : dK x = 0 := hf₁inj (by rw [← hf₀, hx, hy, map_zero])
  rw [← hx, hK x hdk, map_zero]

/-- The right-end chase: surjectivity of the last differential propagates. -/
theorem stokes_chase_right
    {K₁ K₂ L₁ L₂ M₁ M₂ : Type*}
    [AddCommGroup K₁] [AddCommGroup K₂] [AddCommGroup L₁] [AddCommGroup L₂]
    [AddCommGroup M₁] [AddCommGroup M₂]
    (dK' : K₁ →+ K₂) (dL' : L₁ →+ L₂) (dM' : M₁ →+ M₂)
    (f₁ : K₁ →+ L₁) (f₂ : K₂ →+ L₂) (g₁ : L₁ →+ M₁) (g₂ : L₂ →+ M₂)
    (hf₁ : ∀ v, dL' (f₁ v) = f₂ (dK' v)) (hg₁ : ∀ y, dM' (g₁ y) = g₂ (dL' y))
    (hg₁surj : Function.Surjective g₁)
    (hcol : ∀ z : L₂, g₂ z = 0 → ∃ x, f₂ x = z)
    (hK : Function.Surjective dK') (hM : Function.Surjective dM') :
    Function.Surjective dL' := by
  intro z
  obtain ⟨m, hm⟩ := hM (g₂ z)
  obtain ⟨l, hl⟩ := hg₁surj m
  obtain ⟨x, hx⟩ := hcol (z - dL' l) (by rw [map_sub, ← hg₁, hl, hm, sub_self])
  obtain ⟨k, hk⟩ := hK x
  refine ⟨l + f₁ k, ?_⟩
  rw [map_add, hf₁, hk, hx]
  abel

end Chase

/-! ### Short exact columns, and the cone dévissage -/

section ConeSES

/-- A **short exact column**: the data consumed by the chases (injectivity, surjectivity, the
`ker ⊆ im` half of exactness) together with `im ⊆ ker` (`comp_zero`), which dualization
needs. -/
structure StokesSES {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : B →+ C) : Prop where
  inj : Function.Injective f
  surj : Function.Surjective g
  exact : ∀ b : B, g b = 0 → ∃ a, f a = b
  comp_zero : ∀ a : A, g (f a) = 0

/-- The subgroup form of exactness, recovered from the two halves. -/
theorem StokesSES.range_eq_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] {f : A →+ B} {g : B →+ C} (h : StokesSES f g) : f.range = g.ker := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    exact AddMonoidHom.mem_ker.mpr (h.comp_zero a)
  · intro hb
    obtain ⟨a, ha⟩ := h.exact b (AddMonoidHom.mem_ker.mp hb)
    exact ⟨a, ha⟩

/-- A short exact column from the subgroup form. -/
theorem stokesSES_of_range_eq_ker {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] {f : A →+ B} {g : B →+ C} (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hexact : f.range = g.ker) : StokesSES f g := by
  refine ⟨hinj, hsurj, fun b hb => ?_, fun a => ?_⟩
  · exact AddMonoidHom.mem_range.mp (hexact ▸ AddMonoidHom.mem_ker.mpr hb)
  · exact AddMonoidHom.mem_ker.mp (hexact ▸ AddMonoidHom.mem_range.mpr ⟨a, rfl⟩)

/-- Short exact columns are closed under (independent) products. -/
theorem StokesSES.prod {A B C A' B' C' : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    {f : A →+ B} {g : B →+ C} {f' : A' →+ B'} {g' : B' →+ C'}
    (h : StokesSES f g) (h' : StokesSES f' g') :
    StokesSES (f.prodMap f') (g.prodMap g') := by
  refine ⟨fun p q hpq => ?_, fun c => ?_, fun b hb => ?_, fun a => ?_⟩
  · have h1 : f p.1 = f q.1 := congrArg Prod.fst hpq
    have h2 : f' p.2 = f' q.2 := congrArg Prod.snd hpq
    exact Prod.ext (h.inj h1) (h'.inj h2)
  · obtain ⟨b, hb⟩ := h.surj c.1
    obtain ⟨b', hb'⟩ := h'.surj c.2
    exact ⟨(b, b'), Prod.ext hb hb'⟩
  · obtain ⟨a, ha⟩ := h.exact b.1 (congrArg Prod.fst hb)
    obtain ⟨a', ha'⟩ := h'.exact b.2 (congrArg Prod.snd hb)
    exact ⟨(a, a'), Prod.ext ha ha'⟩
  · exact Prod.ext (h.comp_zero a.1) (h'.comp_zero a.2)

/-- The componentwise extension of a coefficient map to `κ`-tuples. -/
def stokesPi {A B : Type*} [AddCommGroup A] [AddCommGroup B] (κ : Type*) (f : A →+ B) :
    (κ → A) →+ (κ → B) :=
  AddMonoidHom.mk' (fun x k => f (x k)) (by
    intro x x'
    funext k
    simp [map_add])

@[simp] theorem stokesPi_apply {A B : Type*} [AddCommGroup A] [AddCommGroup B] (κ : Type*)
    (f : A →+ B) (x : κ → A) (k : κ) : stokesPi κ f x k = f (x k) := rfl

/-- Short exact columns are closed under `κ`-tuples. -/
theorem StokesSES.pi {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {f : A →+ B} {g : B →+ C} (h : StokesSES f g) (κ : Type*) :
    StokesSES (stokesPi κ f) (stokesPi κ g) := by
  refine ⟨fun x x' hx => ?_, fun z => ?_, fun y hy => ?_, fun x => ?_⟩
  · funext k
    exact h.inj (congrFun hx k)
  · choose y hy using fun k => h.surj (z k)
    exact ⟨y, funext hy⟩
  · choose x hx using fun k => h.exact (y k) (congrFun hy k)
    exact ⟨x, funext hx⟩
  · funext k
    exact h.comp_zero (x k)

/-- **Dualization of a short exact column** (the elementary-dual pack, packaged): for finite
elementary modules, `A' ↪ A ↠ A''` dualizes to `A''^∨ ↪ A^∨ ↠ A'^∨`. -/
theorem StokesSES.dual {A' A A'' : Type*} [AddCommGroup A'] [AddCommGroup A]
    [AddCommGroup A''] [Finite A] [Finite A'']
    (hA₂ : ∀ a : A, a + a = 0) (hA''₂ : ∀ a : A'', a + a = 0)
    {f : A' →+ A} {g : A →+ A''} (h : StokesSES f g) :
    StokesSES (dualMap g) (dualMap f) := by
  refine ⟨dualMap_injective g h.surj, dualMap_surjective hA₂ f h.inj, fun lam h0 => ?_,
    fun mu => ?_⟩
  · exact AddMonoidHom.mem_range.mp
      ((dual_exact_pair hA''₂ f g h.range_eq_ker lam).mp h0)
  · ext a'
    show mu (g (f a')) = 0
    rw [h.comp_zero, map_zero]

variable {U₀ U₁ U₂ V₀ V₁ V₂ X₀ X₁ X₂ Y₀ Y₁ Y₂ S₀ S₁ S₂ T₀ T₁ T₂ : Type*}
  [AddCommGroup U₀] [AddCommGroup U₁] [AddCommGroup U₂]
  [AddCommGroup V₀] [AddCommGroup V₁] [AddCommGroup V₂]
  [AddCommGroup X₀] [AddCommGroup X₁] [AddCommGroup X₂]
  [AddCommGroup Y₀] [AddCommGroup Y₁] [AddCommGroup Y₂]
  [AddCommGroup S₀] [AddCommGroup S₁] [AddCommGroup S₂]
  [AddCommGroup T₀] [AddCommGroup T₁] [AddCommGroup T₂]

/-- Cone-map square in degree `−1`, from the component squares. -/
private theorem stokesCone_comm_Dm {dU₀ : U₀ →+ U₁} {dX₀ : X₀ →+ X₁} {ψ₀ : U₀ →+ V₀}
    {φ₀ : X₀ →+ Y₀} {p₀ : U₀ →+ X₀} {p₁ : U₁ →+ X₁} {r₀ : V₀ →+ Y₀}
    (hp₀ : ∀ u, dX₀ (p₀ u) = p₁ (dU₀ u)) (hn₀ : ∀ u, φ₀ (p₀ u) = r₀ (ψ₀ u)) (u : U₀) :
    stokesConeDm dX₀ φ₀ (p₀ u) = (p₁.prodMap r₀) (stokesConeDm dU₀ ψ₀ u) := by
  show (-dX₀ (p₀ u), φ₀ (p₀ u)) = (p₁ (-dU₀ u), r₀ (ψ₀ u))
  rw [Prod.mk.injEq, map_neg, hp₀, hn₀]
  exact ⟨rfl, rfl⟩

/-- Cone-map square in degree `0`. -/
private theorem stokesCone_comm_D0 {dU₁ : U₁ →+ U₂} {dV₀ : V₀ →+ V₁} {dX₁ : X₁ →+ X₂}
    {dY₀ : Y₀ →+ Y₁} {ψ₁ : U₁ →+ V₁} {φ₁ : X₁ →+ Y₁} {p₁ : U₁ →+ X₁} {p₂ : U₂ →+ X₂}
    {r₀ : V₀ →+ Y₀} {r₁ : V₁ →+ Y₁}
    (hp₁ : ∀ u, dX₁ (p₁ u) = p₂ (dU₁ u)) (hr₀ : ∀ v, dY₀ (r₀ v) = r₁ (dV₀ v))
    (hn₁ : ∀ u, φ₁ (p₁ u) = r₁ (ψ₁ u)) (pu : U₁ × V₀) :
    stokesConeD0 dX₁ dY₀ φ₁ ((p₁.prodMap r₀) pu)
      = (p₂.prodMap r₁) (stokesConeD0 dU₁ dV₀ ψ₁ pu) := by
  show (-dX₁ (p₁ pu.1), φ₁ (p₁ pu.1) + dY₀ (r₀ pu.2))
    = (p₂ (-dU₁ pu.1), r₁ (ψ₁ pu.1 + dV₀ pu.2))
  rw [Prod.mk.injEq, map_neg, hp₁, hn₁, hr₀, map_add]
  exact ⟨rfl, rfl⟩

/-- Cone-map square in degree `1`. -/
private theorem stokesCone_comm_D1 {dV₁ : V₁ →+ V₂} {dY₁ : Y₁ →+ Y₂} {ψ₂ : U₂ →+ V₂}
    {φ₂ : X₂ →+ Y₂} {p₂ : U₂ →+ X₂} {r₁ : V₁ →+ Y₁} {r₂ : V₂ →+ Y₂}
    (hr₁ : ∀ v, dY₁ (r₁ v) = r₂ (dV₁ v)) (hn₂ : ∀ u, φ₂ (p₂ u) = r₂ (ψ₂ u)) (qu : U₂ × V₁) :
    stokesConeD1 dY₁ φ₂ ((p₂.prodMap r₁) qu) = r₂ (stokesConeD1 dV₁ ψ₂ qu) := by
  show φ₂ (p₂ qu.1) + dY₁ (r₁ qu.2) = r₂ (ψ₂ qu.1 + dV₁ qu.2)
  rw [hn₂, hr₁, map_add]

/-- **The cone dévissage** (packet Lem. 5.1, induction step): given a commuting short exact
sequence of ladders — sub-ladder `(ψ)` on `(U, V)`, middle ladder `(φ)` on `(X, Y)`, quotient
ladder `(χ)` on `(S, T)` — with the two outer cones acyclic, the middle cone is acyclic.
Four applications of the exactness chases to the degreewise short exact sequence of mapping
cones; no dimension count. -/
theorem stokesConeAcyclic_of_ses
    -- the three ladders
    {dU₀ : U₀ →+ U₁} {dU₁ : U₁ →+ U₂} {dV₀ : V₀ →+ V₁} {dV₁ : V₁ →+ V₂}
    {ψ₀ : U₀ →+ V₀} {ψ₁ : U₁ →+ V₁} {ψ₂ : U₂ →+ V₂}
    {dX₀ : X₀ →+ X₁} {dX₁ : X₁ →+ X₂} {dY₀ : Y₀ →+ Y₁} {dY₁ : Y₁ →+ Y₂}
    {φ₀ : X₀ →+ Y₀} {φ₁ : X₁ →+ Y₁} {φ₂ : X₂ →+ Y₂}
    {dS₀ : S₀ →+ S₁} {dS₁ : S₁ →+ S₂} {dT₀ : T₀ →+ T₁} {dT₁ : T₁ →+ T₂}
    {χ₀ : S₀ →+ T₀} {χ₁ : S₁ →+ T₁} {χ₂ : S₂ →+ T₂}
    -- the middle ladder's squares and complex laws
    (hφ₀ : ∀ v, dY₀ (φ₀ v) = φ₁ (dX₀ v)) (hφ₁ : ∀ x, dY₁ (φ₁ x) = φ₂ (dX₁ x))
    (hdX : ∀ v, dX₁ (dX₀ v) = 0) (hdY : ∀ y, dY₁ (dY₀ y) = 0)
    -- the columns
    {p₀ : U₀ →+ X₀} {p₁ : U₁ →+ X₁} {p₂ : U₂ →+ X₂}
    {q₀ : X₀ →+ S₀} {q₁ : X₁ →+ S₁} {q₂ : X₂ →+ S₂}
    {r₀ : V₀ →+ Y₀} {r₁ : V₁ →+ Y₁} {r₂ : V₂ →+ Y₂}
    {s₀ : Y₀ →+ T₀} {s₁ : Y₁ →+ T₁} {s₂ : Y₂ →+ T₂}
    (hS₀ : StokesSES p₀ q₀) (hS₁ : StokesSES p₁ q₁) (hS₂ : StokesSES p₂ q₂)
    (hT₀ : StokesSES r₀ s₀) (hT₁ : StokesSES r₁ s₁) (hT₂ : StokesSES r₂ s₂)
    -- commutation of columns with the differentials
    (hp₀ : ∀ u, dX₀ (p₀ u) = p₁ (dU₀ u)) (hp₁ : ∀ u, dX₁ (p₁ u) = p₂ (dU₁ u))
    (hq₀ : ∀ x, dS₀ (q₀ x) = q₁ (dX₀ x)) (hq₁ : ∀ x, dS₁ (q₁ x) = q₂ (dX₁ x))
    (hr₀ : ∀ v, dY₀ (r₀ v) = r₁ (dV₀ v)) (hr₁ : ∀ v, dY₁ (r₁ v) = r₂ (dV₁ v))
    (hs₀ : ∀ y, dT₀ (s₀ y) = s₁ (dY₀ y)) (hs₁ : ∀ y, dT₁ (s₁ y) = s₂ (dY₁ y))
    -- naturality of the ladders in the columns
    (hn₀ : ∀ u, φ₀ (p₀ u) = r₀ (ψ₀ u)) (hn₁ : ∀ u, φ₁ (p₁ u) = r₁ (ψ₁ u))
    (hn₂ : ∀ u, φ₂ (p₂ u) = r₂ (ψ₂ u))
    (hm₀ : ∀ x, χ₀ (q₀ x) = s₀ (φ₀ x)) (hm₁ : ∀ x, χ₁ (q₁ x) = s₁ (φ₁ x))
    (hm₂ : ∀ x, χ₂ (q₂ x) = s₂ (φ₂ x))
    -- the outer cones are acyclic
    (hA' : StokesConeAcyclic dU₀ dU₁ dV₀ dV₁ ψ₀ ψ₁ ψ₂)
    (hA'' : StokesConeAcyclic dS₀ dS₁ dT₀ dT₁ χ₀ χ₁ χ₂) :
    StokesConeAcyclic dX₀ dX₁ dY₀ dY₁ φ₀ φ₁ φ₂ := by
  constructor
  · -- exactness at degree `−1`: the left-end chase
    exact stokes_chase_left (stokesConeDm dU₀ ψ₀) (stokesConeDm dX₀ φ₀)
      (stokesConeDm dS₀ χ₀) p₀ (p₁.prodMap r₀) q₀ (q₁.prodMap s₀)
      (stokesCone_comm_Dm hp₀ hn₀) (stokesCone_comm_Dm hq₀ hm₀)
      ((hS₁.prod hT₀).inj) hS₀.exact hA'.inj hA''.inj
  · -- exactness at degree `0`: the interior chase
    exact stokes_chase (stokesConeDm dU₀ ψ₀) (stokesConeD0 dU₁ dV₀ ψ₁)
      (stokesConeDm dX₀ φ₀) (stokesConeD0 dX₁ dY₀ φ₁)
      (stokesConeDm dS₀ χ₀) (stokesConeD0 dS₁ dT₀ χ₁)
      p₀ (p₁.prodMap r₀) (p₂.prodMap r₁) q₀ (q₁.prodMap s₀) (q₂.prodMap s₁)
      (stokesCone_comm_Dm hp₀ hn₀) (stokesCone_comm_D0 hp₁ hr₀ hn₁)
      (stokesCone_comm_Dm hq₀ hm₀) (stokesCone_comm_D0 hq₁ hs₀ hm₁)
      ((hS₂.prod hT₁).inj) hS₀.surj (hS₁.prod hT₀).exact
      (stokesConeD0_comp_Dm dX₀ dX₁ dY₀ φ₀ φ₁ hdX hφ₀)
      hA'.ex0 hA''.ex0
  · -- exactness at degree `1`: the interior chase, one degree up
    exact stokes_chase (stokesConeD0 dU₁ dV₀ ψ₁) (stokesConeD1 dV₁ ψ₂)
      (stokesConeD0 dX₁ dY₀ φ₁) (stokesConeD1 dY₁ φ₂)
      (stokesConeD0 dS₁ dT₀ χ₁) (stokesConeD1 dT₁ χ₂)
      (p₁.prodMap r₀) (p₂.prodMap r₁) r₂ (q₁.prodMap s₀) (q₂.prodMap s₁) s₂
      (stokesCone_comm_D0 hp₁ hr₀ hn₁) (stokesCone_comm_D1 hr₁ hn₂)
      (stokesCone_comm_D0 hq₁ hs₀ hm₁) (stokesCone_comm_D1 hs₁ hm₂)
      hT₂.inj (hS₁.prod hT₀).surj (hS₂.prod hT₁).exact
      (stokesConeD1_comp_D0 dX₁ dY₀ dY₁ φ₁ φ₂ hdY hφ₁)
      hA'.ex1 hA''.ex1
  · -- surjectivity at the top: the right-end chase
    exact stokes_chase_right (stokesConeD1 dV₁ ψ₂) (stokesConeD1 dY₁ φ₂)
      (stokesConeD1 dT₁ χ₂) (p₂.prodMap r₁) r₂ (q₂.prodMap s₁) s₂
      (stokesCone_comm_D1 hr₁ hn₂) (stokesCone_comm_D1 hs₁ hm₂)
      (hS₂.prod hT₁).surj hT₂.exact hA'.surj hA''.surj

end ConeSES

/-! ## The Stokes duality ladder and packet Lem. 5.1

The chain map `η_A` assembles into a ladder from the word complex `C•(A)` to the shifted dual
complex `Hom(C•(A^∨), 𝔽₂)[−2]`, whose differentials are the `dualMap`s of the word complex
over `A^∨`.  `StokesDuality c w A` says the ladder is a quasi-isomorphism — the conclusion of
packet Lem. 5.1, and the generic content of the `StokesDualityCertificate` clause.

`stokesDuality_of_simple` is **packet Lem. 5.1**: quasi-isomorphism for every simple module
(plus the zero module, automatic) extends to every finite elementary module — including
nonsplit ones — by strong induction on the cardinality along the composition series, the
induction step being the cone dévissage `stokesConeAcyclic_of_ses`. -/

section DualityLadder

variable {ι ρ : Type*} {C : Type*} [Group C] {A A' : Type*} [AddCommGroup A]
  [DistribMulAction C A] [AddCommGroup A'] [DistribMulAction C A']

/-- Naturality of `d⁰` in the coefficient module. -/
theorem heisD0_map (c : ι → C) (f : A' →+ A)
    (hf : ∀ (g : C) (a : A'), f (g • a) = g • f a) (v : A') :
    heisD0 c (f v) = stokesPi ι f (heisD0 c v) := by
  funext i
  show c i • f v - f v = f (c i • v - v)
  rw [map_sub, hf]

/-- Naturality of `d¹` in the coefficient module. -/
theorem heisD1_map (c : ι → C) (w : ρ → FreeGroup ι) (f : A' →+ A)
    (hf : ∀ (g : C) (a : A'), f (g • a) = g • f a) (x : ι → A') :
    heisD1 c w (stokesPi ι f x) = stokesPi ρ f (heisD1 c w x) := by
  funext k
  show (FreeGroup.lift (heisGen c (fun i => f (x i)) (0 : ι → ElemDual A)) (w k)).a
    = f ((FreeGroup.lift (heisGen c x (0 : ι → ElemDual A')) (w k)).a)
  exact heisWord_a_map c f hf x 0 0 (w k)

variable [Fintype ρ]

/-- **The Stokes duality ladder is a quasi-isomorphism** — the conclusion of packet Lem. 5.1
for the module `A`, and the generic content of the `StokesDualityCertificate` clause.  The
source is the word complex `A → (ι → A) → (ρ → A)`; the target is the `𝔽₂`-dual of the word
complex of `A^∨`, read backwards; the ladder is `η = (heisEta0, heisEta1, heisEta2)`. -/
def StokesDuality (c : ι → C) (w : ρ → FreeGroup ι) (A : Type*) [AddCommGroup A]
    [DistribMulAction C A] : Prop :=
  StokesQuasiIso (heisD0 (A := A) c) (heisD1 c w)
    (dualMap (heisD1 (A := ElemDual A) c w)) (dualMap (heisD0 (A := ElemDual A) c))
    heisEta0 (heisEta1 c w) heisEta2

variable [Fintype ι] [DecidableEq ι]

/-- The first ladder square, bundled: `η` commutes with the degree-`0` differentials. -/
theorem stokes_square₀ (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) (a : A) :
    dualMap (heisD1 (A := ElemDual A) c w) (heisEta0 a) = heisEta1 c w (heisD0 c a) :=
  ElemDual.ext fun y => (heisEta1_comp_d0 c w hr hend a y).symm

/-- The second ladder square, bundled: `η` commutes with the degree-`1` differentials. -/
theorem stokes_square₁ (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) (x : ι → A) :
    dualMap (heisD0 (A := ElemDual A) c) (heisEta1 c w x) = heisEta2 (heisD1 c w x) :=
  ElemDual.ext fun lam => (heisEta2_comp_d1 c w hr hend x lam).symm

omit [Fintype ι] [DecidableEq ι] [Fintype ρ] in
/-- The target complex is a complex (the dual of `d¹ ∘ d⁰ = 0` over `A^∨`). -/
theorem stokes_dual_comp (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (yc : ElemDual (ρ → ElemDual A)) :
    dualMap (heisD0 (A := ElemDual A) c) (dualMap (heisD1 (A := ElemDual A) c w) yc) = 0 :=
  ElemDual.ext fun lam => by
    show yc (heisD1 (A := ElemDual A) c w (heisD0 c lam)) = 0
    rw [heisD1_comp_heisD0 c w hr lam, map_zero]

omit [Fintype ι] [DecidableEq ι] in
/-- The zero module satisfies Stokes duality (both complexes collapse). -/
theorem stokesDuality_of_subsingleton (c : ι → C) (w : ρ → FreeGroup ι) [Subsingleton A] :
    StokesDuality c w A := by
  have hd : Subsingleton (ElemDual A) :=
    ⟨fun lam mu => ElemDual.ext fun a => by rw [Subsingleton.elim a 0, map_zero, map_zero]⟩
  have hd0 : Subsingleton (ElemDual (ρ → ElemDual A)) :=
    ⟨fun lam mu => ElemDual.ext fun ξ => by
      rw [Subsingleton.elim ξ 0, map_zero, map_zero]⟩
  have hd1 : Subsingleton (ElemDual (ι → ElemDual A)) :=
    ⟨fun lam mu => ElemDual.ext fun y => by
      rw [Subsingleton.elim y 0, map_zero, map_zero]⟩
  have hd2 : Subsingleton (ElemDual (ElemDual A)) :=
    ⟨fun lam mu => ElemDual.ext fun l => by rw [Subsingleton.elim l 0, map_zero, map_zero]⟩
  constructor
  · intro x₀ _ _
    exact Subsingleton.elim x₀ 0
  · intro y₀ _
    exact ⟨0, map_zero _, Subsingleton.elim _ y₀⟩
  · intro x₁ _ _
    exact ⟨0, Subsingleton.elim _ x₁⟩
  · intro y₁ _
    exact ⟨0, 0, map_zero _, Subsingleton.elim _ y₁⟩
  · intro x₂ _
    exact ⟨0, Subsingleton.elim _ x₂⟩
  · intro y₂
    exact ⟨0, 0, Subsingleton.elim _ y₂⟩

end DualityLadder

/-! ### The induction step and the composition-series theorem -/

section CompositionSeries

variable {ι ρ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ρ] {C : Type*} [Group C]

private theorem stokes_pi_dual_torsion {B : Type*} [AddCommGroup B] (κ : Type*)
    (v : κ → ElemDual B) : v + v = 0 :=
  funext fun k => ElemDual.add_self_eq_zero (v k)

/-- **The dévissage step of packet Lem. 5.1**: along a short exact sequence
`0 → A' → A → A'' → 0` of finite elementary `𝔽₂[C]`-modules, Stokes duality for the two ends
gives Stokes duality for the middle.  Cone dévissage: the source short exact sequence is
componentwise, the target one is the elementary-dual pack applied twice, the naturality
squares are the Stokes adjunction. -/
theorem stokesDuality_of_ses {A' A A'' : Type*}
    [AddCommGroup A'] [DistribMulAction C A'] [Finite A']
    [AddCommGroup A] [DistribMulAction C A] [Finite A]
    [AddCommGroup A''] [DistribMulAction C A''] [Finite A'']
    (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (f : A' →+ A) (g : A →+ A'')
    (hf : ∀ (co : C) (a : A'), f (co • a) = co • f a)
    (hg : ∀ (co : C) (a : A), g (co • a) = co • g a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : f.range = g.ker)
    (hA₂ : ∀ a : A, a + a = 0) (hA''₂ : ∀ a : A'', a + a = 0)
    (hd' : StokesDuality c w A') (hd'' : StokesDuality c w A'') :
    StokesDuality c w A := by
  -- the source columns
  have hS₀ : StokesSES f g := stokesSES_of_range_eq_ker hinj hsurj hexact
  have hdual : StokesSES (dualMap g) (dualMap f) := hS₀.dual hA₂ hA''₂
  -- the target columns: the dual pack, once at the module level and once at the term level
  have hT₀ : StokesSES (dualMap (stokesPi ρ (dualMap f))) (dualMap (stokesPi ρ (dualMap g))) :=
    (hdual.pi ρ).dual (stokes_pi_dual_torsion ρ) (stokes_pi_dual_torsion ρ)
  have hT₁ : StokesSES (dualMap (stokesPi ι (dualMap f))) (dualMap (stokesPi ι (dualMap g))) :=
    (hdual.pi ι).dual (stokes_pi_dual_torsion ι) (stokes_pi_dual_torsion ι)
  have hT₂ : StokesSES (dualMap (dualMap f)) (dualMap (dualMap g)) :=
    hdual.dual ElemDual.add_self_eq_zero ElemDual.add_self_eq_zero
  -- differential/column commutations on the dual side
  have hfd := dualMap_equivariant (C := C) f hf
  have hgd := dualMap_equivariant (C := C) g hg
  have hr₀ : ∀ v : ElemDual (ρ → ElemDual A'),
      dualMap (heisD1 (A := ElemDual A) c w) (dualMap (stokesPi ρ (dualMap f)) v)
        = dualMap (stokesPi ι (dualMap f))
            (dualMap (heisD1 (A := ElemDual A') c w) v) := fun v =>
    ElemDual.ext fun y => by
      show v (stokesPi ρ (dualMap f) (heisD1 (A := ElemDual A) c w y))
        = v (heisD1 (A := ElemDual A') c w (stokesPi ι (dualMap f) y))
      rw [heisD1_map c w (dualMap f) hfd y]
  have hr₁ : ∀ v : ElemDual (ι → ElemDual A'),
      dualMap (heisD0 (A := ElemDual A) c) (dualMap (stokesPi ι (dualMap f)) v)
        = dualMap (dualMap f) (dualMap (heisD0 (A := ElemDual A') c) v) := fun v =>
    ElemDual.ext fun lam => by
      show v (stokesPi ι (dualMap f) (heisD0 (A := ElemDual A) c lam))
        = v (heisD0 (A := ElemDual A') c (dualMap f lam))
      rw [heisD0_map c (dualMap f) hfd lam]
  have hs₀ : ∀ y : ElemDual (ρ → ElemDual A),
      dualMap (heisD1 (A := ElemDual A'') c w) (dualMap (stokesPi ρ (dualMap g)) y)
        = dualMap (stokesPi ι (dualMap g))
            (dualMap (heisD1 (A := ElemDual A) c w) y) := fun y =>
    ElemDual.ext fun t => by
      show y (stokesPi ρ (dualMap g) (heisD1 (A := ElemDual A'') c w t))
        = y (heisD1 (A := ElemDual A) c w (stokesPi ι (dualMap g) t))
      rw [heisD1_map c w (dualMap g) hgd t]
  have hs₁ : ∀ y : ElemDual (ι → ElemDual A),
      dualMap (heisD0 (A := ElemDual A'') c) (dualMap (stokesPi ι (dualMap g)) y)
        = dualMap (dualMap g) (dualMap (heisD0 (A := ElemDual A) c) y) := fun y =>
    ElemDual.ext fun lam => by
      show y (stokesPi ι (dualMap g) (heisD0 (A := ElemDual A'') c lam))
        = y (heisD0 (A := ElemDual A) c (dualMap g lam))
      rw [heisD0_map c (dualMap g) hgd lam]
  -- naturality of `η` in the columns
  have hn₀ : ∀ u : A', heisEta0 (f u)
      = dualMap (stokesPi ρ (dualMap f)) (heisEta0 (A := A') (ρ := ρ) u) := fun u =>
    ElemDual.ext fun ξ => rfl
  have hn₁ : ∀ x : ι → A', heisEta1 (A := A) c w (stokesPi ι f x)
      = dualMap (stokesPi ι (dualMap f)) (heisEta1 (A := A') c w x) := fun x =>
    ElemDual.ext fun y => by
      show (∑ k, (FreeGroup.lift (heisGen c (fun i => f (x i)) y) (w k)).z)
        = ∑ k, (FreeGroup.lift (heisGen c x (fun i => dualMap f (y i))) (w k)).z
      exact Finset.sum_congr rfl fun k _ => heisWord_z_adjoint c f hf x y (w k)
  have hn₂ : ∀ v : ρ → A', heisEta2 (stokesPi ρ f v)
      = dualMap (dualMap f) (heisEta2 (A := A') v) := fun v =>
    ElemDual.ext fun lam => by
      show lam (∑ k, f (v k)) = lam (f (∑ k, v k))
      rw [map_sum f v]
  have hm₀ : ∀ x : A, heisEta0 (g x)
      = dualMap (stokesPi ρ (dualMap g)) (heisEta0 (A := A) (ρ := ρ) x) := fun x =>
    ElemDual.ext fun ξ => rfl
  have hm₁ : ∀ x : ι → A, heisEta1 (A := A'') c w (stokesPi ι g x)
      = dualMap (stokesPi ι (dualMap g)) (heisEta1 (A := A) c w x) := fun x =>
    ElemDual.ext fun y => by
      show (∑ k, (FreeGroup.lift (heisGen c (fun i => g (x i)) y) (w k)).z)
        = ∑ k, (FreeGroup.lift (heisGen c x (fun i => dualMap g (y i))) (w k)).z
      exact Finset.sum_congr rfl fun k _ => heisWord_z_adjoint c g hg x y (w k)
  have hm₂ : ∀ v : ρ → A, heisEta2 (stokesPi ρ g v)
      = dualMap (dualMap g) (heisEta2 (A := A) v) := fun v =>
    ElemDual.ext fun lam => by
      show lam (∑ k, g (v k)) = lam (g (∑ k, v k))
      rw [map_sum g v]
  -- assemble: outer cones acyclic, cone dévissage, back to the ladder
  exact (stokesConeAcyclic_of_ses
    (fun a => stokes_square₀ c w hr hend a) (fun x => stokes_square₁ c w hr hend x)
    (heisD1_comp_heisD0 c w hr) (stokes_dual_comp c w hr)
    hS₀ (hS₀.pi ι) (hS₀.pi ρ) hT₀ hT₁ hT₂
    (heisD0_map c f hf) (heisD1_map c w f hf) (heisD0_map c g hg) (heisD1_map c w g hg)
    hr₀ hr₁ hs₀ hs₁ hn₀ hn₁ hn₂ hm₀ hm₁ hm₂
    (hd'.coneAcyclic (fun a => stokes_square₀ c w hr hend a)
      (fun x => stokes_square₁ c w hr hend x))
    (hd''.coneAcyclic (fun a => stokes_square₀ c w hr hend a)
      (fun x => stokes_square₁ c w hr hend x))).quasiIso

universe u

open GQ2.FoxH in
/-- **Packet Lem. 5.1 (`lem:composition`), the composition-series extension**: if the Stokes
duality ladder is a quasi-isomorphism for every *simple* finite elementary `𝔽₂[C]`-module, it
is one for **every** finite elementary module — including nonsplit coefficients.  Strong
induction on `Nat.card`, the induction step being the mapping-cone dévissage
`stokesDuality_of_ses`; the natural chain map and the commuting exact ladders are used
throughout, dimension equalities never (packet warning).  The `ℚ₂` chain proves this per word
by cloning a dévissage (`GQ2/Devissage` → `GQ2/Roe/Devissage`); the branch lanes instantiate
this theorem instead. -/
theorem stokesDuality_of_simple [Finite C] (c : ι → C) (w : ρ → FreeGroup ι)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (hsimp : ∀ (V : Type u) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality c w V)
    (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : StokesDuality c w A := by
  suffices h : ∀ (n : ℕ) (B : Type u) [AddCommGroup B] [DistribMulAction C B] [Finite B],
      Nat.card B = n → (∀ b : B, b + b = 0) → StokesDuality c w B by
    exact h (Nat.card A) A rfl hA₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro B instAdd instAct instFin hcard hB₂
    rcases subsingleton_or_nontrivial B with hsub | hnt
    · exact stokesDuality_of_subsingleton c w
    · by_cases hsimple : IsSimpleModTwo C B
      · exact hsimp B hB₂ hsimple
      · -- extract a proper nonzero `C`-stable subgroup and dévisse along it
        rw [IsSimpleModTwo] at hsimple
        push Not at hsimple
        obtain ⟨W, hWstable, hWbot, hWtop⟩ := hsimple hnt
        letI := stableSubAction W hWstable
        letI := stableQuotAction W hWstable
        have hW₂ : ∀ x : ↥W, x + x = 0 := two_torsion_sub W hB₂
        have hQ₂ : ∀ q : B ⧸ W, q + q = 0 := two_torsion_quot W hB₂
        have hltW : Nat.card ↥W < n := hcard ▸ card_lt_of_ne_top W hWtop
        have hltQ : Nat.card (B ⧸ W) < n := hcard ▸ card_quot_lt_of_ne_bot W hWbot
        have ihW : StokesDuality c w ↥W := IH _ hltW ↥W rfl hW₂
        have ihQ : StokesDuality c w (B ⧸ W) := IH _ hltQ (B ⧸ W) rfl hQ₂
        exact stokesDuality_of_ses c w hr hend W.subtype (QuotientAddGroup.mk' W)
          (stableSubAction_subtype_equivariant W hWstable)
          (stableQuotAction_mk'_equivariant W hWstable)
          (AddSubgroup.subtype_injective W)
          (QuotientAddGroup.mk'_surjective W)
          (subtype_range_eq_mk'_ker W) hB₂ hQ₂ ihW ihQ

end CompositionSeries

/-! ## Scalar-lane hooks: cup–Bockstein extraction

The scalar (`𝔽₂`-trivial-module) clause of the word certificate compares the traced Stokes
pairing against the field-side Hilbert Gram matrix in coordinates
(`GQ2/Roe/TrivialSelfDual.lean`'s `scalarGramR`-by-`decide` pattern).  The hooks: the
comparison matrix `stokesGram` of two representative families (entries are `heisEta1`-values,
`decide`-able on concrete modules), the relator-triviality bridge for discharging `hr` from
resolved reflected words, and the pairing-vanishing extraction that converts the relative
quasi-isomorphism clause into the "vanishing against all dual cocycles ⇒ coboundary" reading.

The **Bockstein diagonal** caveat travels with the matrix: a diagonal entry
`stokesGram p p` carries the quadratic refinement of the polar form (the `β(u⁻¹)`-rule
`heisEvalZ_inv_z` and the ω₂-scalar slots of the frozen chain), so comparisons must match
diagonals through the extraspecial normalization `κ_q⁰` — WW4's `Hessian.lean` interface, per
`class2.py`'s "the polarization alone cannot see the Bockstein diagonal". -/

section ScalarHooks

variable {ι ρ : Type*} [Fintype ρ] {C : Type*} [Group C] {A : Type*} [AddCommGroup A]
  [DistribMulAction C A]

/-- The **cup–Bockstein comparison matrix** of two families of offset vectors: the traced
Stokes pairing evaluated entrywise — the shape in which the marked local Hilbert matrix
comparison is performed (and `decide`-able on concrete finite modules). -/
noncomputable def stokesGram (c : ι → C) (w : ρ → FreeGroup ι) {m m' : ℕ}
    (xs : Fin m → ι → A) (ys : Fin m' → ι → ElemDual A) :
    Matrix (Fin m) (Fin m') (ZMod 2) :=
  Matrix.of fun p q => heisEta1 c w (xs p) (ys q)

@[simp] theorem stokesGram_apply (c : ι → C) (w : ρ → FreeGroup ι) {m m' : ℕ}
    (xs : Fin m → ι → A) (ys : Fin m' → ι → ElemDual A) (p : Fin m) (q : Fin m') :
    stokesGram c w xs ys p q = heisEta1 c w (xs p) (ys q) := rfl

omit [Fintype ρ] in
/-- Relator triviality transfers between the resolved free word and the reflected word — the
bridge for discharging the `hr` hypotheses of the chain map from Gate-level facts about the
branch words. -/
theorem lift_heisToFree_eq_one_iff {X G : Type*} [Group G] (μ : X → G) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    FreeGroup.lift μ (heisToFree E E₂ w) = 1 ↔ PWord.evalZ μ E E₂ w = 1 := by
  rw [evalZ_eq_lift_heisToFree]

/-- **Pairing-vanishing extraction** (left): under Stokes duality, a `1`-cocycle whose traced
pairing vanishes against **every** dual `1`-cocycle is a coboundary.  (The factorization
through the dual complex is the elementary-dual pack's extension lemma applied to the kernel
inclusion.) -/
theorem StokesDuality.pairing_vanish_left [Fintype ι] {c : ι → C} {w : ρ → FreeGroup ι}
    [Finite A] (hd : StokesDuality c w A) (x : ι → A) (hx : heisD1 c w x = 0)
    (hvan : ∀ y : ι → ElemDual A, heisD1 (A := ElemDual A) c w y = 0 → heisEta1 c w x y = 0) :
    ∃ v, heisD0 c v = x := by
  refine hd.h1_inj x hx ?_
  -- `η¹ x` kills the kernel of `d¹_{A^∨}`, hence factors through it by dual exactness.
  set v₁ : (ι → ElemDual A) →+ (ρ → ElemDual A) := heisD1 (A := ElemDual A) c w
  have hker : dualMap v₁.ker.subtype (heisEta1 c w x) = 0 := by
    ext y
    exact hvan y.1 (AddMonoidHom.mem_ker.mp y.2)
  have hfac := (dual_exact_pair (stokes_pi_dual_torsion (B := A) ρ) v₁.ker.subtype v₁
    (AddSubgroup.range_subtype _) (heisEta1 c w x)).mp hker
  obtain ⟨t, ht⟩ := AddMonoidHom.mem_range.mp hfac
  exact ⟨t, ht⟩

end ScalarHooks

/-! ## Stress tests

Regression pins in the sense of plan §3 A1; nothing below is cited by a proof. -/

section StressTests

open GQ2.FoxH

/-- Over a `Fin`-alphabet the generic exponent vector **is** the frozen one, definitionally. -/
theorem stress_heisEps_eq_expMod2 {m : ℕ} (i : Fin m) :
    heisEps (ι := Fin m) i = expMod2 i := rfl

/-- **The `Γ_A` endpoint pin** (Roe note Lem 5.1 / display (40) at `n = 1`): the relator pair
`(r_t, r_w)` of the frozen `Γ_A` chain — the tame word and the wild word at the odd
`ω₂`-representative `e = 3` — satisfies the generic endpoint condition: the traced mod-2
exponent vector vanishes.  Pins `IsStokesEndpoint` against `expMod2_fgTame` and
`expMod2_wildValueExp`. -/
theorem stress_endpoint_gammaA :
    IsStokesEndpoint ![fgTame, wildValueExp freeMarking 3] := by
  intro i
  rw [Fin.sum_univ_two]
  show Multiplicative.toAdd (expMod2 i fgTame)
      + Multiplicative.toAdd (expMod2 i (wildValueExp freeMarking 3)) = 0
  rw [congrFun expMod2_fgTame i, congrFun (expMod2_wildValueExp 3) i]
  fin_cases i <;> decide

/-- The trivial action of `Multiplicative (ZMod 2)` on `ZMod 2`, for the pin below only. -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- **Second-order rule pin**: the no-cross-term lemma is not vacuous — over
`A = ZMod 2` with `C = Multiplicative (ZMod 2)` acting trivially, a jet-carrying pair
produces a genuine cross term, and zeroing the left factor's dual jet kills exactly it. -/
theorem stress_jetZero_nonvacuous :
    ∃ p q : HeisLift (ZMod 2) (Multiplicative (ZMod 2)),
      (p * q).z ≠ p.z + q.z ∧
        ∀ p' q' : HeisLift (ZMod 2) (Multiplicative (ZMod 2)),
          p'.l = 0 → (p' * q').z = p'.z + q'.z := by
  refine ⟨⟨0, (AddMonoidHom.id (ZMod 2) : ElemDual (ZMod 2)), 0, 1⟩, ⟨1, 0, 0, 1⟩, ?_,
    fun p' q' h => ?_⟩
  · show (0 : ZMod 2) + 0 + (AddMonoidHom.id (ZMod 2))
        ((1 : Multiplicative (ZMod 2)) • (1 : ZMod 2)) ≠ 0 + 0
    decide +kernel
  · exact heisMul_z_of_l_eq_zero p' q' h

end StressTests

end GQ2.Dyadic
