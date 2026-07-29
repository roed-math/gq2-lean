/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Shapiro.Finiteness
public import GQ2.EulerCharacteristic
public import Mathlib.FieldTheory.Galois.Profinite

@[expose] public section

/-!
# The local Euler–Poincaré characteristic over a finite extension `K/ℚ₂` (LG2a)

**Derived from B7 — no new axiom.**  For `U ≤ G_ℚ₂` open of finite index (in the application
`U = G_K = K.fixingSubgroup` for `K/ℚ₂` finite) and a finite discrete `U`-module `V`, the
coinduced module

  `IndMod U V = Map(G_ℚ₂ ⧸ U, V)`,   `(g • Φ) x = τ(g,x) • Φ (g⁻¹ • x)`

is a finite discrete `G_ℚ₂`-module with `#(IndMod U V) = (#V) ^ [G : U]`, and Shapiro's lemma
identifies `Hⁱ(U, V) ≅ Hⁱ(G_ℚ₂, IndMod U V)` in **all three degrees `i = 0, 1, 2`**.  Feeding
`IndMod U V` to **B7** (`GQ2.Foundations.absGalQ2_localEulerCharacteristic`) and transporting
the three finiteness clauses and the three cardinalities therefore gives the `K`-level formula

  `#H¹(G_K, V) = #H⁰(G_K, V) · #H²(G_K, V) · 2 ^ (n · v₂(#V))`,   `n = [G_ℚ₂ : G_K]`,

with **no** multiplicativity of `χ` and **no** dévissage: `padicValNat 2 ((#V)^n)
= n · padicValNat 2 (#V)` is the whole exponent bookkeeping.  This closes the dyadic campaign's
`AX2` as a theorem (board `docs/dyadic/tickets.md`, design memo `docs/dyadic/lg-design.md` §1).

## Contents (the memo's L-decomposition)

* **L1** — the transversal/twist API.  `sect`, the Shapiro word `w(g,x)` and its cocycle rule
  are re-used verbatim from `GQ2.PermMod` (`GQ2/Shapiro/Finiteness.lean`, coefficient-free); the
  action is built from the **inverse** twist `τ(g,x) := w(g,x)⁻¹ = (sect x)⁻¹ · g · sect (g⁻¹•x)`
  (`GQ2.Dyadic.tw`), whose transport rule is `τ(g₁g₂,x) = τ(g₁,x) · τ(g₂, g₁⁻¹•x)`.  *The `𝔽₂`
  section `PermMod.sigmaFun` uses `w` itself; that is correct only because inversion in `𝔽₂` is
  trivial, and must not be copied at general coefficients.*
* **L0** — `IndMod` and its instances (`AddCommGroup`, discrete topology, `Finite`,
  `DistribMulAction`, `ContinuousSMul`) and `card_indMod`.
* **L2** — degree 0: `h0Equiv`, `H⁰(G, Ind V) ≃+ H⁰(U, V)` by constants/evaluation.
* **L3** — degree 1: `theta1` with the section `sigma1Fun` and the explicit round trips
  (`theta1Z_sigma1Fun` on the nose, `sigma1Fun_theta1Z_sub` up to the coboundary of
  `htpy1 C = (x ↦ C(sect x) x)`), hence `theta1_bijective` and `card_H1_indMod`.
* **L4** — degree 2: `theta2` with `sigma2Fun` and the prism homotopy
  `htpy2 C (g) (x) = C(sect x, τ(g,x))(x) − C(g, sect (g⁻¹•x))(x)`, hence `theta2_bijective`
  and `card_H2_indMod`.
* **L5** — assembly: `localEulerCharacteristic_open` (open finite-index `U ≤ G_ℚ₂`) and its
  field-level corollary `absGalK_localEulerCharacteristic`.

`#print axioms absGalK_localEulerCharacteristic` = the standard three plus
`GQ2.Foundations.absGalQ2_localEulerCharacteristic` (B7).  No new axiom, no `sorryAx`.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh

/-! ## L1 — the transversal and the twist `τ`

Everything here is coefficient-free.  `PermMod.sect`, `PermMod.wElt`, `PermMod.wElt_mul` and
`PermMod.basePt` come from `GQ2/Shapiro/Finiteness.lean`; the three small facts `sect_mk`,
`sect_base`, `smul_base_of_mem` are `private` there and are re-proved here (same one-line
proofs). -/

section L1

variable {U : Subgroup AbsGalQ2}

/-- `sect` is a set-theoretic section of `G → G ⧸ U`. -/
theorem sect_mk (x : AbsGalQ2 ⧸ U) :
    (QuotientGroup.mk (PermMod.sect x) : AbsGalQ2 ⧸ U) = x := by
  unfold PermMod.sect
  split
  · rename_i h; rw [h]; rfl
  · exact QuotientGroup.out_eq' x

/-- `sect` is normalized at the base coset. -/
theorem sect_base : PermMod.sect (PermMod.basePt U) = 1 := by
  unfold PermMod.sect; rw [if_pos rfl]

/-- Elements of `U` fix the base coset. -/
theorem smul_base_of_mem {v : AbsGalQ2} (hv : v ∈ U) :
    v • PermMod.basePt U = PermMod.basePt U := by
  show (QuotientGroup.mk (v * 1) : AbsGalQ2 ⧸ U) = QuotientGroup.mk 1
  rw [mul_one]
  exact QuotientGroup.eq.mpr (by simpa using U.inv_mem hv)

/-- `sect x` moves the base coset to `x`. -/
theorem sect_smul_base (x : AbsGalQ2 ⧸ U) : PermMod.sect x • PermMod.basePt U = x := by
  show (QuotientGroup.mk (PermMod.sect x * 1) : AbsGalQ2 ⧸ U) = x
  rw [mul_one]; exact sect_mk x

/-- `(sect x)⁻¹` moves `x` to the base coset. -/
theorem sect_inv_smul (x : AbsGalQ2 ⧸ U) :
    (PermMod.sect x)⁻¹ • x = PermMod.basePt U := by
  have h : (PermMod.sect x)⁻¹ • (QuotientGroup.mk (PermMod.sect x) : AbsGalQ2 ⧸ U)
      = PermMod.basePt U := by
    show (QuotientGroup.mk ((PermMod.sect x)⁻¹ * PermMod.sect x) : AbsGalQ2 ⧸ U)
        = PermMod.basePt U
    rw [inv_mul_cancel]; rfl
  rwa [sect_mk] at h

/-- **The Shapiro twist** `τ(g,x) := w(g,x)⁻¹ ∈ U`, the *inverse* of the word used by the
`𝔽₂`-only section of `GQ2/Shapiro/Finiteness.lean`. -/
noncomputable def tw (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) : ↥U := (PermMod.wElt g x)⁻¹

/-- The explicit word: `τ(g,x) = (sect x)⁻¹ · g · sect (g⁻¹•x)`. -/
theorem tw_coe (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    ((tw g x : ↥U) : AbsGalQ2)
      = (PermMod.sect x)⁻¹ * g * PermMod.sect (g⁻¹ • x) := by
  show ((PermMod.sect (g⁻¹ • x))⁻¹ * g⁻¹ * PermMod.sect x)⁻¹ = _
  group

/-- **The transport rule** `τ(g₁g₂, x) = τ(g₁,x) · τ(g₂, g₁⁻¹•x)` (the inverse of
`PermMod.wElt_mul`). -/
theorem tw_mul (g₁ g₂ : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    tw (g₁ * g₂) x = tw g₁ x * tw g₂ (g₁⁻¹ • x) := by
  simp only [tw, PermMod.wElt_mul, mul_inv_rev]

/-- `τ(1, x) = 1`. -/
theorem tw_one (x : AbsGalQ2 ⧸ U) : tw (1 : AbsGalQ2) x = 1 := by
  apply Subtype.ext
  rw [OneMemClass.coe_one, tw_coe, inv_one, one_smul]
  group

/-- **(B1)** `τ(u, ⟦1⟧) = u` for `u ∈ U`: the twist is the identity at the base coset. -/
theorem tw_base (u : ↥U) : tw ((u : AbsGalQ2)) (PermMod.basePt U) = u := by
  apply Subtype.ext
  rw [tw_coe, smul_base_of_mem (U.inv_mem u.2)]
  simp only [sect_base]
  group

/-- **(B3)** `τ(sect x, x) = 1`. -/
theorem tw_sect (x : AbsGalQ2 ⧸ U) : tw (PermMod.sect x) x = 1 := by
  apply Subtype.ext
  rw [OneMemClass.coe_one, tw_coe, sect_inv_smul, sect_base]
  group

/-- `τ((sect x)⁻¹, ⟦1⟧) = 1`. -/
theorem tw_sect_inv (x : AbsGalQ2 ⧸ U) :
    tw (PermMod.sect x)⁻¹ (PermMod.basePt U) = 1 := by
  apply Subtype.ext
  rw [OneMemClass.coe_one, tw_coe, sect_base, inv_inv, sect_smul_base]
  group

/-- Continuity of `g ↦ sect (g⁻¹ • x)` (the coset space is discrete for `U` open). -/
theorem continuous_sect_smul (hU : IsOpen (U : Set AbsGalQ2)) (x : AbsGalQ2 ⧸ U) :
    Continuous (fun g : AbsGalQ2 => PermMod.sect (g⁻¹ • x)) := by
  haveI := QuotientGroup.discreteTopology hU
  exact (continuous_of_discreteTopology (f := PermMod.sect (U := U))).comp
    ((PermMod.continuous_orbit x).comp continuous_inv)

/-- Continuity of `g ↦ τ(g,x)` for fixed `x`. -/
theorem continuous_tw (hU : IsOpen (U : Set AbsGalQ2)) (x : AbsGalQ2 ⧸ U) :
    Continuous (fun g : AbsGalQ2 => tw g x) := by
  have h : Continuous (fun g : AbsGalQ2 => PermMod.wElt g x) := by
    apply Continuous.subtype_mk
    exact (((continuous_sect_smul hU x).inv).mul continuous_inv).mul continuous_const
  exact h.inv

/-- Joint continuity of `(g₁, g₂) ↦ τ(g₂, g₁⁻¹•x)`, needed in degree 2. -/
theorem continuous_tw₂ (hU : IsOpen (U : Set AbsGalQ2)) (x : AbsGalQ2 ⧸ U) :
    Continuous (fun p : AbsGalQ2 × AbsGalQ2 => tw p.2 (p.1⁻¹ • x)) := by
  haveI := QuotientGroup.discreteTopology hU
  have h1 : Continuous (fun p : AbsGalQ2 × AbsGalQ2 =>
      PermMod.sect (p.2⁻¹ • p.1⁻¹ • x)) := by
    have hEq : (fun p : AbsGalQ2 × AbsGalQ2 => PermMod.sect (p.2⁻¹ • p.1⁻¹ • x))
        = fun p : AbsGalQ2 × AbsGalQ2 => PermMod.sect ((p.1 * p.2)⁻¹ • x) := by
      funext p; rw [mul_inv_rev, mul_smul]
    rw [hEq]
    exact (continuous_of_discreteTopology (f := PermMod.sect (U := U))).comp
      ((PermMod.continuous_orbit x).comp (continuous_fst.mul continuous_snd).inv)
  have h2 : Continuous (fun p : AbsGalQ2 × AbsGalQ2 => PermMod.sect (p.1⁻¹ • x)) :=
    (continuous_sect_smul hU x).comp continuous_fst
  have h : Continuous (fun p : AbsGalQ2 × AbsGalQ2 => PermMod.wElt p.2 (p.1⁻¹ • x)) := by
    apply Continuous.subtype_mk
    exact (h1.inv.mul continuous_snd.inv).mul h2
  exact h.inv

end L1

/-! ## L0 — the coinduced module `IndMod U V = Map(G ⧸ U, V)`

An **instance-opaque plain `def`** (as `PermMod` is): the coinduced `τ`-twisted action must not
be shadowed by the pointwise `Pi`-action on the raw function type. -/

/-- The **coinduced module** `Ind_U^G V = Map(G_ℚ₂ ⧸ U, V)` with the `τ`-twisted action
`(g • Φ) x = τ(g,x) • Φ (g⁻¹ • x)`.  For `V = 𝔽₂` with trivial `U`-action this is
`GQ2.PermMod U`. -/
def IndMod (U : Subgroup AbsGalQ2) (V : Type) : Type := (AbsGalQ2 ⧸ U) → V

namespace IndMod

variable {U : Subgroup AbsGalQ2} {V : Type}

section Additive

variable [AddCommGroup V]

noncomputable instance : AddCommGroup (IndMod U V) :=
  inferInstanceAs (AddCommGroup ((AbsGalQ2 ⧸ U) → V))

instance : TopologicalSpace (IndMod U V) := ⊥

instance : DiscreteTopology (IndMod U V) := ⟨rfl⟩

instance : IsTopologicalAddGroup (IndMod U V) := inferInstance

instance [Finite (AbsGalQ2 ⧸ U)] [Finite V] : Finite (IndMod U V) :=
  inferInstanceAs (Finite ((AbsGalQ2 ⧸ U) → V))

@[simp] theorem add_apply (Φ₁ Φ₂ : IndMod U V) (x : AbsGalQ2 ⧸ U) :
    (Φ₁ + Φ₂) x = Φ₁ x + Φ₂ x := rfl

@[simp] theorem neg_apply (Φ : IndMod U V) (x : AbsGalQ2 ⧸ U) : (-Φ) x = -(Φ x) := rfl

@[simp] theorem sub_apply (Φ₁ Φ₂ : IndMod U V) (x : AbsGalQ2 ⧸ U) :
    (Φ₁ - Φ₂) x = Φ₁ x - Φ₂ x := rfl

@[simp] theorem zero_apply (x : AbsGalQ2 ⧸ U) : (0 : IndMod U V) x = 0 := rfl

end Additive

/-- The constant function `x ↦ v`, as an element of `IndMod U V`. -/
def constMod (U : Subgroup AbsGalQ2) {V : Type} (v : V) : IndMod U V := fun _ => v

@[simp] theorem constMod_apply (v : V) (x : AbsGalQ2 ⧸ U) : constMod U v x = v := rfl

section Action

variable [AddCommGroup V] [DistribMulAction ↥U V]

noncomputable instance : SMul AbsGalQ2 (IndMod U V) :=
  ⟨fun g Φ => (fun x => tw g x • (Φ : (AbsGalQ2 ⧸ U) → V) (g⁻¹ • x) : IndMod U V)⟩

theorem smul_apply (g : AbsGalQ2) (Φ : IndMod U V) (x : AbsGalQ2 ⧸ U) :
    (g • Φ) x = tw g x • (Φ : (AbsGalQ2 ⧸ U) → V) (g⁻¹ • x) := rfl

noncomputable instance : DistribMulAction AbsGalQ2 (IndMod U V) where
  one_smul Φ := by
    funext x; rw [smul_apply, tw_one, one_smul, inv_one, one_smul]
  mul_smul g₁ g₂ Φ := by
    funext x
    rw [smul_apply, smul_apply, smul_apply, tw_mul, mul_smul, mul_inv_rev, mul_smul]
  smul_zero g := by funext x; rw [smul_apply]; exact smul_zero _
  smul_add g Φ₁ Φ₂ := by
    funext x
    rw [smul_apply, add_apply, add_apply, smul_apply, smul_apply]
    exact smul_add _ _ _

/-- The `↥U`-action on `IndMod U V` is the restriction of the `G_ℚ₂`-action. -/
theorem coe_smul (u : ↥U) (Φ : IndMod U V) : u • Φ = ((u : AbsGalQ2) • Φ : IndMod U V) := rfl

/-- **(B2)** `(sect x • Φ) x = Φ ⟦1⟧`. -/
theorem smul_sect_apply (Φ : IndMod U V) (x : AbsGalQ2 ⧸ U) :
    (PermMod.sect x • Φ : IndMod U V) x = Φ (PermMod.basePt U) := by
  rw [smul_apply, tw_sect, one_smul, sect_inv_smul]

/-- **(B2′)** `((sect x)⁻¹ • Ψ) ⟦1⟧ = Ψ x`. -/
theorem smul_sect_inv_base (Ψ : IndMod U V) (x : AbsGalQ2 ⧸ U) :
    ((PermMod.sect x)⁻¹ • Ψ : IndMod U V) (PermMod.basePt U) = Ψ x := by
  rw [smul_apply, tw_sect_inv, one_smul, inv_inv, sect_smul_base]

end Action

section Topology

variable [TopologicalSpace V] [DiscreteTopology V]

/-- A map into the discrete module `IndMod U V` is continuous as soon as each of its
`#(G ⧸ U)` coordinates is: every fibre is then a *finite* intersection of open sets. -/
theorem continuous_of_coord [Finite (AbsGalQ2 ⧸ U)] {W : Type} [TopologicalSpace W]
    (F : W → IndMod U V) (hF : ∀ x : AbsGalQ2 ⧸ U, Continuous (fun w => F w x)) :
    Continuous F := by
  refine (IsLocallyConstant.iff_isOpen_fiber.mpr (fun Φ₀ => ?_)).continuous
  have hset : F ⁻¹' {Φ₀} = ⋂ x : AbsGalQ2 ⧸ U, {w : W | F w x = Φ₀ x} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hw x; exact congrFun hw x
    · intro hw; funext x; exact hw x
  rw [hset]
  refine isOpen_iInter_of_finite (fun x => ?_)
  exact (hF x).isOpen_preimage {Φ₀ x} (isOpen_discrete _)

omit [DiscreteTopology V] in
/-- Evaluation `IndMod U V → V` at a coset is continuous (both sides discrete). -/
theorem continuous_eval (x : AbsGalQ2 ⧸ U) :
    Continuous (fun Φ : IndMod U V => Φ x) := continuous_of_discreteTopology

variable [AddCommGroup V] [DistribMulAction ↥U V] [ContinuousSMul ↥U V]

theorem continuous_smul_left (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)]
    (Φ : IndMod U V) : Continuous (fun g : AbsGalQ2 => g • Φ) := by
  haveI := QuotientGroup.discreteTopology hU
  exact continuous_of_coord _ (fun x => continuous_smul.comp ((continuous_tw hU x).prodMk
    (continuous_of_discreteTopology.comp ((PermMod.continuous_orbit x).comp continuous_inv))))

/-- The coinduced action is (jointly) continuous. -/
theorem continuousSMul (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] :
    ContinuousSMul AbsGalQ2 (IndMod U V) :=
  ⟨continuous_prod_of_discrete_right.mpr (fun Φ => continuous_smul_left hU Φ)⟩

end Topology

/-- `#(Ind_U^G V) = (#V) ^ [G : U]` (Mathlib's `Nat.card_fun`). -/
theorem card_indMod (U : Subgroup AbsGalQ2) (V : Type) [Finite (AbsGalQ2 ⧸ U)] :
    Nat.card (IndMod U V) = Nat.card V ^ U.index := by
  show Nat.card ((AbsGalQ2 ⧸ U) → V) = _
  rw [Nat.card_fun, Subgroup.index_eq_card]

/-! ### Evaluation at the base coset -/

/-- **Evaluation at the base coset** `Φ ↦ Φ ⟦1⟧`, a `U`-equivariant additive map `Ind V → V`. -/
noncomputable def ev (U : Subgroup AbsGalQ2) (V : Type) [AddCommGroup V] : IndMod U V →+ V where
  toFun Φ := (Φ : (AbsGalQ2 ⧸ U) → V) (PermMod.basePt U)
  map_zero' := rfl
  map_add' _ _ := rfl

variable [AddCommGroup V]

theorem ev_apply (Φ : IndMod U V) : ev U V Φ = Φ (PermMod.basePt U) := rfl

theorem ev_continuous [TopologicalSpace V] [DiscreteTopology V] :
    Continuous (ev U V) := continuous_of_discreteTopology

/-- `ev` intertwines the `U`-actions — this is **(B1)** `τ(u, ⟦1⟧) = u`. -/
theorem ev_compat [DistribMulAction ↥U V] (u : ↥U) (Φ : IndMod U V) :
    ev U V (u • Φ) = u • ev U V Φ := by
  show ((u : AbsGalQ2) • Φ : IndMod U V) (PermMod.basePt U) = u • Φ (PermMod.basePt U)
  rw [smul_apply, tw_base, smul_base_of_mem (U.inv_mem u.2)]

end IndMod

/-! ## L2 — degree 0: `H⁰(G, Ind V) ≃+ H⁰(U, V)` by constants / evaluation -/

section L2

open IndMod

variable (U : Subgroup AbsGalQ2) (V : Type) [AddCommGroup V] [DistribMulAction ↥U V]

/-- A constant function is `G`-invariant iff its value is `U`-invariant (`τ(g,x) ∈ U`). -/
theorem const_mem_H0 (v : V) (hv : v ∈ H0 ↥U V) :
    constMod U v ∈ H0 AbsGalQ2 (IndMod U V) := by
  intro g
  funext x
  rw [IndMod.smul_apply]
  exact hv (tw g x)

theorem ev_mem_H0 (Φ : IndMod U V) (hΦ : Φ ∈ H0 AbsGalQ2 (IndMod U V)) :
    ev U V Φ ∈ H0 ↥U V := by
  intro u
  rw [← ev_compat u Φ]
  show ev U V ((u : AbsGalQ2) • Φ) = ev U V Φ
  rw [hΦ (u : AbsGalQ2)]

/-- A `G`-invariant `Φ` is constant: `Φ x = (sect x • Φ) x = Φ ⟦1⟧`. -/
theorem const_ev (Φ : IndMod U V) (hΦ : Φ ∈ H0 AbsGalQ2 (IndMod U V)) :
    constMod U (ev U V Φ) = Φ := by
  funext x
  show ev U V Φ = Φ x
  have h := smul_sect_apply Φ x
  rw [hΦ (PermMod.sect x)] at h
  exact h.symm

/-- **Degree-0 Shapiro**: `H⁰(G_ℚ₂, Ind_U^G V) ≃+ H⁰(U, V)`, evaluation at `⟦1⟧` with inverse
"constant function". -/
noncomputable def h0Equiv : ↥(H0 AbsGalQ2 (IndMod U V)) ≃+ ↥(H0 ↥U V) where
  toFun Φ := ⟨ev U V Φ.1, ev_mem_H0 U V Φ.1 Φ.2⟩
  invFun v := ⟨constMod U v.1, const_mem_H0 U V v.1 v.2⟩
  left_inv Φ := Subtype.ext (const_ev U V Φ.1 Φ.2)
  right_inv _ := Subtype.ext rfl
  map_add' _ _ := rfl

/-- Degree-0 cardinality transport. -/
theorem card_H0_indMod :
    Nat.card ↥(H0 AbsGalQ2 (IndMod U V)) = Nat.card ↥(H0 ↥U V) :=
  Nat.card_congr (h0Equiv U V).toEquiv

end L2

/-! ## L3 — degree 1

`θ₁ = mapCoeff₁(ev) ∘ res₁` with the explicit section `σ₁(c)(g)(x) = c (τ(g,x))`.  Round trip A
is on the nose at the `Z¹`-level; round trip B holds modulo the explicit coboundary of
`htpy1 C = (x ↦ C(sect x) x)`. -/

section L3

open IndMod

variable (U : Subgroup AbsGalQ2) (V : Type) [AddCommGroup V] [TopologicalSpace V]
  [DiscreteTopology V] [DistribMulAction ↥U V]

/-- The `Z¹`-level Shapiro map: restrict to `U`, then evaluate at the base coset. -/
noncomputable def theta1Z : ↥(Z1 AbsGalQ2 (IndMod U V)) →+ ↥(Z1 ↥U V) :=
  (Z1comap (ContinuousMonoidHom.id ↥U) (ev U V) ev_continuous
      (fun u Φ => ev_compat u Φ)).comp
    (Z1comap (subgroupIncl AbsGalQ2 U) (AddMonoidHom.id (IndMod U V)) continuous_id
      (fun _ _ => rfl))

/-- **The degree-1 Shapiro map** `θ₁ : H¹(G_ℚ₂, Ind_U^G V) →+ H¹(U, V)`. -/
noncomputable def theta1 : H1 AbsGalQ2 (IndMod U V) →+ H1 ↥U V :=
  (mapCoeff1 (ev U V) ev_continuous (fun u Φ => ev_compat u Φ)).comp
    (res1 AbsGalQ2 (IndMod U V) U)

variable {U V}

theorem theta1Z_apply (C : ↥(Z1 AbsGalQ2 (IndMod U V))) (u : ↥U) :
    (theta1Z U V C).1 u = C.1 (u : AbsGalQ2) (PermMod.basePt U) := rfl

theorem theta1_H1mk (C : ↥(Z1 AbsGalQ2 (IndMod U V))) :
    theta1 U V (H1mk AbsGalQ2 (IndMod U V) C) = H1mk (↥U) V (theta1Z U V C) := rfl

/-- **The degree-1 Shapiro section** `σ₁(c)(g)(x) = c (τ(g,x))` — the **inverse** twist. -/
noncomputable def sigma1Fun (c : ↥U → V) : AbsGalQ2 → IndMod U V :=
  fun g => (fun x => c (tw g x) : IndMod U V)

omit [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction ↥U V] in
theorem sigma1Fun_apply (c : ↥U → V) (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    sigma1Fun c g x = c (tw g x) := rfl

omit [AddCommGroup V] [DistribMulAction ↥U V] in
theorem sigma1Fun_continuous [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    {c : ↥U → V} (hc : Continuous c) : Continuous (sigma1Fun c) :=
  continuous_of_coord _ (fun x => hc.comp (continuous_tw hU x))

/-- `σ₁` lands in `Z¹`: the transport rule for `τ` *is* the 1-cocycle rule at the moved pair. -/
theorem sigma1Fun_mem [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    (c : ↥(Z1 ↥U V)) : sigma1Fun c.1 ∈ Z1 AbsGalQ2 (IndMod U V) := by
  obtain ⟨hcc, hc⟩ := mem_Z1_iff.mp c.2
  refine mem_Z1_iff.mpr ⟨sigma1Fun_continuous hU hcc, fun g₁ g₂ => ?_⟩
  funext x
  rw [sigma1Fun_apply, IndMod.add_apply, sigma1Fun_apply, IndMod.smul_apply, sigma1Fun_apply,
    tw_mul, hc]

/-- **Round trip A** (on the nose, at the `Z¹`-level): `θ₁(σ₁ c) = c`, by `τ(u, ⟦1⟧) = u`. -/
theorem theta1Z_sigma1Fun [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    (c : ↥(Z1 ↥U V)) :
    theta1Z U V ⟨sigma1Fun c.1, sigma1Fun_mem hU c⟩ = c := by
  apply Subtype.ext
  funext u
  show sigma1Fun c.1 (u : AbsGalQ2) (PermMod.basePt U) = c.1 u
  rw [sigma1Fun_apply, tw_base]

omit [TopologicalSpace V] [DiscreteTopology V] in
/-- `σ₁` carries coboundaries to coboundaries: `σ₁(δ⁰v) = δ⁰(const v)`. -/
theorem sigma1Fun_dZero (v : V) :
    sigma1Fun (dZero ↥U V v) = dZero AbsGalQ2 (IndMod U V) (constMod U v) := by
  funext g
  funext x
  rfl

/-- The degree-1 prism homotopy `m x = C (sect x) x`. -/
noncomputable def htpy1 (C : ↥(Z1 AbsGalQ2 (IndMod U V))) : IndMod U V :=
  fun x => C.1 (PermMod.sect x) x

omit [TopologicalSpace V] [DiscreteTopology V] in
/-- The cocycle expansion of `C` along the transversal word: expand
`C(s_x⁻¹ · g · s_{g⁻¹x})` by the 1-cocycle rule twice and evaluate at `⟦1⟧`. -/
theorem cocycle_tw (C : ↥(Z1 AbsGalQ2 (IndMod U V))) (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    C.1 ((tw g x : ↥U) : AbsGalQ2) (PermMod.basePt U)
      = -(C.1 (PermMod.sect x) x) + C.1 g x
        + tw g x • C.1 (PermMod.sect (g⁻¹ • x)) (g⁻¹ • x) := by
  have hc := (mem_Z1_iff.mp C.2).2
  rw [tw_coe, hc _ (PermMod.sect (g⁻¹ • x)), hc (PermMod.sect x)⁻¹ g]
  rw [IndMod.add_apply, IndMod.add_apply, mul_smul]
  rw [IndMod.smul_sect_inv_base, IndMod.smul_sect_inv_base, IndMod.smul_apply]
  rw [Z1_apply_inv C (PermMod.sect x), IndMod.neg_apply, IndMod.smul_sect_inv_base]

/-- **Round trip B**: `σ₁(θ₁ C) − C = δ⁰(htpy1 C)`. -/
theorem sigma1Fun_theta1Z_sub (C : ↥(Z1 AbsGalQ2 (IndMod U V))) :
    sigma1Fun (theta1Z U V C).1 - C.1 = dZero AbsGalQ2 (IndMod U V) (htpy1 C) := by
  funext g
  funext x
  show C.1 ((tw g x : ↥U) : AbsGalQ2) (PermMod.basePt U) - C.1 g x
      = ((g • htpy1 C : IndMod U V) - htpy1 C) x
  rw [IndMod.sub_apply, IndMod.smul_apply, cocycle_tw]
  show _ = tw g x • C.1 (PermMod.sect (g⁻¹ • x)) (g⁻¹ • x) - C.1 (PermMod.sect x) x
  abel

/-- **`θ₁` is bijective on `H¹`** — Shapiro in degree 1 at general coefficients. -/
theorem theta1_bijective [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2)) :
    Function.Bijective (theta1 U V) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr ?_
    intro ξ hξ
    obtain ⟨C, rfl⟩ := H1mk_surjective ξ
    rw [theta1_H1mk] at hξ
    have hB : (theta1Z U V C).1 ∈ B1 ↥U V := by
      have := (QuotientAddGroup.eq_zero_iff _).mp hξ
      exact (AddSubgroup.mem_addSubgroupOf).mp this
    obtain ⟨v, hv⟩ := hB
    have hkey : C.1 = dZero AbsGalQ2 (IndMod U V) (constMod U v - htpy1 C) := by
      rw [map_sub, ← sigma1Fun_dZero, hv, ← sigma1Fun_theta1Z_sub C]
      abel
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      ((AddSubgroup.mem_addSubgroupOf).mpr ⟨_, hkey.symm⟩)
  · intro ξ
    obtain ⟨c, rfl⟩ := H1mk_surjective ξ
    refine ⟨H1mk AbsGalQ2 (IndMod U V) ⟨sigma1Fun c.1, sigma1Fun_mem hU c⟩, ?_⟩
    rw [theta1_H1mk, theta1Z_sigma1Fun hU c]

/-- Degree-1 cardinality transport. -/
theorem card_H1_indMod [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2)) :
    Nat.card (H1 AbsGalQ2 (IndMod U V)) = Nat.card (H1 ↥U V) :=
  Nat.card_congr (Equiv.ofBijective _ (theta1_bijective hU))

end L3

/-! ## L4 — degree 2

`θ₂ = mapCoeff₂(ev) ∘ res₂` with `σ₂(c)(g₁,g₂)(x) = c (τ(g₁,x), τ(g₂, g₁⁻¹•x))`.  Round trip A
is again on the nose; round trip B is the prism homotopy
`h(g)(x) = C(s_x, τ(g,x))(x) − C(g, s_{g⁻¹x})(x)`, whose verification is exactly three
applications of the 2-cocycle rule, at `(s₀, τ₁, τ₂)`, `(g₁, s₁, τ₂)` and `(g₁, g₂, s₂)`. -/

section L4

open IndMod

variable (U : Subgroup AbsGalQ2) (V : Type) [AddCommGroup V] [TopologicalSpace V]
  [DiscreteTopology V] [DistribMulAction ↥U V]

/-- The `Z²`-level Shapiro map. -/
noncomputable def theta2Z : ↥(Z2 AbsGalQ2 (IndMod U V)) →+ ↥(Z2 ↥U V) :=
  (Z2comap (ContinuousMonoidHom.id ↥U) (ev U V) ev_continuous
      (fun u Φ => ev_compat u Φ)).comp
    (Z2comap (subgroupIncl AbsGalQ2 U) (AddMonoidHom.id (IndMod U V)) continuous_id
      (fun _ _ => rfl))

/-- **The degree-2 Shapiro map** `θ₂ : H²(G_ℚ₂, Ind_U^G V) →+ H²(U, V)`. -/
noncomputable def theta2 : H2 AbsGalQ2 (IndMod U V) →+ H2 ↥U V :=
  (mapCoeff2 (ev U V) ev_continuous (fun u Φ => ev_compat u Φ)).comp
    (res2 AbsGalQ2 (IndMod U V) U)

variable {U V}

theorem theta2Z_apply (C : ↥(Z2 AbsGalQ2 (IndMod U V))) (u₁ u₂ : ↥U) :
    (theta2Z U V C).1 (u₁, u₂)
      = C.1 ((u₁ : AbsGalQ2), (u₂ : AbsGalQ2)) (PermMod.basePt U) := rfl

theorem theta2_H2mk (C : ↥(Z2 AbsGalQ2 (IndMod U V))) :
    theta2 U V (H2mk AbsGalQ2 (IndMod U V) C) = H2mk (↥U) V (theta2Z U V C) := rfl

/-- **The degree-2 Shapiro section** `σ₂(c)(g₁,g₂)(x) = c (τ(g₁,x), τ(g₂, g₁⁻¹•x))`. -/
noncomputable def sigma2Fun (c : ↥U × ↥U → V) : AbsGalQ2 × AbsGalQ2 → IndMod U V :=
  fun p => (fun x => c (tw p.1 x, tw p.2 (p.1⁻¹ • x)) : IndMod U V)

omit [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [DistribMulAction ↥U V] in
theorem sigma2Fun_apply (c : ↥U × ↥U → V) (p : AbsGalQ2 × AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    sigma2Fun c p x = c (tw p.1 x, tw p.2 (p.1⁻¹ • x)) := rfl

omit [AddCommGroup V] [DistribMulAction ↥U V] in
theorem sigma2Fun_continuous [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    {c : ↥U × ↥U → V} (hc : Continuous c) : Continuous (sigma2Fun c) :=
  continuous_of_coord _ (fun x =>
    hc.comp (((continuous_tw hU x).comp continuous_fst).prodMk (continuous_tw₂ hU x)))

/-- `σ₂` lands in `Z²`: with `a = τ(g₁,x)`, `b = τ(g₂,g₁⁻¹x)`, `d = τ(g₃,g₂⁻¹g₁⁻¹x)` the
2-cocycle identity for `σ₂(c)` at `(g₁,g₂,g₃)` evaluated at `x` is literally the one for `c` at
`(a,b,d)`. -/
theorem sigma2Fun_mem [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    (c : ↥(Z2 ↥U V)) : sigma2Fun c.1 ∈ Z2 AbsGalQ2 (IndMod U V) := by
  obtain ⟨hcc, hc⟩ := mem_Z2_iff.mp c.2
  refine mem_Z2_iff.mpr ⟨sigma2Fun_continuous hU hcc, fun g₁ g₂ g₃ => ?_⟩
  funext x
  rw [IndMod.add_apply, IndMod.add_apply, IndMod.smul_apply, sigma2Fun_apply, sigma2Fun_apply,
    sigma2Fun_apply, sigma2Fun_apply]
  show tw g₁ x • c.1 (tw g₂ (g₁⁻¹ • x), tw g₃ (g₂⁻¹ • g₁⁻¹ • x))
      + c.1 (tw g₁ x, tw (g₂ * g₃) (g₁⁻¹ • x))
    = c.1 (tw (g₁ * g₂) x, tw g₃ ((g₁ * g₂)⁻¹ • x)) + c.1 (tw g₁ x, tw g₂ (g₁⁻¹ • x))
  rw [tw_mul, tw_mul, mul_inv_rev, mul_smul, hc]

omit [TopologicalSpace V] [DiscreteTopology V] in
/-- `σ₂` carries coboundaries to coboundaries: `σ₂(δ¹ψ) = δ¹(σ₁ψ)`. -/
theorem sigma2Fun_dOne (ψ : ↥U → V) :
    sigma2Fun (dOne ↥U V ψ) = dOne AbsGalQ2 (IndMod U V) (sigma1Fun ψ) := by
  funext p
  funext x
  obtain ⟨g₁, g₂⟩ := p
  show tw g₁ x • ψ (tw g₂ (g₁⁻¹ • x)) - ψ (tw g₁ x * tw g₂ (g₁⁻¹ • x)) + ψ (tw g₁ x)
      = ((g₁ • sigma1Fun ψ g₂ : IndMod U V) - sigma1Fun ψ (g₁ * g₂) + sigma1Fun ψ g₁) x
  rw [IndMod.add_apply, IndMod.sub_apply, IndMod.smul_apply, sigma1Fun_apply, sigma1Fun_apply,
    sigma1Fun_apply, tw_mul]

/-- **Round trip A** (on the nose, at the `Z²`-level): `θ₂(σ₂ c) = c`. -/
theorem theta2Z_sigma2Fun [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    (c : ↥(Z2 ↥U V)) :
    theta2Z U V ⟨sigma2Fun c.1, sigma2Fun_mem hU c⟩ = c := by
  apply Subtype.ext
  funext q
  obtain ⟨u₁, u₂⟩ := q
  show c.1 (tw (u₁ : AbsGalQ2) (PermMod.basePt U),
      tw (u₂ : AbsGalQ2) ((u₁ : AbsGalQ2)⁻¹ • PermMod.basePt U)) = c.1 (u₁, u₂)
  rw [smul_base_of_mem (U.inv_mem u₁.2), tw_base, tw_base]

/-- The degree-2 prism homotopy `h(g)(x) = C(s_x, τ(g,x))(x) − C(g, s_{g⁻¹x})(x)`. -/
noncomputable def htpy2 (C : ↥(Z2 AbsGalQ2 (IndMod U V))) : AbsGalQ2 → IndMod U V :=
  fun g => (fun x => C.1 (PermMod.sect x, ((tw g x : ↥U) : AbsGalQ2)) x
    - C.1 (g, PermMod.sect (g⁻¹ • x)) x : IndMod U V)

omit [TopologicalSpace V] [DiscreteTopology V] in
theorem htpy2_apply (C : ↥(Z2 AbsGalQ2 (IndMod U V))) (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    htpy2 C g x = C.1 (PermMod.sect x, ((tw g x : ↥U) : AbsGalQ2)) x
      - C.1 (g, PermMod.sect (g⁻¹ • x)) x := rfl

theorem htpy2_continuous [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2))
    (C : ↥(Z2 AbsGalQ2 (IndMod U V))) : Continuous (htpy2 C) := by
  have hC : Continuous C.1 := (mem_Z2_iff.mp C.2).1
  refine continuous_of_coord _ (fun x => ?_)
  refine Continuous.sub ?_ ?_
  · exact (continuous_eval x).comp
      (hC.comp (continuous_const.prodMk (continuous_subtype_val.comp (continuous_tw hU x))))
  · exact (continuous_eval x).comp
      (hC.comp (continuous_id.prodMk (continuous_sect_smul hU x)))

omit [TopologicalSpace V] [DiscreteTopology V] in
/-- **The prism identity**, before evaluation: three applications of the 2-cocycle rule, at
`(s₀, τ₁, τ₂)`, `(g₁, s₁, τ₂)` and `(g₁, g₂, s₂)`, using `s₀τ₁ = g₁s₁` and `s₁τ₂ = g₂s₂`. -/
theorem prism_identity (C : ↥(Z2 AbsGalQ2 (IndMod U V))) (g₁ g₂ : AbsGalQ2)
    (x : AbsGalQ2 ⧸ U) :
    (PermMod.sect x • C.1 (((tw g₁ x : ↥U) : AbsGalQ2),
        ((tw g₂ (g₁⁻¹ • x) : ↥U) : AbsGalQ2)) : IndMod U V)
      = g₁ • C.1 (PermMod.sect (g₁⁻¹ • x), ((tw g₂ (g₁⁻¹ • x) : ↥U) : AbsGalQ2))
        - g₁ • C.1 (g₂, PermMod.sect (g₂⁻¹ • g₁⁻¹ • x))
        - C.1 (PermMod.sect x, ((tw (g₁ * g₂) x : ↥U) : AbsGalQ2))
        + C.1 (g₁ * g₂, PermMod.sect (g₂⁻¹ • g₁⁻¹ • x))
        + C.1 (PermMod.sect x, ((tw g₁ x : ↥U) : AbsGalQ2))
        - C.1 (g₁, PermMod.sect (g₁⁻¹ • x))
        + C.1 (g₁, g₂) := by
  have hc := (mem_Z2_iff.mp C.2).2
  have hs₀τ₁ : PermMod.sect x * ((tw g₁ x : ↥U) : AbsGalQ2)
      = g₁ * PermMod.sect (g₁⁻¹ • x) := by rw [tw_coe]; group
  have hs₁τ₂ : PermMod.sect (g₁⁻¹ • x) * ((tw g₂ (g₁⁻¹ • x) : ↥U) : AbsGalQ2)
      = g₂ * PermMod.sect (g₂⁻¹ • g₁⁻¹ • x) := by rw [tw_coe]; group
  have hτ₁τ₂ : ((tw g₁ x : ↥U) : AbsGalQ2) * ((tw g₂ (g₁⁻¹ • x) : ↥U) : AbsGalQ2)
      = ((tw (g₁ * g₂) x : ↥U) : AbsGalQ2) := by rw [tw_mul]; rfl
  set s₀ := PermMod.sect x with hs₀
  set s₁ := PermMod.sect (g₁⁻¹ • x) with hs₁
  set s₂ := PermMod.sect (g₂⁻¹ • g₁⁻¹ • x) with hs₂
  set τ₁ := ((tw g₁ x : ↥U) : AbsGalQ2) with hτ₁
  set τ₂ := ((tw g₂ (g₁⁻¹ • x) : ↥U) : AbsGalQ2) with hτ₂
  have h1 := hc s₀ τ₁ τ₂
  have h2 := hc g₁ s₁ τ₂
  have h3 := hc g₁ g₂ s₂
  rw [hs₀τ₁, hτ₁τ₂] at h1
  rw [hs₁τ₂] at h2
  have e1 : (s₀ • C.1 (τ₁, τ₂) : IndMod U V)
      = C.1 (g₁ * s₁, τ₂) + C.1 (s₀, τ₁)
        - C.1 (s₀, ((tw (g₁ * g₂) x : ↥U) : AbsGalQ2)) := by
    rw [← h1]; abel
  have e2 : C.1 (g₁ * s₁, τ₂)
      = (g₁ • C.1 (s₁, τ₂) : IndMod U V) + C.1 (g₁, g₂ * s₂) - C.1 (g₁, s₁) := by
    rw [h2]; abel
  have e3 : C.1 (g₁, g₂ * s₂)
      = C.1 (g₁ * g₂, s₂) + C.1 (g₁, g₂) - (g₁ • C.1 (g₂, s₂) : IndMod U V) := by
    rw [← h3]; abel
  rw [e1, e2, e3]
  abel

/-- **Round trip B** in degree 2: `σ₂(θ₂ C) − C = δ¹(htpy2 C)`. -/
theorem sigma2Fun_theta2Z_sub (C : ↥(Z2 AbsGalQ2 (IndMod U V))) :
    sigma2Fun (theta2Z U V C).1 - C.1 = dOne AbsGalQ2 (IndMod U V) (htpy2 C) := by
  funext p
  funext x
  obtain ⟨g₁, g₂⟩ := p
  have hkey := congrFun (prism_identity C g₁ g₂ x) x
  rw [smul_sect_apply] at hkey
  show C.1 (((tw g₁ x : ↥U) : AbsGalQ2), ((tw g₂ (g₁⁻¹ • x) : ↥U) : AbsGalQ2))
        (PermMod.basePt U) - C.1 (g₁, g₂) x
      = ((g₁ • htpy2 C g₂ : IndMod U V) - htpy2 C (g₁ * g₂) + htpy2 C g₁) x
  simp only [IndMod.add_apply, IndMod.sub_apply, IndMod.smul_apply] at hkey
  rw [hkey]
  simp only [IndMod.add_apply, IndMod.sub_apply, IndMod.smul_apply, htpy2_apply, smul_sub,
    show (g₁ * g₂)⁻¹ • x = g₂⁻¹ • g₁⁻¹ • x from by rw [mul_inv_rev, mul_smul]]
  abel

/-- **`θ₂` is bijective on `H²`** — Shapiro in degree 2 at general coefficients. -/
theorem theta2_bijective [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2)) :
    Function.Bijective (theta2 U V) := by
  constructor
  · refine (injective_iff_map_eq_zero _).mpr ?_
    intro ξ hξ
    obtain ⟨C, rfl⟩ := H2mk_surjective ξ
    rw [theta2_H2mk] at hξ
    have hB : (theta2Z U V C).1 ∈ B2 ↥U V :=
      (AddSubgroup.mem_addSubgroupOf).mp ((QuotientAddGroup.eq_zero_iff _).mp hξ)
    obtain ⟨ψ, hψc, hψ⟩ := hB
    have hkey : C.1 = dOne AbsGalQ2 (IndMod U V) (sigma1Fun ψ - htpy2 C) := by
      rw [map_sub, ← sigma2Fun_dOne, hψ, ← sigma2Fun_theta2Z_sub C]
      abel
    refine (QuotientAddGroup.eq_zero_iff _).mpr
      ((AddSubgroup.mem_addSubgroupOf).mpr ⟨sigma1Fun ψ - htpy2 C, ?_, hkey.symm⟩)
    exact (sigma1Fun_continuous hU hψc).sub (htpy2_continuous hU C)
  · intro ξ
    obtain ⟨c, rfl⟩ := H2mk_surjective ξ
    refine ⟨H2mk AbsGalQ2 (IndMod U V) ⟨sigma2Fun c.1, sigma2Fun_mem hU c⟩, ?_⟩
    rw [theta2_H2mk, theta2Z_sigma2Fun hU c]

/-- Degree-2 cardinality transport. -/
theorem card_H2_indMod [Finite (AbsGalQ2 ⧸ U)] (hU : IsOpen (U : Set AbsGalQ2)) :
    Nat.card (H2 AbsGalQ2 (IndMod U V)) = Nat.card (H2 ↥U V) :=
  Nat.card_congr (Equiv.ofBijective _ (theta2_bijective hU))

end L4

/-! ## L5 — assembly: B7 at `IndMod U V` is the `K`-level Euler characteristic -/

section L5

open IndMod

/-- **The local Euler–Poincaré characteristic for an open subgroup `U ≤ G_ℚ₂`.**  Derived from
**B7** applied to the coinduced module `IndMod U V`, whose order is `(#V) ^ [G_ℚ₂ : U]`, through
the degree-0/1/2 Shapiro comparisons `h0Equiv`, `theta1`, `theta2`.  No new axiom. -/
theorem localEulerCharacteristic_open (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [Finite V] :
    Finite (H0 ↥U V) ∧ Finite (H1 ↥U V) ∧ Finite (H2 ↥U V) ∧
      Nat.card (H1 ↥U V)
        = Nat.card (H0 ↥U V) * Nat.card (H2 ↥U V)
          * 2 ^ (U.index * padicValNat 2 (Nat.card V)) := by
  haveI := IndMod.continuousSMul (U := U) (V := V) hU
  obtain ⟨hfin0, hfin1, hfin2, hcard⟩ :=
    Foundations.absGalQ2_localEulerCharacteristic (IndMod U V)
  have hVne : Nat.card V ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have hexp : padicValNat 2 (Nat.card (IndMod U V)) = U.index * padicValNat 2 (Nat.card V) := by
    rw [card_indMod, padicValNat.pow _ hVne]
  refine ⟨Finite.of_equiv _ (h0Equiv U V).toEquiv,
    Finite.of_equiv _ (Equiv.ofBijective _ (theta1_bijective (V := V) hU)),
    Finite.of_equiv _ (Equiv.ofBijective _ (theta2_bijective (V := V) hU)), ?_⟩
  rw [← card_H1_indMod (V := V) hU, ← card_H0_indMod U V, ← card_H2_indMod (V := V) hU, hcard,
    hexp]

/-! ### The field-level statement

For `K/ℚ₂` finite, `G_K = K.fixingSubgroup` is open in `G_ℚ₂` (Krull topology) and of finite
index (`G_ℚ₂` is profinite), so the previous theorem applies with `n = [G_ℚ₂ : G_K]`. -/

/-- `G_ℚ₂` is compact: the absolute Galois group of a field is profinite in the Krull topology
(spelled through `Gal(ℚ̄₂/ℚ₂)`, since `Field.absoluteGaloisGroup` is not reducible). -/
theorem compactSpace_absGalQ2 : CompactSpace AbsGalQ2 :=
  inferInstanceAs (CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]))

/-- Separate continuity of multiplication on `G_ℚ₂`, in the spelling `Subgroup`'s
finite-quotient lemma asks for. -/
theorem separatelyContinuousMul_absGalQ2 : SeparatelyContinuousMul AbsGalQ2 :=
  inferInstanceAs
    (SeparatelyContinuousMul (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]))

/-- **An open subgroup of `G_ℚ₂` has finite index** (open + compact ⇒ discrete finite quotient).
Consumers of `localEulerCharacteristic_open` can discharge its `[Finite (G ⧸ U)]` instance with
this. -/
theorem finite_quotient_of_isOpen (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2)) :
    Finite (AbsGalQ2 ⧸ U) :=
  haveI := compactSpace_absGalQ2
  haveI := separatelyContinuousMul_absGalQ2
  Subgroup.quotient_finite_of_isOpen U hU

/-- `Gal(ℚ̄₂/K) ≤ G_ℚ₂` is open for `K/ℚ₂` finite. -/
theorem isOpen_fixingSubgroup (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] :
    IsOpen (SetLike.coe (K.fixingSubgroup : Subgroup AbsGalQ2)) :=
  IntermediateField.fixingSubgroup_isOpen K

/-- **B7 over a finite extension `K/ℚ₂`** — the local Euler–Poincaré characteristic of
`G_K = Gal(ℚ̄₂/K)`.  For every finite discrete `G_K`-module `V`, the groups `Hⁱ(G_K, V)` are
finite for `i = 0, 1, 2` and

  `#H¹(G_K, V) = #H⁰(G_K, V) · #H²(G_K, V) · 2 ^ (n · v₂(#V))`,   `n = [G_ℚ₂ : G_K]`.

This is NSW VII (7.3.1) at `K`, `χ(K, A) = ‖#A‖_K`, and it is a **theorem** here: it is derived
from the `ℚ₂` axiom B7 (`GQ2.Foundations.absGalQ2_localEulerCharacteristic`) by Shapiro's lemma
at the coinduced module, so the dyadic campaign's `AX2` closes with no census change. -/
theorem absGalK_localEulerCharacteristic
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
    [hsmul : DistribMulAction ↥K.fixingSubgroup V]
    [hcont : ContinuousSMul ↥K.fixingSubgroup V] [Finite V] :
    Finite (H0 ↥K.fixingSubgroup V) ∧ Finite (H1 ↥K.fixingSubgroup V) ∧
      Finite (H2 ↥K.fixingSubgroup V) ∧
      Nat.card (H1 ↥K.fixingSubgroup V)
        = Nat.card (H0 ↥K.fixingSubgroup V) * Nat.card (H2 ↥K.fixingSubgroup V)
          * 2 ^ (K.fixingSubgroup.index * padicValNat 2 (Nat.card V)) :=
  -- the instances are threaded by hand: `↥K.fixingSubgroup` is spelled over
  -- `Gal(ℚ̄₂/ℚ₂)` while `localEulerCharacteristic_open` spells it over `AbsGalQ2`
  @localEulerCharacteristic_open K.fixingSubgroup (isOpen_fixingSubgroup K)
    (finite_quotient_of_isOpen K.fixingSubgroup (isOpen_fixingSubgroup K)) V
    inferInstance inferInstance inferInstance hsmul hcont inferInstance

end L5

end GQ2.Dyadic
