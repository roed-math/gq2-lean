/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.NpcBridge
import GQ2.Dyadic.Certificates.MpcStokes

/-!
# Dyadic campaign, ticket WMP-J: the procyclic-`M` jet theorem

The `npc_cross_operators` analogue for `mpcW`, and WW4 gap item 5 on the procyclic-`M` row.
-/

namespace GQ2.Dyadic.Certificates.MpcJet

open GQ2.FoxH GQ2.SectionSix GQ2.QuadraticFp2
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates.MProcyclic

/-! ## §1. The register bridge `WordLift V C ≃* SemiProd C V` -/

section Register

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] [Finite C] [Finite V]

/-- The Fox lane's lift group and the `Word/` layer's semidirect carrier are the same group. -/
def wlEquiv : WordLift V C ≃* SemiProd C V where
  toFun p := (p.u, p.g)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite C] [Finite V] in
@[simp] theorem wlEquiv_fst (p : WordLift V C) : (wlEquiv p).1 = p.u := rfl

omit [Finite C] [Finite V] in
@[simp] theorem wlEquiv_snd (p : WordLift V C) : (wlEquiv p).2 = p.g := rfl

/-- The primal offsets of a graph-type marking, as a Fox offset vector. -/
def hessOffsets {h : ℕ} (vv : Fin (2 + 2 * h + 1) → V) : Generator (2 + 2 * h) → V
  | .sigma => 0
  | .tau => 0
  | .wild i => vv i

omit [Finite C] [Finite V] in
@[simp] theorem hessOffsets_sigma {h : ℕ} (vv : Fin (2 + 2 * h + 1) → V) :
    hessOffsets vv Generator.sigma = 0 := rfl

omit [Finite C] [Finite V] in
@[simp] theorem hessOffsets_wild {h : ℕ} (vv : Fin (2 + 2 * h + 1) → V)
    (i : Fin (2 + 2 * h + 1)) : hessOffsets vv (Generator.wild i) = vv i := rfl

/-- The lower marking of a graph-type marking: `σ ↦ s`, `τ ↦ u`, every wild letter trivial. -/
noncomputable def coreMark {h : ℕ} (s u : C) : Marking (2 + 2 * h) C :=
  Marking.ofLetters s u (fun _ => 1)

omit [Finite C] [Finite V] in
@[simp] theorem coreMark_sigma {h : ℕ} (s u : C) : (coreMark (h := h) s u).σ = s := rfl

omit [Finite C] [Finite V] in
@[simp] theorem coreMark_tau {h : ℕ} (s u : C) : (coreMark (h := h) s u).τ = u := rfl

omit [Finite C] [Finite V] in
@[simp] theorem coreMark_x {h : ℕ} (s u : C) (i : Fin (2 + 2 * h + 1)) :
    (coreMark (h := h) s u).x i = 1 := rfl

omit [Finite C] [Finite V] in
/-- **The graph-type marking is the Fox lift of its two halves.** -/
theorem hessMark_eq_foxLift {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    Certificates.hessMark s u vv
      = fun g => wlEquiv (foxLift (⇑(coreMark (h := h) s u)) (hessOffsets vv) g) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => rfl

/-- **The primal coordinate of a graph-type evaluation is the Fox derivative.**  Both sides are
`evalFin`, so no resolver hypothesis is spent: the identification is pure naturality. -/
theorem evalFin_hessMark_fst {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord (Generator (2 + 2 * h))) :
    (PWord.evalFin (Certificates.hessMark s u vv) E E₂ w).1
      = foxD (⇑(coreMark (h := h) s u)) (hessOffsets vv) E E₂ w := by
  rw [hessMark_eq_foxLift s u vv, foxD_def, foxEval_def]
  exact congrArg Prod.fst
    (PWord.map_evalFin (wlEquiv : WordLift V C ≃* SemiProd C V).toMonoidHom
      (foxLift (⇑(coreMark (h := h) s u)) (hessOffsets vv)) E E₂ w).symm

end Register

/-! ## §2. The `ω₂`-power rule on the `Word/` carrier -/

section Omega

/-- `powOmega2` form of NC3's reduction rule 1 — one rewrite from `zpowHat_omega2`. -/
theorem powOmega2_eq_pow_of_dvd_two_mul {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] {y : P} {m : ℕ} (hm : Odd m) (hdvd : orderOf y ∣ 2 * m) :
    powOmega2 y = y ^ m := by
  rw [← zpowHat_omega2, zpowHat_omega2_eq_pow_of_dvd_two_mul hm hdvd]

end Omega

/-! ## §3. The δ-letters at the graph-type κ⁰-marking -/

section Letters

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

/-- The κ⁰-lift of a graph-type marking, the object every value below is read at. -/
noncomputable def hessLift {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    Generator (2 + 2 * h) → WordCoh.CentExt (kappa0Cocycle dat hdat) :=
  WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)

omit [Finite C] [Finite V] in
@[simp] theorem hessLift_sigma {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    hessLift dat hdat (h := h) s u vv Generator.sigma = hessLine dat hdat s := rfl

omit [Finite C] [Finite V] in
@[simp] theorem hessLift_tau {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    hessLift dat hdat (h := h) s u vv Generator.tau = hessLine dat hdat u := rfl

omit [Finite C] [Finite V] in
@[simp] theorem hessLift_wild {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V)
    (i : Fin (2 + 2 * h + 1)) :
    hessLift dat hdat (h := h) s u vv (Generator.wild i) = hessSlice dat hdat (vv i) 0 := rfl

omit [Finite C] [Finite V] in
theorem hessLift_coreLetter {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (i : Fin 3) :
    hessLift dat hdat (h := h) s u vv (coreLetter h i)
      = hessSlice dat hdat (vv ⟨(i : ℕ), by omega⟩) 0 := rfl

omit [Finite C] [Finite V] in
/-- The value of `x_i τ`: a `hessElt` over the mixed base `(c_i, u)`. -/
theorem evalFin_coreLetter_mul_tau {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
        (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = NpcBridge.hessElt dat hdat (vv ⟨(i : ℕ), by omega⟩) u 0 := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one,
    hessLift_coreLetter, hessLift_tau, NpcBridge.hessSlice_mul_hessLine]

/-- **The `u_i`-letter is central.**  `(x_iτ)^{ω₂}` at a graph-type marking is the central
inclusion of NC2's accumulated charge — NC3's rules 1 and 2 meeting, on the `Word/` carrier.

Nothing here is re-derived: the order bound is WW6's transported `orderOf_hessElt_dvd_two_mul`,
the norm vanishing is NC3's `sum_pow_smul_orderOf_eq_zero`, the `ω₂`-reduction is NC3's rule 1,
and the `y^m` value is WW6's transported `hessElt_pow_eq_hessSlice`. -/
theorem evalFin_uW {h : ℕ} (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (uW h i)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (NpcJet.powCharge dat u (vv ⟨(i : ℕ), by omega⟩) (orderOf u)) := by
  have hN : ∑ j ∈ Finset.range (orderOf u), u ^ j • vv ⟨(i : ℕ), by omega⟩ = 0 :=
    sum_pow_smul_orderOf_eq_zero hVu _
  have hm : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  rw [uW, PWord.omega2Pow, PWord.evalFin_profPow_omega2,
    evalFin_coreLetter_mul_tau dat hdat s u vv E E₂ i,
    powOmega2_eq_pow_of_dvd_two_mul hu
      (NpcBridge.orderOf_hessElt_dvd_two_mul dat hdat hm hN),
    NpcBridge.hessElt_pow_eq_hessSlice dat hdat hm hN]
  rfl

/-- **The δ-letter is a Heisenberg-slice element** at offset `c_i`, with a charge that no
downstream value depends on (both the square law and the commutator law are charge-free). -/
theorem evalFin_dW {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (dW h i)
      = hessSlice dat hdat (vv ⟨(i : ℕ), by omega⟩)
          (NpcJet.powCharge dat u (vv ⟨(i : ℕ), by omega⟩) (orderOf u)
            + q (vv ⟨(i : ℕ), by omega⟩)) := by
  rw [dW, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_one, mul_one, PWord.evalFin_inv, PWord.evalFin_gen,
    evalFin_uW dat hdat s u hu hVu vv E E₂ i, hessLift_coreLetter,
    hessSlice_inv dat hdat hV2,
    show WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (NpcJet.powCharge dat u (vv ⟨(i : ℕ), by omega⟩) (orderOf u))
      = hessSlice dat hdat 0 (NpcJet.powCharge dat u (vv ⟨(i : ℕ), by omega⟩) (orderOf u)) from
      rfl,
    hessSlice_mul dat hdat, hdat.f_zero_left, add_zero, zero_add, zero_add]

end Letters

end GQ2.Dyadic.Certificates.MpcJet
