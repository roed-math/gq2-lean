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


/-! ## §4. Central elements are invisible to squares and commutators

Three laws the `Word/` kit lacks (WW6 supplied six; these are three more of the same kind).
They are what makes the two copies of the procyclic-`M` word *literally equal* on the κ⁰
carrier — the κ⁰-register face of P4's central clause, which here is a theorem rather than
the module hypothesis `CentralReplication` that the Heisenberg register needs. -/

section Central

variable {G : Type*} [Group G]

/-- Conjugation is blind to a central right factor. -/
theorem conjR_mul_central (x y c : G) (hc : ∀ z : G, Commute c z) :
    conjR x (y * c) = conjR x y := by
  calc conjR x (y * c)
      = c⁻¹ * ((y⁻¹ * x * y) * c) := by show (y * c)⁻¹ * x * (y * c) = _; group
    _ = c⁻¹ * (c * (y⁻¹ * x * y)) := by rw [(hc (y⁻¹ * x * y)).eq]
    _ = conjR x y := by rw [← mul_assoc, inv_mul_cancel, one_mul]; rfl

/-- The commutator is blind to a central factor in its left slot. -/
theorem commR_mul_central_left (x y c : G) (hc : ∀ z : G, Commute c z) :
    commR (x * c) y = commR x y := by
  calc commR (x * c) y
      = c⁻¹ * (x⁻¹ * y⁻¹ * x * (c * y)) := by show (x * c)⁻¹ * y⁻¹ * (x * c) * y = _; group
    _ = c⁻¹ * (x⁻¹ * y⁻¹ * x * (y * c)) := by rw [(hc y).eq]
    _ = c⁻¹ * ((x⁻¹ * y⁻¹ * x * y) * c) := by group
    _ = c⁻¹ * (c * (x⁻¹ * y⁻¹ * x * y)) := by rw [← (hc (x⁻¹ * y⁻¹ * x * y)).eq]
    _ = commR x y := by rw [← mul_assoc, inv_mul_cancel, one_mul]; rfl

/-- The commutator is blind to a central factor in its right slot. -/
theorem commR_mul_central_right (x y d : G) (hd : ∀ z : G, Commute d z) :
    commR x (y * d) = commR x y := by
  have hswap : x⁻¹ * (d⁻¹ * y⁻¹) = d⁻¹ * (x⁻¹ * y⁻¹) := by
    rw [← mul_assoc, ← mul_assoc, ((hd x).inv_left.inv_right).eq]
  calc commR x (y * d)
      = d⁻¹ * ((x⁻¹ * y⁻¹ * x * y) * d) := by
        show x⁻¹ * (y * d)⁻¹ * x * (y * d) = _
        rw [mul_inv_rev, show x⁻¹ * (d⁻¹ * y⁻¹) * x * (y * d)
          = x⁻¹ * (d⁻¹ * y⁻¹) * (x * (y * d)) from by group, hswap]
        group
    _ = d⁻¹ * (d * (x⁻¹ * y⁻¹ * x * y)) := by rw [(hd (x⁻¹ * y⁻¹ * x * y)).eq]
    _ = commR x y := by rw [← mul_assoc, inv_mul_cancel, one_mul]; rfl

end Central

section CentralIncl

variable {L : Type} [Group L] {c : WordCoh.TwoCocycle L}

/-- The central inclusion really is central. -/
theorem incl_commute (z : ZMod 2) (p : WordCoh.CentExt c) :
    Commute (WordCoh.CentExt.incl c z) p := by
  refine WordCoh.CentExt.ext ?_ ?_
  · show (1 : L) * WordCoh.CentExt.base p = WordCoh.CentExt.base p * 1
    rw [one_mul, mul_one]
  · show z + WordCoh.CentExt.fib p + c.κ 1 (WordCoh.CentExt.base p)
      = WordCoh.CentExt.fib p + z + c.κ (WordCoh.CentExt.base p) 1
    rw [c.κ_one_left, c.κ_one_right, add_comm z (WordCoh.CentExt.fib p)]

/-- Squares are blind to a central `𝔽₂`-factor (characteristic two). -/
theorem sq_mul_incl (p : WordCoh.CentExt c) (z : ZMod 2) :
    (p * WordCoh.CentExt.incl c z) ^ 2 = p ^ 2 := by
  rw [sq, mul_assoc, ← mul_assoc (WordCoh.CentExt.incl c z) p, (incl_commute z p).eq,
    mul_assoc, ← mul_assoc, centExt_incl_mul_self, mul_one, sq]

end CentralIncl

/-! ## §5. The plus block, and the vanishing boundary δ-letter -/

section PlusBlock

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

omit [Finite C] [Finite V] in
include hdat in
/-- `q` vanishes at the origin — `f_diag` read against `f_zero_left`. -/
theorem q_zero : q (0 : V) = 0 := by
  rw [← hdat.f_diag, hdat.f_zero_left]

omit [Finite C] [Finite V] in
include hdat in
/-- NC2's accumulated charge vanishes at a zero offset. -/
theorem powCharge_zero_vec (cc : C) (k : ℕ) : NpcJet.powCharge dat cc (0 : V) k = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show NpcJet.normSum cc j (0 : V) = 0 from
      Finset.sum_eq_zero fun i _ => smul_zero _,
    smul_zero, hdat.f_zero_left, factorSet_m_zero dat hdat, add_zero]

/-- **The boundary δ-letter dies exactly.**  `x₂` carries no primal letter at the gate-E
marking, so `δ₂` is the identity — which is why the whole `E₂^pc` block is invisible here
(the value-level face of S4.5's rider (ii)). -/
theorem evalFin_dW_two {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (hv2 : vv (Certificates.x2Idx h) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (dW h 2) = 1 := by
  rw [evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 2,
    show vv (⟨(2 : Fin 3), by omega⟩ : Fin (2 + 2 * h + 1)) = 0 from hv2,
    powCharge_zero_vec dat hdat, q_zero dat hdat, add_zero]
  rfl

/-- **The plus block's value**: `D₀²[D₀,D₁]` is the central inclusion of the plus form
`Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)` — a word identity, charge-free in both slots (the square law
and the commutator law of the slice calculus are both independent of the δ-letters' charges). -/
theorem evalFin_plusW {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (plusW h)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q (vv (Certificates.x0Idx h))
            + polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h))) := by
  rw [plusW, MCompact.evalFin_prodList_pair, PWord.evalFin_zpow, PWord.evalFin_comm,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 0,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 1,
    zpow_natCast, NpcBridge.hessSlice_sq_of_npc dat hdat hV2,
    hessSlice_commR dat hdat hV2, NpcBridge.hessSlice_zero_eq_incl, centExt_incl_mul]
  rfl

end PlusBlock

end GQ2.Dyadic.Certificates.MpcJet
