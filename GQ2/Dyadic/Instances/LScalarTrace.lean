/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.LComparisonSquares
import GQ2.Dyadic.Instances.LSourceComposition

/-!
# The canonical scalar trace orientation for the L source

At scalar coefficients the word differential depends only on the mod-`2` exponent vector of
the resolved words.  Hence all odd L resolvers induce the same scalar differential, even when
only quotient-dependent resolvers are available.  This gives the flexible scalar `H²` map
without asking for a fixed-target scalar resolver.

For the two-relator L family, the `tau` column of the scalar differential is `(1,1)` whenever
`q` is even and `e` is odd.  The sum of the two relator coordinates therefore descends to an
equivalence `WordH² ≃ ZMod 2`.  Composing this trace with the flexible scalar map gives the
canonical source orientation and proves `ScalarTraceCompatible` by construction.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH GQ2.SectionEight
open ContCoh SectionSeven
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.LiftingDualityG
open GQ2.Dyadic.Words GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates.LSq

/-! ## The word trace -/

section WordTrace

variable {iota rel C : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]
  [Group C] [DistribMulAction C (ZMod 2)]

/-- The sum of relator coordinates, descended to scalar word `H²`. -/
noncomputable def wordH2Trace (c : iota → C) (w : rel → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    WordH2 c w (ZMod 2) →+ ZMod 2 :=
  QuotientAddGroup.lift (heisD1 (A := ZMod 2) c w).range
    (AddMonoidHom.mk' (fun v ↦ ∑ k, v k) (fun v v' ↦ by
      simp only [Pi.add_apply, Finset.sum_add_distrib])) (by
        intro v hv
        obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hv
        exact sum_heisD1_zmod2 hr hend x)

@[simp] theorem wordH2Trace_mk (c : iota → C) (w : rel → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (v : rel → ZMod 2) :
    wordH2Trace c w hr hend
      (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range v) = ∑ k, v k := rfl

end WordTrace

/-! ## Scalar differentials only see mod-2 exponent vectors -/

section ScalarDifferential

variable {iota rel C D : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]
  [Group C] [DistribMulAction C (ZMod 2)]
  [Group D] [DistribMulAction D (ZMod 2)]

/-- At scalar coefficients the first word differential is the mod-`2` exponent matrix. -/
theorem heisD1_zmod2_apply_eq_eps (c : iota → C) (w : rel → FreeGroup iota)
    (x : iota → ZMod 2) (k : rel) :
    heisD1 (A := ZMod 2) c w x k =
      ∑ i, Multiplicative.toAdd (heisEps i (w k)) * x i := by
  rw [heisD1_apply]
  have aux : ∀ r : FreeGroup iota,
      (FreeGroup.lift (heisGen c x 0) r).a =
        ∑ i, Multiplicative.toAdd (heisEps i r) * x i := by
    intro r
    induction r using FreeGroup.induction_on with
    | C1 => simp [heisEps]
    | of j => simp [FreeGroup.lift_apply_of, heisEps]
    | inv_of r ih =>
        rw [map_inv, HeisLift.inv_a, heisWord_g, ih, smul_zmod2]
        simp only [map_inv, toAdd_inv, neg_mul, Finset.sum_neg_distrib]
    | mul r s ihr ihs =>
        rw [map_mul, HeisLift.mul_a, heisWord_g, smul_zmod2, ihr, ihs]
        simp only [map_mul, toAdd_mul, add_mul, Finset.sum_add_distrib]
  exact aux (w k)

/-- Equal mod-`2` exponent vectors give equal scalar differentials, independently of the base
group and marking. -/
theorem heisD1_zmod2_eq_of_eps
    (c : iota → C) (w : rel → FreeGroup iota)
    (d : iota → D) (v : rel → FreeGroup iota)
    (heps : ∀ k i, heisEps i (w k) = heisEps i (v k)) :
    heisD1 (A := ZMod 2) c w = heisD1 (A := ZMod 2) d v := by
  apply AddMonoidHom.ext
  intro x
  funext k
  rw [heisD1_zmod2_apply_eq_eps, heisD1_zmod2_apply_eq_eps]
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun z ↦ Multiplicative.toAdd z * x i) (heps k i)

end ScalarDifferential

/-! ## Odd L resolvers have the same scalar differential -/

section LParity

variable {h q e e' : ℕ}

/-- The tame L word has the same mod-`2` exponent vector at every integer resolver. -/
theorem lSqFam_zero_heisEps_eq
    (i : Generator (2 * h + 1)) :
    heisEps i (lSqFam h q e 0) = heisEps i (lSqFam h q e' 0) := by
  change heisEps i (heisToFree (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
      (tameRelW (2 * h + 1) q)) =
    heisEps i (heisToFree (fun _ ↦ (e' : ℤ)) (fun _ ↦ (e' : ℤ))
      (tameRelW (2 * h + 1) q))
  rw [tameRelW, heisToFree, heisToFree,
    PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv, PWord.evalZ_zpow,
    PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR, conjR_eq_self_of_comm,
    map_inv, map_zpow, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
    conjR_eq_self_of_comm, map_inv, map_zpow]

/-- The wild L word has the same mod-`2` exponent vector at all odd resolvers. -/
theorem lSqFam_one_heisEps_eq (he : Odd e) (he' : Odd e')
    (i : Generator (2 * h + 1)) :
    heisEps i (lSqFam h q e 1) = heisEps i (lSqFam h q e' 1) := by
  have hform : ∀ n : ℕ,
      heisEps i (lSqFam h q n 1) =
        (heisEps i (FreeGroup.of (coreLetter h 0)))⁻¹ *
          ((heisEps i (FreeGroup.of (coreLetter h 0)) ^ (-3 : ℤ) *
              heisEps i (FreeGroup.of Generator.tau)) ^ (n : ℤ) *
            heisEps i (FreeGroup.of (coreLetter h 1)) ^ (2 : ℤ)) := by
    intro n
    rw [lSqFam_one, heisToFree, evalZ_lSqW]
    simp only [lSqCore, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_mul, heisEps_lSqHandles, mul_one, map_mul, map_mul, map_mul,
      PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, map_inv,
      map_conjR, conjR_eq_self_of_comm, PWord.omega2Pow, PWord.evalZ_profPow, map_zpow,
      PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one,
      mul_one, map_mul, map_zpow, PWord.evalZ_zpow, PWord.evalZ_gen, map_zpow,
      PWord.evalZ_comm, monoidHom_commR_eq_one, mul_one]
  rw [hform e, hform e']
  have hez : Odd (e : ℤ) := by exact_mod_cast he
  have hez' : Odd (e' : ℤ) := by exact_mod_cast he'
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_zpow]
  rw [zsmul_zmod2_odd hez, zsmul_zmod2_odd hez']

/-- All odd L families have the same mod-`2` exponent matrix. -/
theorem lSqFam_heisEps_eq_of_odd (he : Odd e) (he' : Odd e') :
    ∀ k i, heisEps i (lSqFam h q e k) = heisEps i (lSqFam h q e' k) := by
  intro k i
  fin_cases k
  · exact lSqFam_zero_heisEps_eq i
  · exact lSqFam_one_heisEps_eq he he' i

end LParity

/-! ## The visible `(1,1)` scalar column and trace equivalence -/

section LTraceEquiv

variable {h q e : ℕ} {C : Type*} [Group C] [DistribMulAction C (ZMod 2)]

/-- The tame relator's `tau` exponent is odd when `q` is even. -/
theorem lSqFam_zero_tau_eps (hq : Even q) :
    Multiplicative.toAdd
      (heisEps (Generator.tau : Generator (2 * h + 1)) (lSqFam h q e 0)) = 1 := by
  change Multiplicative.toAdd
    (heisEps (Generator.tau : Generator (2 * h + 1))
      (heisToFree (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))
        (tameRelW (2 * h + 1) q))) = 1
  rw [tameRelW, heisToFree, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
    conjR_eq_self_of_comm, map_inv, map_zpow, toAdd_mul, toAdd_inv, toAdd_zpow]
  simp only [heisEps, FreeGroup.lift_apply_of, if_pos, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq]
  simp

/-- The wild relator's `tau` exponent is odd at every odd resolver. -/
theorem lSqFam_one_tau_eps (hq : Even q) (he : Odd e) :
    Multiplicative.toAdd
      (heisEps (Generator.tau : Generator (2 * h + 1)) (lSqFam h q e 1)) = 1 := by
  have hend := lSq_isStokesEndpoint (h := h) hq he
    (Generator.tau : Generator (2 * h + 1))
  rw [Fin.sum_univ_two, lSqFam_zero_tau_eps hq] at hend
  let z := Multiplicative.toAdd
    (heisEps (Generator.tau : Generator (2 * h + 1)) (lSqFam h q e 1))
  change 1 + z = 0 at hend
  calc
    z = 0 + z := (zero_add z).symm
    _ = (1 + 1) + z := by rw [CharTwo.add_self_eq_zero]
    _ = 1 + (1 + z) := add_assoc _ _ _
    _ = 1 + 0 := by rw [hend]
    _ = 1 := add_zero _

/-- The scalar basis vector supported on the tame generator `tau`. -/
def lScalarTauBasis : Generator (2 * h + 1) → ZMod 2 :=
  fun i ↦ if i = Generator.tau then 1 else 0

/-- At even `q` and odd `e`, the `tau` column of the two-relator scalar differential is
`(1,1)`. -/
theorem lSq_heisD1_tauColumn (c : Generator (2 * h + 1) → C)
    (hq : Even q) (he : Odd e) :
    heisD1 (A := ZMod 2) c (lSqFam h q e) lScalarTauBasis = ![1, 1] := by
  funext k
  rw [heisD1_zmod2_apply_eq_eps]
  rw [Finset.sum_eq_single Generator.tau]
  · fin_cases k
    · simpa [lScalarTauBasis] using lSqFam_zero_tau_eps (h := h) (e := e) hq
    · simpa [lScalarTauBasis] using lSqFam_one_tau_eps (h := h) hq he
  · intro i _ hi
    simp [lScalarTauBasis, hi]
  · simp

/-- If the two-relator scalar differential contains the column `(1,1)`, the descended trace
is injective. -/
theorem wordH2Trace_injective_of_pairColumn
    {iota : Type*} [Fintype iota] [DecidableEq iota]
    (c : iota → C) (w : Fin 2 → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (hpair : ∃ x, heisD1 (A := ZMod 2) c w x = ![1, 1]) :
    Function.Injective (wordH2Trace c w hr hend) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  induction y using QuotientAddGroup.induction_on with
  | H v =>
      rw [QuotientAddGroup.eq_zero_iff]
      change (∑ k, v k) = 0 at hy
      rw [Fin.sum_univ_two] at hy
      have hv10 : v 1 = v 0 := by
        calc
          v 1 = 0 + v 1 := (zero_add _).symm
          _ = (v 0 + v 0) + v 1 := by rw [CharTwo.add_self_eq_zero]
          _ = v 0 + (v 0 + v 1) := add_assoc _ _ _
          _ = v 0 + 0 := by rw [hy]
          _ = v 0 := add_zero _
      rcases ZMod.eq_zero_or_eq_one (v 0) with hv0 | hv1
      · have hv : v = 0 := by
          funext k
          fin_cases k <;> simp [hv0, hv10]
        rw [hv]
        exact zero_mem _
      · obtain ⟨x, hx⟩ := hpair
        have hv : v = ![1, 1] := by
          funext k
          fin_cases k <;> simp [hv1, hv10]
        rw [hv]
        exact AddMonoidHom.mem_range.mpr ⟨x, hx⟩

/-- The scalar word trace is an additive equivalence for the L family. -/
noncomputable def lWordH2TraceEquiv (c : Generator (2 * h + 1) → C)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift c (lSqFam h q e k) = 1) :
    WordH2 c (lSqFam h q e) (ZMod 2) ≃+ ZMod 2 :=
  AddEquiv.ofBijective (wordH2Trace c (lSqFam h q e) hr (lSq_isStokesEndpoint hq he))
    ⟨wordH2Trace_injective_of_pairColumn c (lSqFam h q e) hr
      (lSq_isStokesEndpoint hq he) ⟨lScalarTauBasis, lSq_heisD1_tauColumn c hq he⟩,
      fun z ↦ ⟨QuotientAddGroup.mk'
        (heisD1 (A := ZMod 2) c (lSqFam h q e)).range (![z, 0]), by
          change z + 0 = z
          exact add_zero z⟩⟩

@[simp] theorem lWordH2TraceEquiv_mk (c : Generator (2 * h + 1) → C)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift c (lSqFam h q e k) = 1)
    (v : Fin 2 → ZMod 2) :
    lWordH2TraceEquiv c hq he hr
      (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c (lSqFam h q e)).range v) =
      ∑ k, v k := rfl

end LTraceEquiv

/-! ## The scalar flexible map without a fixed-target resolver -/

section LScalarMap

variable {h q e : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (ZMod 2)]
  [ContinuousSMul ((gamma h q : Type)) (ZMod 2)]
  [DistribMulAction ((gamma h q : Type)) (MuN 2)]
  [ContinuousSMul ((gamma h q : Type)) (MuN 2)]
  [DistribMulAction C (ZMod 2)]

local notation "GammaL" => (gamma h q : Type)
local notation "genL" => gammaGen (2 * h + 1) q (lSqW h)
local notation "WL" => gammaFam (2 * h + 1) q (lSqW h)
local notation "wL" => lSqFam h q e

/-- Quotient-dependent odd scalar resolvers have the same differential as the fixed odd L word.
This is the scalar flexible resolver system; unlike the module-valued system it needs no
fixed-target resolver. -/
noncomputable def lScalarFlexibleResolverSystem
    (rho : ContinuousMonoidHom GammaL C) (he : Odd e) :
    ∀ (V : OpenNormalSubgroup GammaL)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (GammaL ⧸ V.toSubgroup) (ZMod 2) :=
        DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := ZMod 2) WL
        (fun i ↦ rho (genL i)) wL
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i)) := by
  intro V hV
  let rhoV := quotientActionHom rho V hV
  letI : DistribMulAction (GammaL ⧸ V.toSubgroup) (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) rhoV
  let Q := WordLift (ZMod 2) (GammaL ⧸ V.toSubgroup)
  let N := 2 * Monoid.exponent Q
  have hlevel := twoMulExponent_ne_zero_and_even Q
  let eV := omega2Exp N
  have heV : Odd eV := odd_omega2Exp hlevel.1 hlevel.2
  let word := lSqFam h q eV
  refine
    { word := word
      resolves := resolvesAt_lSqFam hlevel.1 (fun x ↦
        (Monoid.order_dvd_exponent x).trans (dvd_mul_left _ _)) h q
      range_eq := ?_ }
  have hd :
      heisD1 (A := ZMod 2)
          (fun i ↦ QuotientGroup.mk' V.toSubgroup (genL i)) word =
        heisD1 (A := ZMod 2) (fun i ↦ rho (genL i)) wL :=
    heisD1_zmod2_eq_of_eps _ _ _ _ (lSqFam_heisEps_eq_of_odd heV he)
  exact congrArg AddMonoidHom.range hd

/-- The scalar continuous-to-word `H²` map at a fixed odd L word, constructed without a
fixed-target scalar resolver. -/
noncomputable def lScalarH2WordFlexible
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e) :
    H2 GammaL (ZMod 2) →+
      WordH2 (fun i ↦ rho (genL i)) wL (ZMod 2) :=
  globalModuleH2WordFlexible
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
    rho hcompatScalar (fun V ↦ hwildLevel_gammaR V) (by decide)
      (lScalarFlexibleResolverSystem rho he)

@[simp] theorem lScalarH2WordFlexible_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e) (f : Z2 GammaL (ZMod 2)) :
    lScalarH2WordFlexible rho hcompatScalar he (H2mk GammaL (ZMod 2) f) =
      QuotientAddGroup.mk'
        (heisD1 (A := ZMod 2) (fun i ↦ rho (genL i)) wL).range
        (moduleObsFam WL genL rho hcompatScalar f) := rfl

/-- The resolver-free scalar flexible map is injective. -/
theorem lScalarH2WordFlexible_injective
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (he : Odd e) :
    Function.Injective (lScalarH2WordFlexible rho hcompatScalar he) :=
  globalModuleH2WordFlexible_injective
    (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h))
    rho hcompatScalar (fun V ↦ hwildLevel_gammaR V) (by decide)
      (lScalarFlexibleResolverSystem rho he)

/-- Tate duality and the explicit word trace give equal cardinalities on the two sides of the
scalar flexible map. -/
theorem lScalarH2_card_eq_wordH2_of_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s) :
    Nat.card (H2 GammaL (ZMod 2)) =
      Nat.card (WordH2 (fun i ↦ rho (genL i)) wL (ZMod 2)) := by
  calc
    Nat.card (H2 GammaL (ZMod 2)) = 2 := card_H2_zmod2_eq_twoG D htriv
    _ = Nat.card (ZMod 2) := (Nat.card_zmod 2).symm
    _ = Nat.card (WordH2 (fun i ↦ rho (genL i)) wL (ZMod 2)) :=
      (Nat.card_congr (lWordH2TraceEquiv (fun i ↦ rho (genL i)) hq he hr).toEquiv).symm

/-- The scalar flexible map upgraded to an equivalence by Tate duality and the explicit trace
cardinality. -/
noncomputable def lScalarModuleH2EquivFlexible_of_tateDuality
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s) :
    H2 GammaL (ZMod 2) ≃+
      WordH2 (fun i ↦ rho (genL i)) wL (ZMod 2) :=
  AddEquiv.ofBijective (lScalarH2WordFlexible rho hcompatScalar he) (by
    let f := lScalarH2WordFlexible rho hcompatScalar he
    have hinj := lScalarH2WordFlexible_injective rho hcompatScalar he
    letI : Finite (H2 GammaL (ZMod 2)) := Finite.of_injective f hinj
    letI : Fintype (H2 GammaL (ZMod 2)) := Fintype.ofFinite _
    letI : Fintype (WordH2 (fun i ↦ rho (genL i)) wL (ZMod 2)) := Fintype.ofFinite _
    exact (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using
        lScalarH2_card_eq_wordH2_of_tateDuality rho hq he hr D htriv⟩)

/-- The canonical scalar source orientation: flexible obstruction, then word trace. -/
noncomputable def lScalarH2TraceEquiv
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s) :
    H2 GammaL (ZMod 2) ≃+ ZMod 2 :=
  (lScalarModuleH2EquivFlexible_of_tateDuality rho hcompatScalar hq he hr D htriv).trans
    (lWordH2TraceEquiv (fun i ↦ rho (genL i)) hq he hr)

/-- Representative formula: the canonical scalar orientation reads the trace of the global
relator obstruction. -/
@[simp] theorem lScalarH2TraceEquiv_mk
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s)
    (f : Z2 GammaL (ZMod 2)) :
    lScalarH2TraceEquiv rho hcompatScalar hq he hr D htriv
        (H2mk GammaL (ZMod 2) f) =
      ∑ k, moduleObsFun WL genL rho hcompatScalar f k := rfl

/-- The canonical scalar orientation satisfies exactly the compatibility required by both edge
comparison squares. -/
theorem lScalarTraceCompatible
    (rho : ContinuousMonoidHom GammaL C)
    (hcompatScalar : ∀ (g : GammaL) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genL i)) (wL k) = 1)
    (D : TateDualityG GammaL 2)
    (htriv : ∀ (g : GammaL) (s : ZMod 2), g • s = s) :
    ScalarTraceCompatible WL genL rho hcompatScalar
      (lScalarH2TraceEquiv rho hcompatScalar hq he hr D htriv) :=
  fun f ↦ lScalarH2TraceEquiv_mk rho hcompatScalar hq he hr D htriv f

end LScalarMap

end

end GQ2.Dyadic.LSquare
