/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.WordPhaseModel

/-!
# W88-SEAM: the scalar word trace at the compact family

Ticket source: `docs/dyadic/w87-normal-note.md` §6 item 1.  W87 reduced the compact rows'
determinant clause to a single analytic statement, `wPmCompactHeadPhase`, and then reduced
*that* to the **trace seam**: the compact twin of `LSquare.QZero_eq_lUniform_graphHessianTrace`,
which says the source scalar obstruction is the sum of the evaluated word Hessians of the two
relators.  The odd proof of the seam runs through a scalar orientation `H² Γ 𝔽₂ ≃+ 𝔽₂`, and
the only word-specific ingredient of that orientation is the **word trace** `WordH² ≃+ 𝔽₂`,
which existed for the `L` family alone (`LSquare.lWordH2TraceEquiv`).

This file supplies the word trace at both compact words.

## §1 The word-generic trace equivalence

`LSquare.wordH2Trace_injective_of_pairColumn` is already word-generic: for any two-relator
family, the descended trace is injective as soon as the scalar differential hits the column
`(1,1)`.  Surjectivity is generic too.  `wPsWordH2TraceEquiv` is therefore the `L`-free
statement: a two-relator word whose scalar `d¹` contains `(1,1)` has scalar word `H²` of order
two, with the coordinate sum as the isomorphism.  `LSquare.lWordH2TraceEquiv` is the `L`
instance of it; that declaration is untouched.

## §2 The compact pair column

Every action of any group on `𝔽₂` is trivial (`GQ2.ResidueLift.htriv_zmod2`), so the
completely-split hypotheses of `heisD1_{n,m}CompactFam_tauRow_of_split`
(`Instances/N0M0ScalarStokes.lean`) are free at scalar coefficients: those theorems say both
rows of the resolved compact family read off the `tau` coordinate, so the `tau` basis vector
is carried to `(1,1)` on the nose.  This is the compact counterpart of
`LSquare.lSq_heisD1_tauColumn`, and it holds for both compact words.

## §2b The mod-2 exponent row at every odd resolver

§2 is pinned at the uniform exponent because its raw material is.  §2b removes both pins with
an argument the ticket did not anticipate: the tame row is the `tau` indicator at *every*
resolver once `q` is even, and `IsStokesEndpoint` already says the two rows sum to zero, so in
characteristic two the wild row **equals** the tame one.  No branch word is touched.  The
outcome is the whole scalar `d¹` of either compact family, at every odd resolver and every
marking: `x ↦ (x_τ, x_τ)`.

## §3 The compact word traces

`wPsNCompactWordH2TraceEquiv` and `wPsMCompactWordH2TraceEquiv`: the objects W87 §6 item 1
asked for, at every odd resolver.
-/

namespace GQ2.Dyadic.Instances.WordPhaseSeam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.LSquare

/-! ## §1 The word-generic trace equivalence -/

section Generic

variable {iota : Type*} [Fintype iota] [DecidableEq iota] {C : Type*} [Group C]
  [DistribMulAction C (ZMod 2)]

/-- **The scalar word trace of any two-relator word that hits the column `(1,1)`.**  The
`L`-free form of `LSquare.lWordH2TraceEquiv`: injectivity is
`LSquare.wordH2Trace_injective_of_pairColumn`, already word-generic, and surjectivity is the
representative `(z, 0)`. -/
def wPsWordH2TraceEquiv (c : iota → C) (w : Fin 2 → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (hpair : ∃ x, heisD1 (A := ZMod 2) c w x = ![1, 1]) :
    WordH2 c w (ZMod 2) ≃+ ZMod 2 :=
  AddEquiv.ofBijective (wordH2Trace c w hr hend)
    ⟨wordH2Trace_injective_of_pairColumn c w hr hend hpair,
      fun z ↦ ⟨QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range (![z, 0]), by
        change z + 0 = z
        exact add_zero z⟩⟩

@[simp] theorem wPsWordH2TraceEquiv_mk (c : iota → C) (w : Fin 2 → FreeGroup iota)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (hpair : ∃ x, heisD1 (A := ZMod 2) c w x = ![1, 1]) (v : Fin 2 → ZMod 2) :
    wPsWordH2TraceEquiv c w hr hend hpair
      (QuotientAddGroup.mk' (heisD1 (A := ZMod 2) c w).range v) = ∑ k, v k := rfl

end Generic

/-! ## §2 The compact pair column -/

section PairColumn

variable {α h q : ℕ} {C : Type*} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]

/-- The scalar basis vector supported on the tame generator `tau`, at the compact alphabet.
The compact twin of `LSquare.lScalarTauBasis`. -/
def wPsCompactTauBasis (h : ℕ) : Generator (2 + 2 * h) → ZMod 2 :=
  fun i ↦ if i = Generator.tau then 1 else 0

@[simp] theorem wPsCompactTauBasis_tau (h : ℕ) :
    wPsCompactTauBasis h Generator.tau = 1 := by
  simp [wPsCompactTauBasis]

/-- **The `tau` column of the uniform compact-`N` scalar differential is `(1,1)`.**  The compact
twin of `LSquare.lSq_heisD1_tauColumn`.  The completely-split hypotheses of
`heisD1_nCompactFam_tauRow_of_split` cost nothing at scalar coefficients: every action on `𝔽₂`
is trivial. -/
theorem wPs_heisD1_nCompactFam_tauColumn (t : Marking (2 + 2 * h) C)
    (hq : Even q) (hα : 1 ≤ α) :
    heisD1 (A := ZMod 2) ⇑t (nCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (wPsCompactTauBasis h) = ![1, 1] := by
  rw [heisD1_nCompactFam_tauRow_of_split (A := ZMod 2) t (by decide)
    (fun _ a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a)
    (fun a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a) hq hα]
  simp

/-- **The `tau` column of the uniform compact-`M` scalar differential is `(1,1)`.** -/
theorem wPs_heisD1_mCompactFam_tauColumn (t : Marking (2 + 2 * h) C) (hq : Even q) :
    heisD1 (A := ZMod 2) ⇑t
        (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent C)))
        (wPsCompactTauBasis h) = ![1, 1] := by
  rw [heisD1_mCompactFam_tauRow_of_split (A := ZMod 2) t (by decide)
    (fun _ a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a)
    (fun a ↦ ResidueLift.htriv_zmod2 _ a) (fun a ↦ ResidueLift.htriv_zmod2 _ a) hq]
  simp

end PairColumn

/-! ## §2b The compact mod-2 exponent row, at every odd resolver

§2 is pinned at the uniform exponent because its raw material is.  For the flexible resolver
system (§4) the same row is needed at the *quotient-level* exponent, so it has to be known at
every odd resolver and at every marking.  It is, and the proof is two lines of arithmetic on
top of the endpoint theorem: the tame row is the `tau` indicator (independently of the
resolver, once `q` is even), and `IsStokesEndpoint` says the two rows sum to zero, so in
characteristic two the wild row **equals** the tame one.  The compact twin of
`LSquare.lSqFam_heisEps_eq_of_odd`, obtained without touching the branch word at all. -/

section ExponentRow

variable {α h q e e' : ℕ}

/-- In characteristic two a vanishing sum identifies its two summands. -/
theorem wPs_eq_of_add_eq_zero : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide

/-- The traced mod-2 exponent vector of the resolved tame relator is the `tau` indicator, at
every resolver value and every even `q`.  Degree- and word-generic. -/
theorem wPs_toAdd_heisEps_tameRelW {n : ℕ} (hq : Even q) (e : ℕ) (i : Generator n) :
    Multiplicative.toAdd (heisEps i
        (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW n q)))
      = if Generator.tau = i then (1 : ZMod 2) else 0 := by
  rw [tameRelW, heisToFree, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
    PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
    conjR_eq_self_of_comm, map_inv, map_zpow]
  simp only [heisEps_of, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq, neg_zero, add_zero]

/-- **Both rows of the resolved compact-`N` family are the `tau` indicator**, at every odd
resolver, every even `q` and every `α ≥ 1`.  The wild row costs nothing: the endpoint theorem
already says the two rows sum to zero. -/
theorem wPs_toAdd_heisEps_nCompactFam (hq : Even q) (hα : 1 ≤ α) (he : Odd e) (k : Fin 2)
    (i : Generator (2 + 2 * h)) :
    Multiplicative.toAdd (heisEps i (nCompactFam α h q e k))
      = if Generator.tau = i then (1 : ZMod 2) else 0 := by
  have hzero : Multiplicative.toAdd (heisEps i (nCompactFam α h q e 0))
      = if Generator.tau = i then (1 : ZMod 2) else 0 :=
    wPs_toAdd_heisEps_tameRelW hq e i
  have hend := nCompact_isStokesEndpoint (α := α) (h := h) (q := q) (e := e) hα hq he i
  rw [Fin.sum_univ_two, hzero] at hend
  have hone : Multiplicative.toAdd (heisEps i (nCompactFam α h q e 1))
      = if Generator.tau = i then (1 : ZMod 2) else 0 :=
    wPs_eq_of_add_eq_zero _ _ hend
  fin_cases k
  · exact hzero
  · exact hone

/-- **Both rows of the resolved compact-`M` family are the `tau` indicator.**  Same argument;
the compact-`M` endpoint theorem needs no `α` hypothesis. -/
theorem wPs_toAdd_heisEps_mCompactFam (hq : Even q) (he : Odd e) (k : Fin 2)
    (i : Generator (2 + 2 * h)) :
    Multiplicative.toAdd (heisEps i (MCompact.mCompactFam α h q e k))
      = if Generator.tau = i then (1 : ZMod 2) else 0 := by
  have hzero : Multiplicative.toAdd (heisEps i (MCompact.mCompactFam α h q e 0))
      = if Generator.tau = i then (1 : ZMod 2) else 0 :=
    wPs_toAdd_heisEps_tameRelW hq e i
  have hend := MCompact.mCompact_isStokesEndpoint
    (α := α) (h := h) (q := q) (e := e) hq he i
  rw [Fin.sum_univ_two, hzero] at hend
  have hone : Multiplicative.toAdd (heisEps i (MCompact.mCompactFam α h q e 1))
      = if Generator.tau = i then (1 : ZMod 2) else 0 :=
    wPs_eq_of_add_eq_zero _ _ hend
  fin_cases k
  · exact hzero
  · exact hone

/-- All odd compact-`N` resolvers have the same mod-2 exponent matrix.  The compact twin of
`LSquare.lSqFam_heisEps_eq_of_odd`. -/
theorem wPs_heisEps_nCompactFam_eq_of_odd (hq : Even q) (hα : 1 ≤ α) (he : Odd e) (he' : Odd e')
    (k : Fin 2) (i : Generator (2 + 2 * h)) :
    heisEps i (nCompactFam α h q e k) = heisEps i (nCompactFam α h q e' k) :=
  Multiplicative.toAdd.injective
    ((wPs_toAdd_heisEps_nCompactFam hq hα he k i).trans
      (wPs_toAdd_heisEps_nCompactFam hq hα he' k i).symm)

/-- All odd compact-`M` resolvers have the same mod-2 exponent matrix. -/
theorem wPs_heisEps_mCompactFam_eq_of_odd (hq : Even q) (he : Odd e) (he' : Odd e')
    (k : Fin 2) (i : Generator (2 + 2 * h)) :
    heisEps i (MCompact.mCompactFam α h q e k)
      = heisEps i (MCompact.mCompactFam α h q e' k) :=
  Multiplicative.toAdd.injective
    ((wPs_toAdd_heisEps_mCompactFam (α := α) hq he k i).trans
      (wPs_toAdd_heisEps_mCompactFam (α := α) hq he' k i).symm)

variable {C : Type*} [Group C] [DistribMulAction C (ZMod 2)]

/-- **The scalar compact-`N` differential reads off the `tau` coordinate, twice.**  This is the
marking-free, resolver-free form of §2's tau column: the whole scalar `d¹` of the compact-`N`
family is `x ↦ (x_τ, x_τ)` at every odd resolver and every marking. -/
theorem wPs_heisD1_zmod2_nCompactFam_apply (c : Generator (2 + 2 * h) → C)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e) (x : Generator (2 + 2 * h) → ZMod 2) :
    heisD1 (A := ZMod 2) c (nCompactFam α h q e) x = ![x Generator.tau, x Generator.tau] := by
  funext k
  rw [heisD1_zmod2_apply_eq_eps]
  have hsum : ∀ i : Generator (2 + 2 * h),
      Multiplicative.toAdd (heisEps i (nCompactFam α h q e k)) * x i
        = if Generator.tau = i then x i else 0 := by
    intro i
    rw [wPs_toAdd_heisEps_nCompactFam hq hα he k i]
    split <;> simp
  rw [Finset.sum_congr rfl (fun i _ ↦ hsum i), Finset.sum_ite_eq,
    if_pos (Finset.mem_univ Generator.tau)]
  fin_cases k <;> simp

/-- **The scalar compact-`M` differential reads off the `tau` coordinate, twice.** -/
theorem wPs_heisD1_zmod2_mCompactFam_apply (c : Generator (2 + 2 * h) → C)
    (hq : Even q) (he : Odd e) (x : Generator (2 + 2 * h) → ZMod 2) :
    heisD1 (A := ZMod 2) c (MCompact.mCompactFam α h q e) x
      = ![x Generator.tau, x Generator.tau] := by
  funext k
  rw [heisD1_zmod2_apply_eq_eps]
  have hsum : ∀ i : Generator (2 + 2 * h),
      Multiplicative.toAdd (heisEps i (MCompact.mCompactFam α h q e k)) * x i
        = if Generator.tau = i then x i else 0 := by
    intro i
    rw [wPs_toAdd_heisEps_mCompactFam (α := α) hq he k i]
    split <;> simp
  rw [Finset.sum_congr rfl (fun i _ ↦ hsum i), Finset.sum_ite_eq,
    if_pos (Finset.mem_univ Generator.tau)]
  fin_cases k <;> simp

end ExponentRow

/-! ## §3 The compact word traces

The objects W87 §6 item 1 asked for.  §2b lets them be stated at **every** odd resolver and
every marking, not only at the uniform exponent and not only at a `Marking` into a finite
group: the pair column is `wPsCompactTauBasis` in all cases.  §2 is the direct instantiation
of the raw material the ticket named, and is subsumed by this. -/

section CompactTrace

variable {α h q e : ℕ} {C : Type*} [Group C] [DistribMulAction C (ZMod 2)]

/-- **The scalar word trace at the compact-`N` family**, at every odd resolver.  The
`NCompact` twin of `LSquare.lWordH2TraceEquiv`. -/
def wPsNCompactWordH2TraceEquiv (c : Generator (2 + 2 * h) → C)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift c (nCompactFam α h q e k) = 1) :
    WordH2 c (nCompactFam α h q e) (ZMod 2) ≃+ ZMod 2 :=
  wPsWordH2TraceEquiv c _ hr (nCompact_isStokesEndpoint hα hq he)
    ⟨wPsCompactTauBasis h, by
      rw [wPs_heisD1_zmod2_nCompactFam_apply c hq hα he]
      simp [wPsCompactTauBasis]⟩

/-- **The scalar word trace at the compact-`M` family**, at every odd resolver. -/
def wPsMCompactWordH2TraceEquiv (c : Generator (2 + 2 * h) → C)
    (hq : Even q) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift c (MCompact.mCompactFam α h q e k) = 1) :
    WordH2 c (MCompact.mCompactFam α h q e) (ZMod 2) ≃+ ZMod 2 :=
  wPsWordH2TraceEquiv c _ hr (MCompact.mCompact_isStokesEndpoint hq he)
    ⟨wPsCompactTauBasis h, by
      rw [wPs_heisD1_zmod2_mCompactFam_apply (α := α) c hq he]
      simp [wPsCompactTauBasis]⟩

end CompactTrace

/-! ## §4 The compact scalar orientation

With §2b and §3 the whole `L` orientation chain transposes.  Every other ingredient of
`LSquare.lScalarH2WordFlexible` and `LSquare.lScalarH2WordFlexible_surjective_of_actionImage`
is word-generic already: the engine `Count.globalModuleH2WordFlexible`, the admissibility
`Count.isAdmissibleMarkedPresentation_gammaR`, the wild-level condition
`Count.hwildLevel_gammaR`, and the resolver `Count.resolvesAt_nCompactFam`.  The only
word-specific inputs were the exponent invariance (§2b) and the word trace (§3).

The `H²` count on the continuous side is `NCompact.cardH2_of_uniformPushed` fed by
`NCompact.uniformPushedHsimp`, which is unconditional at `2 ≤ α`, `Even q`.  No Tate duality,
no Euler characteristic, no ramified certificate enters. -/

section Orientation

open GQ2.Dyadic.Count ContCoh

variable {α h q e : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction
    ((GammaR (2 + 2 * h) q (Words.nCompactW α h) : ProfiniteGrp) : Type) (ZMod 2)]
  [ContinuousSMul
    ((GammaR (2 + 2 * h) q (Words.nCompactW α h) : ProfiniteGrp) : Type) (ZMod 2)]
  [DistribMulAction C (ZMod 2)]

local notation "GammaN" => ((GammaR (2 + 2 * h) q (Words.nCompactW α h) : ProfiniteGrp) : Type)
local notation "genN" => gammaGen (2 + 2 * h) q (Words.nCompactW α h)
local notation "WN" => gammaFam (2 + 2 * h) q (Words.nCompactW α h)

/-- **The compact-`N` scalar flexible resolver system.**  The twin of
`LSquare.lScalarFlexibleResolverSystem`: at each finite level the quotient-dependent resolver
`omega2Exp (2 * exponent Q)` is odd, so §2b says its scalar differential is the fixed word's. -/
def wPsNCompactScalarFlexibleResolverSystem
    (rho : ContinuousMonoidHom GammaN C) (hq : Even q) (hα : 1 ≤ α) (he : Odd e) :
    ∀ (V : OpenNormalSubgroup GammaN)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (GammaN ⧸ V.toSubgroup) (ZMod 2) :=
        DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := ZMod 2) WN
        (fun i ↦ rho (genN i)) (nCompactFam α h q e)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (genN i)) := by
  intro V hV
  letI : DistribMulAction (GammaN ⧸ V.toSubgroup) (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
  have hlevel := twoMulExponent_ne_zero_and_even
    (WordLift (ZMod 2) (GammaN ⧸ V.toSubgroup))
  refine
    { word := nCompactFam α h q
        (omega2Exp (2 * Monoid.exponent (WordLift (ZMod 2) (GammaN ⧸ V.toSubgroup))))
      resolves := Count.resolvesAt_nCompactFam hlevel.1
        (fun x ↦ (Monoid.order_dvd_exponent x).trans (dvd_mul_left _ _)) α h q
      range_eq := ?_ }
  exact congrArg AddMonoidHom.range
    (heisD1_zmod2_eq_of_eps _ _ _ _
      (fun k i ↦ wPs_heisEps_nCompactFam_eq_of_odd hq hα
        (odd_omega2Exp hlevel.1 hlevel.2) he k i))

/-- **The compact-`N` scalar continuous-to-word `H²` map.**  The twin of
`LSquare.lScalarH2WordFlexible`, built on the word-generic engine. -/
def wPsNCompactScalarH2WordFlexible
    (rho : ContinuousMonoidHom GammaN C)
    (hcompatScalar : ∀ (g : GammaN) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e) :
    H2 GammaN (ZMod 2) →+
      WordH2 (fun i ↦ rho (genN i)) (nCompactFam α h q e) (ZMod 2) :=
  globalModuleH2WordFlexible
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (Words.nCompactW α h))
    rho hcompatScalar (fun V ↦ hwildLevel_gammaR V) (by decide)
    (wPsNCompactScalarFlexibleResolverSystem rho hq hα he)

@[simp] theorem wPsNCompactScalarH2WordFlexible_mk
    (rho : ContinuousMonoidHom GammaN C)
    (hcompatScalar : ∀ (g : GammaN) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e) (f : Z2 GammaN (ZMod 2)) :
    wPsNCompactScalarH2WordFlexible rho hcompatScalar hq hα he
        (H2mk GammaN (ZMod 2) f) =
      QuotientAddGroup.mk'
        (heisD1 (A := ZMod 2) (fun i ↦ rho (genN i)) (nCompactFam α h q e)).range
        (moduleObsFam WN genN rho hcompatScalar f) := rfl

/-- The compact-`N` scalar flexible map is injective. -/
theorem wPsNCompactScalarH2WordFlexible_injective
    (rho : ContinuousMonoidHom GammaN C)
    (hcompatScalar : ∀ (g : GammaN) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e) :
    Function.Injective (wPsNCompactScalarH2WordFlexible rho hcompatScalar hq hα he) :=
  globalModuleH2WordFlexible_injective
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (Words.nCompactW α h))
    rho hcompatScalar (fun V ↦ hwildLevel_gammaR V) (by decide)
    (wPsNCompactScalarFlexibleResolverSystem rho hq hα he)

/-- The compact-`N` scalar orientation, from map-level surjectivity and §3's word trace.  The
twin of `LSquare.lScalarH2TraceEquiv_of_surjective`; it takes no `TateDualityG`. -/
def wPsNCompactScalarH2TraceEquiv_of_surjective
    (rho : ContinuousMonoidHom GammaN C)
    (hcompatScalar : ∀ (g : GammaN) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genN i)) (nCompactFam α h q e k) = 1)
    (hsurj : Function.Surjective
      (wPsNCompactScalarH2WordFlexible rho hcompatScalar hq hα he)) :
    H2 GammaN (ZMod 2) ≃+ ZMod 2 :=
  (AddEquiv.ofBijective (wPsNCompactScalarH2WordFlexible rho hcompatScalar hq hα he)
    ⟨wPsNCompactScalarH2WordFlexible_injective rho hcompatScalar hq hα he, hsurj⟩).trans
      (wPsNCompactWordH2TraceEquiv (fun i ↦ rho (genN i)) hq hα he hr)

/-- **The representative formula.**  The compact scalar orientation reads the trace of the
global relator obstruction, exactly as `LSquare.lScalarH2TraceEquiv_of_surjective_mk` does. -/
@[simp] theorem wPsNCompactScalarH2TraceEquiv_of_surjective_mk
    (rho : ContinuousMonoidHom GammaN C)
    (hcompatScalar : ∀ (g : GammaN) (s : ZMod 2), g • s = rho g • s)
    (hq : Even q) (hα : 1 ≤ α) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genN i)) (nCompactFam α h q e k) = 1)
    (hsurj : Function.Surjective
      (wPsNCompactScalarH2WordFlexible rho hcompatScalar hq hα he))
    (f : Z2 GammaN (ZMod 2)) :
    wPsNCompactScalarH2TraceEquiv_of_surjective rho hcompatScalar hq hα he hr hsurj
        (H2mk GammaN (ZMod 2) f) =
      ∑ k, moduleObsFun WN genN rho hcompatScalar f k := rfl

end Orientation

/-! ## §5 The compact scalar orientation is an equivalence

The `H²` count on the continuous side is `NCompact.cardH2_of_uniformPushed` fed by
`NCompact.uniformPushedHsimp`, which is unconditional at `2 ≤ α`, `Even q`; the count on the
word side is §3's trace.  The flexible map is already injective, so it is bijective, and
composing with the trace gives the scalar orientation `H² Γ 𝔽₂ ≃+ 𝔽₂` on the nose.

This is the compact twin of `LSquare.lUniform_scalarH2WordFlexible_surjective_of_actionImage`
and `LSquare.lScalarH2TraceEquiv_of_surjective`.  Like them, and unlike
`LSquare.lScalarH2TraceEquiv`, it takes **no** `TateDualityG`. -/

section OrientationEquiv

open GQ2.Dyadic.Count ContCoh

variable {α h q e : ℕ} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local notation "GammaN" => ((GammaR (2 + 2 * h) q (Words.nCompactW α h) : ProfiniteGrp) : Type)
local notation "genN" => gammaGen (2 + 2 * h) q (Words.nCompactW α h)

/-- **The compact-`N` scalar flexible map is surjective**, hence bijective. -/
theorem wPsNCompactScalarH2WordFlexible_surjective
    (rho : ContinuousMonoidHom GammaN C)
    (hq : Even q) (hα : 2 ≤ α) (hq0 : q ≠ 0) (he : Odd e)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (genN i)) (nCompactFam α h q e k) = 1) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    letI : DistribMulAction GammaN (ZMod 2) := scalarActionZmodTwo GammaN
    letI : ContinuousSMul GammaN (ZMod 2) := scalarActionZmodTwo_continuousSMul GammaN
    Function.Surjective
      (wPsNCompactScalarH2WordFlexible rho (fun _ _ ↦ rfl) hq (by omega) he) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : DistribMulAction GammaN (ZMod 2) := scalarActionZmodTwo GammaN
  letI : ContinuousSMul GammaN (ZMod 2) := scalarActionZmodTwo_continuousSMul GammaN
  let f := wPsNCompactScalarH2WordFlexible rho (fun _ _ ↦ rfl) hq (by omega : 1 ≤ α) he
  have hinj : Function.Injective f :=
    wPsNCompactScalarH2WordFlexible_injective rho (fun _ _ ↦ rfl) hq (by omega) he
  letI : Finite (H2 GammaN (ZMod 2)) := Finite.of_injective f hinj
  letI : Fintype (H2 GammaN (ZMod 2)) := Fintype.ofFinite _
  letI : Fintype (WordH2 (fun i ↦ rho (genN i)) (nCompactFam α h q e) (ZMod 2)) :=
    Fintype.ofFinite _
  have hcard : Nat.card (H2 GammaN (ZMod 2)) =
      Nat.card (WordH2 (fun i ↦ rho (genN i)) (nCompactFam α h q e) (ZMod 2)) := by
    calc
      Nat.card (H2 GammaN (ZMod 2)) = 2 :=
        NCompact.cardH2_of_uniformPushed (NCompact.uniformPushedHsimp hα hq)
          (by omega) hq0 hq
      _ = Nat.card (ZMod 2) := (Nat.card_zmod 2).symm
      _ = Nat.card (WordH2 (fun i ↦ rho (genN i)) (nCompactFam α h q e) (ZMod 2)) :=
        (Nat.card_congr (wPsNCompactWordH2TraceEquiv (fun i ↦ rho (genN i)) hq
          (by omega) he hr).toEquiv).symm
  exact ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩).2

end OrientationEquiv

/-! ## Axiom audit

Every declaration in this file is pinned below.  The honest split: **all of them are std-3**
(`propext`, `Classical.choice`, `Quot.sound`) and none carries a campaign axiom.  In
particular the two compact word traces are axiom-neutral, exactly like their `L` original
`LSquare.lWordH2TraceEquiv`.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no recursion options, no
`set_option` of any kind.

**Trap check.**  No declaration here takes a `TateDualityG`, a `LocalEulerChar` or a
`RamifiedCertificate`.  The Tate-duality route to the same cardinality
(`LSquare.lScalarH2_card_eq_wordH2_of_tateDuality`) is deliberately *not* used: the word
trace is built from the explicit `tau` column, so it is duality-free on both sides. -/

section AxiomPins

#print axioms wPsWordH2TraceEquiv
#print axioms wPsWordH2TraceEquiv_mk
#print axioms wPsCompactTauBasis
#print axioms wPsCompactTauBasis_tau
#print axioms wPs_heisD1_nCompactFam_tauColumn
#print axioms wPs_heisD1_mCompactFam_tauColumn
#print axioms wPs_eq_of_add_eq_zero
#print axioms wPs_toAdd_heisEps_tameRelW
#print axioms wPs_toAdd_heisEps_nCompactFam
#print axioms wPs_toAdd_heisEps_mCompactFam
#print axioms wPs_heisEps_nCompactFam_eq_of_odd
#print axioms wPs_heisEps_mCompactFam_eq_of_odd
#print axioms wPs_heisD1_zmod2_nCompactFam_apply
#print axioms wPs_heisD1_zmod2_mCompactFam_apply
#print axioms wPsNCompactWordH2TraceEquiv
#print axioms wPsMCompactWordH2TraceEquiv
#print axioms wPsNCompactScalarFlexibleResolverSystem
#print axioms wPsNCompactScalarH2WordFlexible
#print axioms wPsNCompactScalarH2WordFlexible_mk
#print axioms wPsNCompactScalarH2WordFlexible_injective
#print axioms wPsNCompactScalarH2TraceEquiv_of_surjective
#print axioms wPsNCompactScalarH2TraceEquiv_of_surjective_mk
#print axioms wPsNCompactScalarH2WordFlexible_surjective

end AxiomPins

end

end GQ2.Dyadic.Instances.WordPhaseSeam
