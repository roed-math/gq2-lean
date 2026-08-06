/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcTwoEntryRamifiedRow
import GQ2.Dyadic.Instances.NpcActionImageDevissage

/-!
# The procyclic-`N` ramified branch, reduced to one pairing statement

`NpcActionImageDevissage` leaves two word-specific residues for the corrected procyclic-`N` row,
`UnramifiedActionImageStokes` and `RamifiedActionImageStokes`.  This file reduces the ramified
one to a single named proposition, `NProcyclic.RamifiedTwistedPairingSeparates`: left
nondegeneracy of the traced Stokes pairing on the *twisted* normal coordinates

`A × A × (Fin h × Fin 2 → A) → (Generator (2 + 2h) → A)`,  `x₂ = B·(A⁻¹ − 1)·x₀`,

`A = S^{E(η̂)}`, `B = S^{2^r}`, of the canonical action image.

Everything first-order on that branch is proved here: the ramified Fox row is the two-entry row
`(A⁻¹ − 1)·a(x₀) − B⁻¹·a(x₂)` (`Certificates.Npc.foxD_npc_ram`), the differential is onto,
and every degree-one cocycle has a unique twisted normal representative
(`NpcTwoEntryRamifiedRow`).  The residual statement is exactly the *second-order* evaluation of
`npcW` on twisted normal offsets.

⚠ **Why that second-order value is not the compact one.**  On a compact even row the ramified
normal cochains vanish at `x₂`, so the `ω₂`-block `(x₂τ)^{ω₂}` is second-order *pure* and
contributes nothing.  Here `x₂ = B(A⁻¹ − 1)x₀` is **not** zero, so that block contributes its
own central charge

`Z_e = Σ_{0 ≤ j < k < e} (T^j·y₂)(T^k·x₂) = y₂((N_{(e+1)/2}(T²) + 1)·x₂)`  (`e = E(ω₂)`, odd),

which is the geometric sum of `T²` truncated at `(e+1)/2` terms.  It is *not* killed by
fixed-point-freeness: the full norm `N_n(T)` vanishes, but this truncation does not — at `e = 3`
it is the single term `y₂(T²x₂)`, nonzero already on `𝔽₄` with `τ` of order `3`.  So the
procyclic ramified second-order row carries a genuinely new atom, absent from every compact row
and from every existing `heisZ_npc_*` (all of which assume `τ` acts trivially).  That atom is the
whole remaining obstruction on this branch.
-/

namespace GQ2.Dyadic.NProcyclic

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage
open GQ2.Dyadic.Certificates.MProcyclic

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The uniform resolver of the two-valued procyclic family -/

/-- The two-valued procyclic resolver lifts `ω₂` at the uniform Heisenberg level: its `ω₂`-value
is the same `omega2Exp (4 * exponent C)` the compact rows use, and the `η̂`-value is irrelevant
to `ResolverLifts`. -/
theorem resolverLifts_npcResolver_wordLift {C A : Type*} [Group C] [Finite C] [AddCommGroup A]
    [DistribMulAction C A] (hA₂ : ∀ a : A, a + a = 0) (d : EtaData) :
    ResolverLifts (npcResolver (4 * Monoid.exponent C) d) (WordLift A C) := by
  intro p
  rw [npcResolver_omega2, zpow_natCast]
  apply powOmega2_pow_eq p
  · exact (WordLift.orderOf_dvd_two_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) p).trans ⟨2, by ring⟩
  · exact (fourMulExponent_ne_zero_and_even C).1

/-! ## The ramified procyclic-`N` row is a two-entry row -/

set_option maxHeartbeats 800000 in
/-- **The complete ramified first differential of the corrected procyclic-`N` family.**  The tame
row is the arbitrary-`q` one; the wild row is the two-entry row with the `x₀`-coboundary of
`A⁻¹ = S^{−E(η̂)}` and the invertible `x₂`-pivot `B⁻¹ = S^{−2^r}`. -/
theorem isTwoEntryRamifiedRow_npc {alpha r h q : ℕ} {d : EtaData}
    {C A : Type*} [Group C] [Finite C] [AddCommGroup A] [Finite A] [DistribMulAction C A]
    (t : Marking (2 + 2 * h) C) (hA₂ : ∀ a : A, a + a = 0)
    (ht : t.TameRelAt q)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (a : A), t.x i • a = a)
    (hτfpf : ∀ a : A, t.τ • a = a → a = 0)
    (hTodd : ∀ a : A, powOmega2 t.τ • a = a) (hα : 1 ≤ alpha) :
    IsTwoEntryRamifiedRow t (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) q
      ((t.σ ^ (npcResolver (4 * Monoid.exponent C) d) d.toZhat)⁻¹)
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹) A := by
  intro x
  funext k
  fin_cases k
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
          (tameRelW (2 + 2 * h) q))).a =
        t.σ⁻¹ • (x .tau + t.τ • x .sigma - x .sigma)
          - ∑ i ∈ Finset.range q, (t.τ ^ i) • x .tau
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (resolverLifts_npcResolver_wordLift hA₂ d),
      Certificates.foxD_tameRelW_of_tameRel t _ _ ht]
  · change
      (FreeGroup.lift (heisGen (⇑t) x 0)
        (heisToFree (npcResolver (4 * Monoid.exponent C) d) (fun _ ↦ (0 : ℤ))
          (Words.Npc.npcW alpha r h d))).a =
        ((t.σ ^ (npcResolver (4 * Monoid.exponent C) d) d.toZhat)⁻¹ • x (coreLetter h 0)
            - x (coreLetter h 0))
          - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)
    rw [← heisEvalZ_eq_lift,
      heisEvalZ_a_eq_foxD (resolverLifts_npcResolver_wordLift hA₂ d),
      Certificates.Npc.foxD_npc_ram t _ _ hA₂ hwild hτfpf hTodd hα d]

/-! ## The residual input, and the branch it closes -/

/-- **The residual procyclic-`N` ramified input.**  On every simple elementary coefficient with
`tau` fixed-point free, the traced pairing of the corrected procyclic-`N` family at the uniform
level separates the nonzero *twisted* normal coordinates. -/
def RamifiedTwistedPairingSeparates (alpha r h q : ℕ) (d : EtaData) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) →
    IsSimpleModTwo ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) .tau • m = m → m = 0) →
    ∀ p : M × M × (Fin h × Fin 2 → M), p ≠ 0 →
      ∃ rr : ElemDual M × ElemDual M × (Fin h × Fin 2 → ElemDual M),
        heisEta1 (actionImageGenerators (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)
            (resolvedFamily alpha r h q d
              (4 * Monoid.exponent
                (ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)))
            (evenTwistedNormal h
              ((actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M).σ
                ^ (npcResolver (4 * Monoid.exponent
                    (ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)) d) d.toZhat)⁻¹
              ((actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M).σ
                ^ ((2 : ℤ) ^ r))⁻¹ p.1 p.2.1 p.2.2)
            (evenTwistedNormal h
              ((actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M).σ
                ^ (npcResolver (4 * Monoid.exponent
                    (ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)) d) d.toZhat)⁻¹
              ((actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M).σ
                ^ ((2 : ℤ) ^ r))⁻¹ rr.1 rr.2.1 rr.2.2) ≠ 0

set_option maxHeartbeats 3200000 in
/-- **The procyclic-`N` ramified branch, from the residual pairing statement.**  Every
first-order ingredient is discharged; `hsep` is exactly left nondegeneracy of the traced pairing
on the twisted normal coordinates, whose evaluation is the missing second-order row. -/
theorem ramifiedActionImageStokes_of_separation {alpha r h q : ℕ} {d : EtaData}
    (hα : 1 ≤ alpha) (hqe : Even q) (hsep : RamifiedTwistedPairingSeparates alpha r h q d) :
    RamifiedActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτfpf
  let C₀ := ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  let t := actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  let w₀ := resolvedFamily alpha r h q d (4 * Monoid.exponent C₀)
  have hlv := levelResolver (alpha := alpha) (r := r) (h := h) (q := q) d hα hqe
  have hres₀ : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d)) w₀
      (HeisLift M C₀) := hlv.heis hM₂
  have hend : IsStokesEndpoint w₀ :=
    hlv.endpoint _ (fourMulExponent_ne_zero_and_even C₀).1
      (fourMulExponent_ne_zero_and_even C₀).2
  letI : TopologicalSpace (WordLift M C₀) := ⊥
  letI : DiscreteTopology (WordLift M C₀) := ⟨rfl⟩
  have hresWord : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d)) w₀
      (WordLift M C₀) := by
    let incl : ContinuousMonoidHom (WordLift M C₀) (HeisLift M C₀) :=
      ⟨heisPrim (A := M) (C := C₀), continuous_of_discreteTopology⟩
    exact hres₀.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift ⇑t (w₀ k) = 1 := fun k ↦
    lower_rel (A := M) (actionImageHom (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)
      (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      hresWord k
  have ht : t.TameRelAt q := actionImage_tameRelAt
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτfpf' : ∀ m : M, t.τ • m = m → m = 0 := fun m hm ↦ hτfpf m hm
  have hTodd : ∀ m : M, powOmega2 t.τ • m = m :=
    actionImage_tau_powOmega2_smul_trivial hM₂ hsimple
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  have hwildD : ∀ (i : Fin (2 + 2 * h + 1)) (lam : ElemDual M), t.x i • lam = lam :=
    fun i lam ↦ elemDual_smul_eq_self (hwild i) lam
  have hτfpfD : ∀ lam : ElemDual M, t.τ • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hτfpf' lam hlam
  have hToddD : ∀ lam : ElemDual M, powOmega2 t.τ • lam = lam :=
    fun lam ↦ elemDual_smul_eq_self hTodd lam
  exact evenTwoEntryRamifiedStokesDuality_of_row _ _ t w₀ hM₂ hr hend
    (isTwoEntryRamifiedRow_npc (d := d) (r := r) t hM₂ ht hwild hτfpf' hTodd hα)
    (isTwoEntryRamifiedRow_npc (A := ElemDual M) (d := d) (r := r) t hM₂D ht hwildD hτfpfD
      hToddD hα)
    hwild hτfpf' (hsep M hM₂ hsimple hτfpf)

end

end GQ2.Dyadic.NProcyclic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclic.resolverLifts_npcResolver_wordLift
#print axioms GQ2.Dyadic.NProcyclic.isTwoEntryRamifiedRow_npc
#print axioms GQ2.Dyadic.NProcyclic.ramifiedActionImageStokes_of_separation

end AxiomAudit
