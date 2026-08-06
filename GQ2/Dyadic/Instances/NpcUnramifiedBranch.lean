/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.N0M0CompactBranches
import GQ2.Dyadic.Instances.NpcUnramifiedPairing

/-!
# The generic unramified sub-branch of the procyclic-`N` row

`NpcUnramifiedPairing` discharges left nondegeneracy of the traced pairing on `Φ`-normal
coordinates.  This file feeds it to `stokesDuality_npc_unramified_generic` at the canonical
action image and closes the **generic** unramified sub-branch, where `sigma` acts without
nonzero fixed vectors.

The branch arithmetic of `NpcUnramifiedProcyclic` is consumed here, and only here:

* `actionImage_unramified_sigma_etaPow` gives `A = σ^{η̂} = σ` — this is what makes the
  operator `A⁻¹` fixed-point free and hence `Φ = (1 − B⁻¹)⁻¹(1 − A⁻¹)` bijective;
* `actionImage_unramified_sigmaPow_fixedPointFree` gives the same for `B = σ^{2^r}`.

What is left of the `tau`-unramified residue is the *scalar* sub-branch, where `sigma` acts
trivially and hence — the action image being procyclic — the whole action image does.  It is
isolated below as `NProcyclic.ScalarActionImageStokes` and settled in `NpcUnramifiedScalar`.
-/

namespace GQ2.Dyadic.NProcyclicUnram

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Npc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.Npc
open GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

set_option maxHeartbeats 3200000 in
/-- **The generic unramified sub-branch of the corrected procyclic-`N` row, unconditionally.**
On a simple `tau`-unramified coefficient with `sigma` fixed-point free, the `Φ`-normal
coordinates freely parametrise middle cohomology, the ends are acyclic, and the traced pairing
separates through the two invertible off-diagonal operators `Φ` and `Φ_D`. -/
theorem stokesDuality_actionImage_generic {alpha r h q : ℕ} {d : EtaData}
    (hα : 2 ≤ alpha) (hqe : Even q)
    (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0)
    (hsimple : IsSimpleModTwo ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M)
    (hτ : ∀ m : M, gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) .tau • m = m)
    (hσfpf : ∀ m : M,
      (actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M).σ • m = m → m = 0) :
    StokesDuality (actionImageGenerators (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)
      (NProcyclic.resolvedFamily alpha r h q d
        (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M))) M := by
  let C₀ := ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  let t := actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M
  let w₀ := NProcyclic.resolvedFamily alpha r h q d (4 * Monoid.exponent C₀)
  have hlv := NProcyclic.levelResolver (alpha := alpha) (r := r) (h := h) (q := q) d
    (by omega) hqe
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
  have hwild : ∀ (i : Fin (2 + 2 * h + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hτ' : ∀ m : M, t.τ • m = m := fun m ↦ hτ m
  have hM₂D : ∀ lam : ElemDual M, lam + lam = 0 := fun lam ↦ lam.add_self_eq_zero
  -- `A = σ`: the whole `η̂`-datum disappears from the unramified row.
  have hAeq : t.σ ^ (npcResolver (4 * Monoid.exponent C₀) d) d.toZhat = t.σ :=
    actionImage_unramified_sigma_etaPow hM₂ hsimple hτ d
      (fourMulExponent_ne_zero_and_even C₀).1
      ((Monoid.order_dvd_exponent t.σ).trans ⟨4, by ring⟩)
  have hBfpf : ∀ m : M, ((t.σ ^ ((2 : ℤ) ^ r)) : C₀) • m = m → m = 0 :=
    actionImage_unramified_sigmaPow_fixedPointFree hM₂ hsimple hτ hσfpf r
  have hufpf : ∀ m : M, ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ : C₀) • m = m → m = 0 := fun m hm ↦
    hBfpf m (inv_smul_eq_iff.mp hm).symm
  have hufpfD : ∀ lam : ElemDual M, ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ : C₀) • lam = lam → lam = 0 :=
    fun lam hlam ↦ elemDual_fpf hufpf lam hlam
  have hgfpf : ∀ m : M,
      ((t.σ ^ (npcResolver (4 * Monoid.exponent C₀) d) d.toZhat)⁻¹ : C₀) • m = m → m = 0 := by
    rw [hAeq]
    exact fun m hm ↦ hσfpf m (inv_smul_eq_iff.mp hm).symm
  have hgfpfD : ∀ lam : ElemDual M,
      ((t.σ ^ (npcResolver (4 * Monoid.exponent C₀) d) d.toZhat)⁻¹ : C₀) • lam = lam →
        lam = 0 := fun lam hlam ↦ elemDual_fpf hgfpf lam hlam
  refine stokesDuality_npc_unramified_generic t hM₂ hqe (by omega) hwild hτ' hσfpf hufpf d
    (4 * Monoid.exponent C₀)
    (NProcyclic.resolverLifts_npcResolver_wordLift hM₂ d)
    (NProcyclic.resolverLifts_npcResolver_wordLift hM₂D d) hr hend ?_
  intro p hp
  exact npc_phiNormal_pairing_separates_left (α := alpha) (r := r) (q := q) t hM₂ hwild hτ' hα d
    (unramPhi (A := M) _ hufpf) (unramPhi (A := ElemDual M) _ hufpfD)
    (unramPhi_spec (A := M) _ hufpf) (unramPhi_injective hgfpf hufpf)
    (unramPhi_bijective hgfpfD hufpfD).2 p hp

end

end GQ2.Dyadic.NProcyclicUnram

namespace GQ2.Dyadic.NProcyclic

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-- **The residual scalar sub-branch of the procyclic-`N` unramified obligation.**  `sigma` acts
trivially, hence — the unramified action image being procyclic — every generator does, the ends
of the complex carry cohomology and the `sigma`-coordinate of a normal cochain is free. -/
def ScalarActionImageStokes (alpha r h q : ℕ) (d : EtaData) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M]
    [ContinuousSMul ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) →
    IsSimpleModTwo ((GammaR (2 + 2 * h) q (Words.Npc.npcW alpha r h d) : Type)) M →
    (∀ m : M, gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) .tau • m = m) →
    (∀ m : M,
      (actionImageMarking (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M).σ • m = m) →
      StokesDuality (actionImageGenerators (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M)
        (resolvedFamily alpha r h q d
          (4 * Monoid.exponent (ActionImage (2 + 2 * h) q (Words.Npc.npcW alpha r h d) M))) M

set_option maxHeartbeats 1600000 in
/-- **The procyclic-`N` unramified branch, reduced to its scalar sub-branch.**  The `sigma`
dichotomy of `actionImage_sigma_split_or_fixedPointFree` splits the `tau`-unramified obligation
in two; the generic half is `NProcyclicUnram.stokesDuality_actionImage_generic`. -/
theorem unramifiedActionImageStokes_of_scalar {alpha r h q : ℕ} {d : EtaData}
    (hα : 2 ≤ alpha) (hqe : Even q) (hsc : ScalarActionImageStokes alpha r h q d) :
    UnramifiedActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d) := by
  intro M _ _ _ _ _ _ hM₂ hsimple hτ
  rcases actionImage_sigma_split_or_fixedPointFree
    (n := 2 + 2 * h) (q := q) (R := Words.Npc.npcW alpha r h d) hM₂ hsimple hτ with hσ | hσfpf
  · exact hsc M hM₂ hsimple hτ hσ
  · exact NProcyclicUnram.stokesDuality_actionImage_generic hα hqe M hM₂ hsimple hτ hσfpf

end

end GQ2.Dyadic.NProcyclic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms GQ2.Dyadic.NProcyclicUnram.stokesDuality_actionImage_generic
#print axioms GQ2.Dyadic.NProcyclic.unramifiedActionImageStokes_of_scalar

end AxiomAudit
