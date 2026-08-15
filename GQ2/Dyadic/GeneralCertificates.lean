/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.GeneralAssembly

/-!
# Certificate plumbing for the general-degree statement  (dyadic campaign, lane W76-CERT)

`GQ2/Dyadic/GeneralAssembly.lean` states the `n`-free final theorem and names its obligations.
One of them, the `CAND` field of `GenAsmRowResidual`, is a `WordCertificate` over the row's own
core.  This module supplies the plumbing that lets the committed producers reach that field.

## §1 The core transport

The lane's first deliverable is the restatement `genAsm_nonempty_equiv_L_core_piBd`'s docstring
asks for: a `WordCertificate` moves along a continuous, marking-compatible equivalence of cores.

The transport is possible because the core enters the certificate only through two objects:

* the boundary `boundarySubgroupQ q νP ≤ T_q × P` (`GQ2/Dyadic/TameBoundary.lean:220`), and
* the boundary frame `BoundaryFrameK q P H E` (`GQ2/Dyadic/Recursion/Frame.lean:57`), whose only
  `P`-dependent field is `psiBar : P → E`;

and because every downstream recursion object factors through the *composite*
`F.frameMap ∘ b : Γ → H × E` rather than through `P` itself.  §1 makes that factorisation
explicit: `genCertBdPull` moves the boundary map backwards along a hom of cores,
`genCertFramePull` moves the frame backwards, and `genCertFrameMap_pull` says the two moves
cancel on `frameMap`.  Everything after that is `Equiv.subtypeEquivRight` on
`BoundaryLiftsK`, which preserves the underlying `ContSurj` **on the nose** — and that is the
reason the four analytic clauses transport at all, since `LiftsOverK`, `rhoPrimeK`,
`GaussZResidueK` and `mBK` all read `ρ` only through `ρ.1.1`.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore

/-! ## §1 Moving the boundary and the frame along a hom of cores -/

section BoundaryPull

variable {q : ℕ} {P₁ P₂ : ProfiniteGrp}

/-- **The boundary map, pulled back along a hom of cores.**  A homomorphism `g : P₂ → P₁` that
carries `ν₁` back to `ν₂` induces `∂(q, ν₂) → ∂(q, ν₁)` by `(t, p) ↦ (t, g p)`: the equalizer
condition `ν_{t,q} t = ν₂ p` becomes `ν_{t,q} t = ν₁ (g p)` by `hnu`. -/
noncomputable def genCertBdHom {nu₁ : ContinuousMonoidHom P₁ Ztwo}
    {nu₂ : ContinuousMonoidHom P₂ Ztwo} (g : ContinuousMonoidHom (P₂ : Type) (P₁ : Type))
    (hnu : ∀ y, nu₁ (g y) = nu₂ y) :
    ContinuousMonoidHom ↥(boundarySubgroupQ q nu₂) ↥(boundarySubgroupQ q nu₁) :=
  ⟨(((MonoidHom.id (Tq q)).prodMap g.toMonoidHom).comp
      (boundarySubgroupQ q nu₂).subtype).codRestrict (boundarySubgroupQ q nu₁)
      (fun x => by
        show nuTq q x.1.1 = nu₁ (g x.1.2)
        rw [hnu]
        exact x.2),
    (Continuous.prodMk (continuous_fst.comp continuous_subtype_val)
      (g.continuous_toFun.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _⟩

@[simp] theorem genCertBdHom_apply {nu₁ : ContinuousMonoidHom P₁ Ztwo}
    {nu₂ : ContinuousMonoidHom P₂ Ztwo} (g : ContinuousMonoidHom (P₂ : Type) (P₁ : Type))
    (hnu : ∀ y, nu₁ (g y) = nu₂ y) (x : ↥(boundarySubgroupQ q nu₂)) :
    ((genCertBdHom g hnu x : ↥(boundarySubgroupQ q nu₁)) : Tq q × (P₁ : Type))
      = (x.1.1, g x.1.2) := rfl

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **The boundary frame, pulled back along a hom of cores.**  Only `psiBar` moves; `alpha`,
`alpha_surjective` and `exponent_two` are `F`'s own fields, which is what makes the whole
block layer (`blockEnrichmentDK` and everything it calls, all of which read `F` only through
`F.alpha` and `F.alpha_surjective`) *definitionally* unchanged by the pull. -/
def genCertFramePull (g : ContinuousMonoidHom (P₁ : Type) (P₂ : Type))
    (F : BoundaryFrameK q P₂ H E) : BoundaryFrameK q P₁ H E where
  alpha := F.alpha
  alpha_surjective := F.alpha_surjective
  exponent_two := F.exponent_two
  psiBar := F.psiBar.comp g

@[simp] theorem genCertFramePull_alpha (g : ContinuousMonoidHom (P₁ : Type) (P₂ : Type))
    (F : BoundaryFrameK q P₂ H E) : (genCertFramePull g F).alpha = F.alpha := rfl

end BoundaryPull

end GQ2.Dyadic
