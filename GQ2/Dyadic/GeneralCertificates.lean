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

/-- A continuous equivalence of cores, read as a hom. -/
noncomputable def genCertHomOfEquiv (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type)) :
    ContinuousMonoidHom (P₁ : Type) (P₂ : Type) :=
  ⟨e.toMulEquiv.toMonoidHom, e.continuous_toFun⟩

@[simp] theorem genCertHomOfEquiv_apply (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type))
    (x : (P₁ : Type)) : genCertHomOfEquiv e x = e x := rfl

variable {nu₁ : ContinuousMonoidHom P₁ Ztwo} {nu₂ : ContinuousMonoidHom P₂ Ztwo}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- **The boundary map, pulled back along a marking-compatible equivalence of cores.**  The
inverse `e⁻¹` carries `ν₁` back to `ν₂`, so `genCertBdHom` applies at `e⁻¹`. -/
noncomputable def genCertBdPull (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type))
    (hnu : ∀ x, nu₂ (e x) = nu₁ x)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nu₂)) :
    ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nu₁) :=
  (genCertBdHom (genCertHomOfEquiv e.symm)
    (fun y => (hnu (e.symm y)).symm.trans (congrArg nu₂ (e.apply_symm_apply y)))).comp b

/-- **The two pullbacks cancel on `frameMap`.**  This one equation is the whole content of the
core transport: everything the recursion layer reads out of a `(b, F)` pair factors through
`F.frameMap ∘ b`, so once the pulled pair agrees with the original here, no downstream object
can tell the two cores apart. -/
theorem genCertFrameMap_pull (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type))
    (hnu : ∀ x, nu₂ (e x) = nu₁ x) (F : BoundaryFrameK q P₂ H E)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nu₂)) (g : Γ) :
    (genCertFramePull (genCertHomOfEquiv e) F).frameMap ((genCertBdPull e hnu b) g)
      = F.frameMap (b g) := by
  show (F.alpha (b g).1.1, F.psiBar (e (e.symm (b g).1.2)))
      = (F.alpha (b g).1.1, F.psiBar (b g).1.2)
  rw [e.apply_symm_apply]

end BoundaryPull

/-! ## §2 The `frameMap` layer

Every lemma here is stated at *two* boundary/frame pairs over *two* cores, related only by
`hfm : ∀ γ, F₁.frameMap (b₁ γ) = F₂.frameMap (b₂ γ)`.  That is deliberate: the determinant
clause's boundary map is not the pulled-back one (it is rebuilt from the certificate's own
`pro2`), and stating the layer at `hfm` covers both uses. -/

section FrameMapLayer

variable {q : ℕ} {P₁ P₂ : ProfiniteGrp} {nu₁ : ContinuousMonoidHom P₁ Ztwo}
  {nu₂ : ContinuousMonoidHom P₂ Ztwo}
  {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {b₁ : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nu₁)} {F₁ : BoundaryFrameK q P₁ H E}
  {b₂ : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nu₂)} {F₂ : BoundaryFrameK q P₂ H E}
  {Y : Type} [Group Y] [TopologicalSpace Y] [Finite Y]

/-- The boundary equation is insensitive to the core, given `hfm`. -/
theorem genCert_isBoundaryLiftK_congr (hfm : ∀ g : Γ, F₁.frameMap (b₁ g) = F₂.frameMap (b₂ g))
    (T : MarkedTarget H E Y) (f : ContinuousMonoidHom Γ Y) :
    IsBoundaryLiftK b₁ F₁ T f ↔ IsBoundaryLiftK b₂ F₂ T f := by
  constructor
  · intro hf g
    rw [← hfm g]
    exact hf g
  · intro hf g
    rw [hfm g]
    exact hf g

/-- **The boundary-lift bijection**, and the reason the analytic clauses move at all: it is the
identity on the underlying `ContSurj`, so every downstream object that reads a lift only through
`ρ.1.1` (`LiftsOverK`, `rhoPrimeK`, `GaussZResidueK`, the `mBK` fibre condition) is *the same
object* on both sides, not merely an isomorphic one. -/
def genCertBdLiftEquiv (hfm : ∀ g : Γ, F₁.frameMap (b₁ g) = F₂.frameMap (b₂ g))
    (T : MarkedTarget H E Y) : BoundaryLiftsK b₁ F₁ T ≃ BoundaryLiftsK b₂ F₂ T where
  toFun r := ⟨r.1, (genCert_isBoundaryLiftK_congr hfm T r.1.1).mp r.2⟩
  invFun r := ⟨r.1, (genCert_isBoundaryLiftK_congr hfm T r.1.1).mpr r.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem genCertBdLiftEquiv_val
    (hfm : ∀ g : Γ, F₁.frameMap (b₁ g) = F₂.frameMap (b₂ g)) (T : MarkedTarget H E Y)
    (r : BoundaryLiftsK b₁ F₁ T) : (genCertBdLiftEquiv hfm T r).1 = r.1 := rfl

/-- Eq. (29)'s count does not see the core. -/
theorem genCert_exactImageCountK_congr
    (hfm : ∀ g : Γ, F₁.frameMap (b₁ g) = F₂.frameMap (b₂ g)) (T : MarkedTarget H E Y) :
    exactImageCountK b₁ F₁ T = exactImageCountK b₂ F₂ T :=
  Nat.card_congr (genCertBdLiftEquiv hfm T)

omit [TopologicalSpace Y] in
/-- `m_{Γ,λ}(B)` does not see the core.  (The `Y`-topology is not needed: `RF.TB` is a marked
target over `RF.YB`, whose instances come from the recursion frame.) -/
theorem genCert_mBK_congr (hfm : ∀ g : Γ, F₁.frameMap (b₁ g) = F₂.frameMap (b₂ g))
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) (l : RF.DR) : mBK RF b₁ F₁ l = mBK RF b₂ F₂ l := by
  classical
  unfold mBK
  split
  · exact genCert_exactImageCountK_congr hfm RF.TB
  · exact Nat.card_congr (Equiv.subtypeEquiv (genCertBdLiftEquiv hfm RF.TB) fun _ => Iff.rfl)

variable [DistribMulAction Γ (ZMod 2)]

omit [TopologicalSpace Y] in
/-- The Gauss-`Z` residue does not see the core: it quantifies over boundary lifts and reads
each one only through `ρ.1.1`, which `genCertBdLiftEquiv` preserves on the nose. -/
theorem genCert_gaussZResidueK_congr
    (hfm : ∀ g : Γ, F₁.frameMap (b₁ g) = F₂.frameMap (b₂ g))
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    {RF : RecursionFrame T Blk} (En : RF.Enrichment) (l : RF.DR) (hl : l ≠ RF.zeroDR) (G0 : ℤ)
    (Hyp : GaussZResidueK b₁ F₁ En l hl G0) : GaussZResidueK b₂ F₂ En l hl G0 :=
  fun r => Hyp ((genCertBdLiftEquiv hfm RF.TC).symm r)

end FrameMapLayer

/-! ## §3 The four analytic clauses transport

`ScalarHilbertCertificate` mentions no core at all, so it needs no transport lemma: it is the
*same* `Prop` on both sides.  The other three are each `∀`-quantified over a boundary/frame pair,
so each is discharged by handing the hypothesis the pulled-back pair together with
`genCertFrameMap_pull`. -/

section ClauseTransport

variable {q : ℕ} {P₁ P₂ : ProfiniteGrp} {nu₁ : ContinuousMonoidHom P₁ Ztwo}
  {nu₂ : ContinuousMonoidHom P₂ Ztwo} {n : ℕ} {SN : SourceNumerics n} {Gam : ProfiniteGrp}
  (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type)) (hnu : ∀ x, nu₂ (e x) = nu₁ x)

include hnu in
/-- **Ledger field 3 transports.**  Clause 2 (the half-torsor count) mentions no core and is
carried verbatim; clauses 1 and 3 go through the pulled pair, clause 3 additionally rewriting
`exactImageCountK` and `mBK` by §2. -/
theorem genCert_exactLiftingSemantics_pull
    (Hyp : ExactLiftingSemantics Gam n q P₁ nu₁ SN) :
    ExactLiftingSemantics Gam n q P₂ nu₂ SN := by
  refine ⟨fun RF b F r => ?_, Hyp.2.1, fun hE2 hRK hR2 b F => ?_⟩
  · exact Hyp.1 RF (genCertBdPull e hnu b) (genCertFramePull (genCertHomOfEquiv e) F)
      ((genCertBdLiftEquiv (genCertFrameMap_pull e hnu F b) RF.TC).symm r)
  · have h := Hyp.2.2 hE2 hRK hR2 (genCertBdPull e hnu b)
      (genCertFramePull (genCertHomOfEquiv e) F)
    simpa only [genCert_exactImageCountK_congr (genCertFrameMap_pull e hnu F b),
      genCert_mBK_congr (genCertFrameMap_pull e hnu F b)] using h

include hnu in
/-- **Ledger field 4 transports.**  All four clauses read the boundary lift only through
`rhoPrimeK`, i.e. through `ρ.1.1`, so the pulled pair gives *definitionally the same* cocycle
groups; nothing is rewritten. -/
theorem genCert_stokes_pull (smul : DistribMulAction ↥Gam (ZMod 2))
    (Hyp : StokesDualityCertificate Gam n q P₁ nu₁ SN smul) :
    StokesDualityCertificate Gam n q P₂ nu₂ SN smul := by
  refine ⟨fun b F En l hl r => ?_, fun b F En l hl Dsc r c => ?_,
    fun b F En l hl Dsc r chi => ?_, fun b F En l hl hW hV hnt r => ?_⟩
  · exact Hyp.1 (genCertBdPull e hnu b) (genCertFramePull (genCertHomOfEquiv e) F) En l hl
      ((genCertBdLiftEquiv (genCertFrameMap_pull e hnu F b) _).symm r)
  · exact Hyp.2.1 (genCertBdPull e hnu b) (genCertFramePull (genCertHomOfEquiv e) F) En l hl Dsc
      ((genCertBdLiftEquiv (genCertFrameMap_pull e hnu F b) _).symm r) c
  · exact Hyp.2.2.1 (genCertBdPull e hnu b) (genCertFramePull (genCertHomOfEquiv e) F) En l hl
      Dsc ((genCertBdLiftEquiv (genCertFrameMap_pull e hnu F b) _).symm r) chi
  · exact Hyp.2.2.2 (genCertBdPull e hnu b) (genCertFramePull (genCertHomOfEquiv e) F) En l hl
      hW hV hnt ((genCertBdLiftEquiv (genCertFrameMap_pull e hnu F b) _).symm r)

include hnu in
/-- The transported ν-compatibility: `ν_{t,q} ∘ tame = ν₂ ∘ (e ∘ pro2)`. -/
theorem genCertCompat {tame : ContinuousMonoidHom Gam (Tq q)}
    {pro2 : ContinuousMonoidHom Gam (P₁ : Type)}
    (compat : ∀ g : Gam, nuTq q (tame g) = nu₁ (pro2 g)) :
    ∀ g : Gam, nuTq q (tame g) = nu₂ (((genCertHomOfEquiv e).comp pro2) g) :=
  fun g => (compat g).trans (hnu (pro2 g)).symm

include hnu in
/-- **Ledger field 6 transports.**  Here the boundary map is *not* the pulled-back one: it is
rebuilt from the certificate's own `pro2`, and the transported `pro2` is `e ∘ pro2`.  The two
`frameMap` composites then agree by `rfl` — no `apply_symm_apply` is needed on this clause,
which is why §2 is stated at a bare `hfm` rather than at the pullback. -/
theorem genCert_determinant_pull {tame : ContinuousMonoidHom Gam (Tq q)}
    {pro2 : ContinuousMonoidHom Gam (P₁ : Type)}
    {compat : ∀ g : Gam, nuTq q (tame g) = nu₁ (pro2 g)}
    (smul : DistribMulAction ↥Gam (ZMod 2))
    (Hyp : AffineDeterminantCertificate Gam n q P₁ nu₁ SN tame pro2 compat smul) :
    AffineDeterminantCertificate Gam n q P₂ nu₂ SN tame ((genCertHomOfEquiv e).comp pro2)
      (genCertCompat e hnu compat) smul := by
  constructor
  · refine fun T Blk => ?_
    intro _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram
    exact genCert_gaussZResidueK_congr (fun _ => rfl) _ l hl _
      (Hyp.1 T Blk hE2 hq0 hqe (genCertFramePull (genCertHomOfEquiv e) F) hsimple hVne hnt m hm
        hcard l hl hunram)
  · refine fun T Blk => ?_
    intro _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram
    exact genCert_gaussZResidueK_congr (fun _ => rfl) _ l hl _
      (Hyp.2 T Blk hE2 hq0 hqe (genCertFramePull (genCertHomOfEquiv e) F) hsimple hVne hnt m hm
        hcard l hl hram)

end ClauseTransport

end GQ2.Dyadic
