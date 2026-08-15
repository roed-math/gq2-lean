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
`BoundaryLiftsK`, which preserves the underlying `ContSurj` **on the nose**, and that is the
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
`frameMap` composites then agree by `rfl`: no `apply_symm_apply` is needed on this clause,
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

/-! ## §4 The `WordCertificate` core transport

The record's seventeen fields split three ways, and it is worth recording the split because
`docs/dyadic/w75-state-note.md` §3.1 (F1) names six "core-dependent" fields and two of them are
not: `coreRel` and `proTwoWord` quantify over *every* pro-`2` group and mention no core at all,
so they move verbatim.  The true split is

* **ten fields mention no core**: `tameSpecialization`, `coreRel`, `proTwoWord`, `tfg`,
  `smulZmod2`, `contSMulZmod2`, `htriv`, `scalar`, `htame`, `hwild`.  Carried verbatim.
* **four fields move by naturality of the equivalence**: `pro2` (post-compose with `e`),
  `ker_pro2` (`e` is injective, so it adds no kernel), `hpro2` (`e` is onto), `compat` (this is
  where the marking compatibility `hnu` is used, and the only place in the record).
* **three fields are the analytic clauses** and move by §3.

`hP` is not derived: the transported `IsProP` witness is an argument, since every use site
already has one (`genAsmCoreIsProP` on the general table). -/

section RecordTransport

variable {n q : ℕ} {R : PWord (Generator n)} {P₁ P₂ : ProfiniteGrp} {hP₁ : IsProP 2 P₁}
  {nu₁ : ContinuousMonoidHom P₁ Ztwo} {nu₂ : ContinuousMonoidHom P₂ Ztwo}
  {SN : SourceNumerics n}

/-- **The word-certificate core transport** (the restatement `genAsm_nonempty_equiv_L_core_piBd`'s
docstring identifies as the whole distance between the committed `n = 1` endpoint and the general
`L` row).  A `WordCertificate` over the core `P₁` becomes one over `P₂` along a continuous
equivalence `e : P₁ ≃ P₂` that carries the `Ztwo` marking of `P₂` back to that of `P₁`.

Nothing about the word, the degree, the tame modulus or the numerics moves; only the core does.
The construction is therefore reusable wherever a classification output lands on a different
presentation of the same core. -/
noncomputable def WordCertificate.genCertTransport (W : WordCertificate n q R P₁ hP₁ nu₁ SN)
    (hP₂ : IsProP 2 P₂) (e : ContinuousMulEquiv (P₁ : Type) (P₂ : Type))
    (hnu : ∀ x, nu₂ (e x) = nu₁ x) : WordCertificate n q R P₂ hP₂ nu₂ SN where
  tameSpecialization := W.tameSpecialization
  coreRel := W.coreRel
  proTwoWord := W.proTwoWord
  pro2 := (genCertHomOfEquiv e).comp W.pro2
  ker_pro2 := by
    rw [← W.ker_pro2]
    ext g
    simp only [MonoidHom.mem_ker]
    constructor
    · intro hg
      have h1 : e (W.pro2 g) = 1 := hg
      have h2 := congrArg e.symm h1
      rwa [e.symm_apply_apply, map_one] at h2
    · intro hg
      have h1 : W.pro2 g = 1 := hg
      show e (W.pro2 g) = 1
      rw [h1, map_one]
  hpro2 := e.surjective.comp W.hpro2
  compat := genCertCompat e hnu W.compat
  tfg := W.tfg
  smulZmod2 := W.smulZmod2
  contSMulZmod2 := W.contSMulZmod2
  htriv := W.htriv
  exactLifting := genCert_exactLiftingSemantics_pull e hnu W.exactLifting
  stokes := genCert_stokes_pull e hnu W.smulZmod2 W.stokes
  scalar := W.scalar
  determinant := genCert_determinant_pull e hnu W.smulZmod2 W.determinant
  htame := W.htame
  hwild := W.hwild

end RecordTransport

/-! ## §5 The acceptance test: the `L` row's certificate over `D_sq 0`

`Main.lean` §6's `wordCertificate_nonempty_lSq` is unconditional but lives over `Π`
(`GQ2/BoundaryFrame.lean:142`), while the general constructor table's `L` row asks for a
certificate over `D_sq h`.  `genAsm_nonempty_equiv_L_core_piBd` supplies the equivalence at
`h = 0`; §4 supplies the transport; together they discharge the `CAND` field of
`GenAsmRowResidual` on the `L 0` row outright. -/

section LRow

/-- The chosen equivalence `D_sq 0 ≃ Π`, from `genAsm_nonempty_equiv_L_core_piBd`. -/
noncomputable def genCertLEquiv :
    ContinuousMulEquiv ((genAsmCore (.L 0) : ProfiniteGrp) : Type) (PiBd : Type) :=
  genAsm_nonempty_equiv_L_core_piBd.some

/-- The `Ztwo` marking of `D_sq 0` transported from `Π`'s `ν₂`.  ⚠ This is the marking the
transported certificate carries; it is **not** claimed to be the canonical `lNu 0`, and no such
claim is available at this tree (`ztwoIota_lNu` compares `lNu` with `nuSq`, not with `nuTwo`
across `genCertLEquiv`). -/
noncomputable def genCertLNu :
    ContinuousMonoidHom ((genAsmCore (.L 0) : ProfiniteGrp) : Type) Ztwo :=
  nuTwo.comp (genCertHomOfEquiv genCertLEquiv)

theorem genCertLNu_surjective : Function.Surjective genCertLNu :=
  SectionThree.nuTwo_surjective.comp genCertLEquiv.surjective

/-- The `L` row's degree at `h = 0` is `1`, definitionally. -/
theorem genCert_L_zero_degree : (SelectedPresentation.L 0).degree = 1 := rfl

/-- **The acceptance test.**  The general constructor table's `L` row at `h = 0` carries an
unconditional `WordCertificate` over its *own* core `D_sq 0`, at the marking `genCertLNu`.

This is `Main.lean`'s `wordCertificate_nonempty_lSq` moved off `Π` by
`WordCertificate.genCertTransport` along `genAsm_nonempty_equiv_L_core_piBd`.  It closes item 1
of `docs/dyadic/w75-state-note.md` §6 at `h = 0`. -/
theorem genCert_wordCertificate_nonempty_L_zero :
    Nonempty (WordCertificate (SelectedPresentation.L 0).degree 2
      (SelectedPresentation.L 0).word (genAsmCore (.L 0)) (genAsmCoreIsProP (.L 0)) genCertLNu
      (standardNumerics (SelectedPresentation.L 0).degree)) :=
  ⟨wordCertificate_nonempty_lSq.some.genCertTransport (genAsmCoreIsProP (.L 0))
    genCertLEquiv.symm
    (fun x => congrArg nuTwo (genCertLEquiv.apply_symm_apply x))⟩

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {Rec : LocalReciprocity} {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **The `n = 1` case of the general-degree theorem, with its candidate side discharged.**
`genAsm_candidate_equiv_galK_of_supply` at the `L 0` row no longer asks for a `WordCertificate`:
the branch datum's marking is pinned to `genCertLNu` and the certificate is supplied by
`genCert_wordCertificate_nonempty_L_zero`.  What remains is exactly the arithmetic supply `KS`
and the field-side inputs `F`, i.e. `GenAsmRowResidual`'s three `ASK` fields, not its four.

The residue hypothesis `hq` is the only extra pin: the committed `n = 1` certificate is at
`q = 2`, and a degree-`1` `K` is `ℚ₂`, so `hq` is a coherence condition rather than a new
obligation. -/
theorem genCert_candidate_equiv_galK_L_zero {T : OrientedTameQuotientK B FF}
    (hq : qOf K FF = 2)
    (KS : KSupply T (SelectedPresentation.L 0).degree (genAsmCore (.L 0))
      (genAsmCoreIsProP (.L 0)) genCertLNu (standardNumerics (SelectedPresentation.L 0).degree))
    (F : GenAsmFieldInputs K B FF (SelectedPresentation.L 0).degree) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.L 0).degree (qOf K FF)
        (SelectedPresentation.L 0).word : ProfiniteGrp) : Type) (GalK K)) := by
  obtain ⟨W⟩ := genCert_wordCertificate_nonempty_L_zero
  exact genAsm_candidate_equiv_galK_of_supply (.L 0) genCertLNu genCertLNu_surjective
    (by rw [hq]; exact W) KS F

end LRow

/-! ## §6 The compact-`N` word certificate at free `(α, h)`

The sibling of `Instances.MCompactCore.mWordCertificate` at the `DN α h` core and the `N` word,
in the same posture: thirteen fields proved, the four analytic clauses as explicit arguments
(the certificate ⇒ count bridge does not exist at the candidate carrier, AS1 divergence 4).

Two differences from the `M` template, both in the `N` row's favour and both checked here rather
than assumed:

* **no `1 ≤ α`.**  The `M` row carries `hα` because WM0-a's Gate-C headline needs `2m = 2^α`.
  Nothing on the `N` side does: `nCorePresentation` (`Count/ProTwo.lean:607`),
  `eval_pro2_nCompact` (`Words/N0.lean:378`) and `tameSpecializes_nCompact`
  (`Count/Routine.lean:379`) are all free in `α`.
* the `coreRel`/`proTwoWord` pair had no named form on this row.  `Count/ProTwo.lean`'s
  `eval_pro2_nCompact_reindex` is the right statement but carries `[T2Space G]` (it is written
  through `CoreReindex.toCore`, whose binder list has one), and `WordCertificate.coreRel` has
  none.  §6 therefore re-derives the pair from `eval_pro2_nCompact` directly, exactly as the `M`
  row does through `mCoreMark`. -/

section NRow

open Words Count Count.PilotN

/-- The compact-`N` core marking: the alphabet marking read through `nIdx`, with **no**
topological hypotheses, which is what lets it sit in the `coreRel` slot. -/
def genCertNCoreMark (h : ℕ) {G : Type*} [Group G] (t : Marking (2 + 2 * h) G) :
    Fin (coreRank h) → G :=
  fun i => t (nIdx h i)

/-- **`WordCertificate.coreRel` at the compact-`N` row.** -/
def genCertNCoreRel (α h : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G) : G :=
  nRelWord α (genCertNCoreMark h t)

/-- **`WordCertificate.proTwoWord` at the compact-`N` row**, at every handle count and every
`α`: WN0's Gate-C headline read through the `nIdx` dictionary. -/
theorem genCertNProTwoWord (α h : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (nCompactW α h)) = genCertNCoreRel α h G t := by
  rw [eval_pro2_nCompact α h t]
  show _ = nRelWord α (fun i => t (nIdx h i))
  simp only [nRelWord, nIdx_zero, nIdx_one, nIdx_two, nIdx_three, nIdx_handleIdxU,
    nIdx_handleIdxV, Marking.apply_sigma]

/-- **`WordCertificate.pro2` at the compact-`N` row.** -/
noncomputable def genCertNPro2 (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR (2 + 2 * h) q (nCompactW α h)) : Type)
      ((DN α h : ProfiniteGrp) : Type) :=
  CorePresentation.coreHom (nCorePresentation α h) hq0 hqe

/-- **`WordCertificate.ker_pro2` at the compact-`N` row.** -/
theorem genCertN_ker_pro2 (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    (genCertNPro2 α h q hq0 hqe).toMonoidHom.ker
      = proPKernel 2 ((GammaR (2 + 2 * h) q (nCompactW α h)) : Type) :=
  CorePresentation.ker_coreHom (nCorePresentation α h) hq0 hqe

/-- **`WordCertificate.hpro2` at the compact-`N` row.** -/
theorem genCertNPro2_surjective (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (genCertNPro2 α h q hq0 hqe) :=
  CorePresentation.coreHom_surjective (nCorePresentation α h) hq0 hqe

/-- **`WordCertificate.tameSpecialization` at the compact-`N` row.** -/
theorem genCertNTameSpecializes (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes (2 + 2 * h) q (nCompactW α h) :=
  Count.tameSpecializes_nCompact hq0 hqe α h

/-- **`WordCertificate.compat` at the compact-`N` row.** -/
theorem genCertNCompat (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes (2 + 2 * h) q (nCompactW α h))
    (nuP : ContinuousMonoidHom ((DN α h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((nCorePresentation α h).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1), nuP ((nCorePresentation α h).mark (.wild j)) = 1)
    (g : ((GammaR (2 + 2 * h) q (nCompactW α h)) : Type)) :
    nuTq q (tameOfSpec (2 + 2 * h) q (nCompactW α h) hspec g)
      = nuP (genCertNPro2 α h q hq0 hqe g) :=
  CorePresentation.nu_compat_coreHom (nCorePresentation α h) hq0 hqe hspec nuP hnuSigma hnuWild g

/-- **The compact-`N` word certificate at free `(α, h, q)`.**  This is the `nWordCertificate`
`docs/dyadic/w75-state-note.md` §6 item 2 asks for: the `N0 α h` row's `CAND` producer, no longer
pinned to the pilot's `(α, h) = (2, 0)`.

Thirteen fields are proved; the four arguments are AS1's analytic clauses at exactly the record's
types, so the elaborator is the acceptance check. -/
noncomputable def genCertNWordCertificate (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 + 2 * h)}
    (nuP : ContinuousMonoidHom ((DN α h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((nCorePresentation α h).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1), nuP ((nCorePresentation α h).mark (.wild j)) = 1)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (nCompactW α h))
      (2 + 2 * h) q (DN α h) nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) q
      (DN α h) nuP SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (nCompactW α h))
      (2 + 2 * h) q (DN α h) nuP SN
      (tameOfSpec (2 + 2 * h) q (nCompactW α h) (genCertNTameSpecializes α h q hq0 hqe))
      (genCertNPro2 α h q hq0 hqe)
      (genCertNCompat α h q hq0 hqe (genCertNTameSpecializes α h q hq0 hqe) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * h) q (nCompactW α h) (DN α h) (isProP_DN α h) nuP SN where
  tameSpecialization := genCertNTameSpecializes α h q hq0 hqe
  coreRel := genCertNCoreRel α h
  proTwoWord := fun G _ _ _ _ _ t => genCertNProTwoWord α h G t
  pro2 := genCertNPro2 α h q hq0 hqe
  ker_pro2 := genCertN_ker_pro2 α h q hq0 hqe
  hpro2 := genCertNPro2_surjective α h q hq0 hqe
  compat := genCertNCompat α h q hq0 hqe (genCertNTameSpecializes α h q hq0 hqe) nuP hnuSigma
    hnuWild
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLifting
  stokes := stokes
  scalar := scalar
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_nCompact _

/-! ### The canonical marking, and non-vacuity

`SelectedCoreLeavesRN.nNuZtwo` is the handle-generic `Ztwo` marking of `D_N`, with both
normalization clauses already proved at free `(α, h)`; what it lacked is surjectivity (the
`(2, 0)` pilot has `SqrtNeg2.pilotNuP_surjective`, the general row had no twin).  With that
one-liner supplied, the producer's three marking binders all vanish. -/

/-- The handle-generic compact-`N` marking is onto (the missing twin of
`SqrtNeg2.pilotNuP_surjective`). -/
theorem genCertNNuZtwo_surjective (alpha h : ℕ) :
    Function.Surjective (SelectedCoreLeavesRN.nNuZtwo alpha h) :=
  Instances.NuWitness.surjective_of_ztwoOne_mem_range _
    ⟨_, SelectedCoreLeavesRN.nNuZtwo_sigma alpha h⟩

/-- **The compact-`N` word certificate at the canonical marking.**  No marking binders remain:
the `N0 α h` row's `CAND` producer takes free `(α, h, q)`, the two `q`-conditions, and AS1's four
analytic clauses, and nothing else. -/
noncomputable def genCertNWordCertificateCanonical (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 + 2 * h)}
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (nCompactW α h))
      (2 + 2 * h) q (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h) SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) q
      (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h) SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (nCompactW α h)) (2 + 2 * h) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (nCompactW α h))
      (2 + 2 * h) q (DN α h) (SelectedCoreLeavesRN.nNuZtwo α h) SN
      (tameOfSpec (2 + 2 * h) q (nCompactW α h) (genCertNTameSpecializes α h q hq0 hqe))
      (genCertNPro2 α h q hq0 hqe)
      (genCertNCompat α h q hq0 hqe (genCertNTameSpecializes α h q hq0 hqe)
        (SelectedCoreLeavesRN.nNuZtwo α h) (SelectedCoreLeavesRN.nNuZtwo_sigma α h)
        (SelectedCoreLeavesRN.nNuZtwo_wild α h))
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * h) q (nCompactW α h) (DN α h) (isProP_DN α h)
      (SelectedCoreLeavesRN.nNuZtwo α h) SN :=
  genCertNWordCertificate α h q hq0 hqe (SelectedCoreLeavesRN.nNuZtwo α h)
    (SelectedCoreLeavesRN.nNuZtwo_sigma α h) (SelectedCoreLeavesRN.nNuZtwo_wild α h)
    exactLifting stokes scalar determinant

/-- The producer sits over the general constructor table's `N0 α h` row: same degree, same
word, same core. -/
theorem genCertN_row_word (α h : ℕ) :
    (SelectedPresentation.N0 α h).word = nCompactW α h := rfl

/-- …and the same core. -/
theorem genCertN_row_core (α h : ℕ) : genAsmCore (.N0 α h) = DN α h := rfl

end NRow

/-! ## §7 The procyclic-`M` row off `h = 0`

`Instances.MProcyclicCore.mpcWordCertificate` is pinned to `h = 0`.  **The diagnosis** (the state
note flagged the hole without one): the pin is *not* in the word layer, not in Gate B, not in
the core `D_M`, and not in the Fox/Stokes layers.  Every one of those is already free in `h`
(`Words.Mpc.eval_pro2_mpcW`, `Count.tameSpecializes_mpcW`, `Count.hwild_mpcW`, `isProP_DM`,
`presentedBy_DM`, `dm_relation`, `Certificates.MProcyclic.mpc_stokesDuality`).  The pin is the
`CoreReindex` dictionary `Instances.MProcyclicCore.mpcReindex`
(`Instances/Cores.lean:882`), which is stated at `Fin (coreRank 0)` and proved by `fin_cases`;
at symbolic `h` its four obligations are blocked on `(k : Fin (2 + 2h + 1)).val = k % (2h + 3)`.
The compact-`M` row escapes only because `mReindex` factors through `nReindex`.

**And the block is already bypassed in the tree**: `mpcCorePresentationUnit`
(`Instances/MpcCoreUnit.lean:381`) is a `CorePresentation` at *every* `h` and every `2`-adic
unit, built from the arbitrary-unit dictionary rather than from a `CoreReindex`.  What it is
stated over is the arbitrary-unit word `mpcWUnit`, not the constructor table's `mpcW`.  The two
coincide **as `PWord`s** exactly when the display is a `.hat`
(`Words.Mpc.mpcWUnit_eq_hatDisplay`); at a `.one` or `.lit` display they agree only after
evaluation (`eval_mpcWUnit_eq_display`).  So the lift lands at free `h` on the `.hat` rows, and
what remains is a word-syntax residual, named as `GenCertMpcDisplayWordEq` below. -/

section MpcRow

open Words Words.Mpc Count Instances.MProcyclicCore

/-- **The word transport.**  Trivial, and named because it is what the `Mpc` lift consumes: a
`WordCertificate` depends on its word only through the index, so an equality of `PWord`s moves
the whole record. -/
noncomputable def WordCertificate.genCertWordTransport {n q : ℕ} {R R' : PWord (Generator n)}
    {P : ProfiniteGrp} {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo}
    {SN : SourceNumerics n} (W : WordCertificate n q R P hP nuP SN) (hR : R = R') :
    WordCertificate n q R' P hP nuP SN :=
  hR ▸ W

/-- ⚠ **The residual of the `Mpc` lift**, as a named `Prop`: the arbitrary-unit word and the
constructor table's word at a display `dsp` agree *as `PWord`s*.  At `dsp = .hat n d` with a
compatible `d` this is `Words.Mpc.mpcWUnit_eq_hatDisplay`, i.e. a theorem; at `.one` and `.lit`
it is open, and only the evaluated form `eval_mpcWUnit_eq_display` is available. -/
def GenCertMpcDisplayWordEq (alpha r p h : ℕ) (eta : ℤ_[2]ˣ) (dsp : EtaDisplay) : Prop :=
  mpcWUnit alpha r p eta h = mpcW alpha r p dsp h

/-- The residual is discharged at every `.hat` display, at every handle count. -/
theorem genCertMpcDisplayWordEq_hat (alpha r p h : ℕ) {eta : ℤ_[2]ˣ} (d : NpcDisplayFor eta) :
    GenCertMpcDisplayWordEq alpha r p h eta (.hat d.data.num d.data.den) :=
  mpcWUnit_eq_hatDisplay alpha r p h d

/-- **The procyclic-`M` core presentation at the table's word**, at every handle count, given the
display residual.  This is `mpcCorePresentationUnit` (free `h`) moved onto `mpcW`. -/
noncomputable def genCertMpcCore (alpha r p h : ℕ) (halpha : 1 ≤ alpha) {eta : ℤ_[2]ˣ}
    {dsp : EtaDisplay} (hw : GenCertMpcDisplayWordEq alpha r p h eta dsp) :
    Count.CorePresentation (2 + 2 * h) (mpcW alpha r p dsp h) (DM alpha h) :=
  hw ▸ mpcCorePresentationUnit alpha r p eta h halpha

/-- **The procyclic-`M` word certificate off `h = 0`.**  Same posture as the `M0`/`N0` producers:
thirteen fields proved, the four analytic clauses as arguments.  The only extra input over
`mpcWordCertificate` is `hw`, the display residual, which is a theorem at every `.hat` display
(`genCertMpcDisplayWordEq_hat`) and at every handle count.

⚠ `1 ≤ alpha` is genuine here, as on the compact-`M` row: it is `eval_pro2_mpcWUnit`'s own
hypothesis and `tameSpecializes_mpcW`'s. -/
noncomputable def genCertMpcWordCertificate (alpha r p q h : ℕ) (halpha : 1 ≤ alpha)
    (hq0 : q ≠ 0) (hqe : Even q) {eta : ℤ_[2]ˣ} {dsp : EtaDisplay}
    (hw : GenCertMpcDisplayWordEq alpha r p h eta dsp)
    {SN : SourceNumerics (2 + 2 * h)}
    (nuP : ContinuousMonoidHom ((DM alpha h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((genCertMpcCore alpha r p h halpha hw).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1),
      nuP ((genCertMpcCore alpha r p h halpha hw).mark (.wild j)) = 1)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (mpcW alpha r p dsp h))
      (2 + 2 * h) q (DM alpha h) nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (mpcW alpha r p dsp h))
      (2 + 2 * h) q (DM alpha h) nuP SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (mpcW alpha r p dsp h))
      (2 + 2 * h) SN (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (mpcW alpha r p dsp h))
      (2 + 2 * h) q (DM alpha h) nuP SN
      (tameOfSpec (2 + 2 * h) q (mpcW alpha r p dsp h)
        (Count.tameSpecializes_mpcW hq0 hqe halpha r p dsp h))
      (Count.CorePresentation.coreHom (genCertMpcCore alpha r p h halpha hw) hq0 hqe)
      (Count.CorePresentation.nu_compat_coreHom (genCertMpcCore alpha r p h halpha hw) hq0 hqe
        (Count.tameSpecializes_mpcW hq0 hqe halpha r p dsp h) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * h) q (mpcW alpha r p dsp h) (DM alpha h) (isProP_DM alpha h) nuP
      SN where
  tameSpecialization := Count.tameSpecializes_mpcW hq0 hqe halpha r p dsp h
  coreRel := fun G _ _ _ _ _ t => mpcCoreRelUnit alpha r p eta h t
  proTwoWord := fun G _ _ _ _ _ t => by
    rw [← hw]
    exact mpcProTwoWordUnit alpha r p eta h halpha t
  pro2 := Count.CorePresentation.coreHom (genCertMpcCore alpha r p h halpha hw) hq0 hqe
  ker_pro2 := Count.CorePresentation.ker_coreHom (genCertMpcCore alpha r p h halpha hw) hq0 hqe
  hpro2 := Count.CorePresentation.coreHom_surjective (genCertMpcCore alpha r p h halpha hw) hq0
    hqe
  compat := Count.CorePresentation.nu_compat_coreHom (genCertMpcCore alpha r p h halpha hw) hq0
    hqe (Count.tameSpecializes_mpcW hq0 hqe halpha r p dsp h) nuP hnuSigma hnuWild
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLifting
  stokes := stokes
  scalar := scalar
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_mpcW _

/-- The producer sits over the general constructor table's `Mpc` row: at `p = p ε r` its word is
the table's word, at every handle count and every display. -/
theorem genCertMpc_row_word (alpha r : ℕ) (epsilon : Bool) (dsp : EtaDisplay) (h : ℕ) :
    (SelectedPresentation.Mpc alpha r epsilon dsp h).word
      = mpcW alpha r (GQ2.Dyadic.p epsilon r) dsp h := rfl

/-- …and the same core. -/
theorem genCertMpc_row_core (alpha r : ℕ) (epsilon : Bool) (dsp : EtaDisplay) (h : ℕ) :
    genAsmCore (.Mpc alpha r epsilon dsp h) = DM alpha h := rfl

end MpcRow

/-! ## §8 The procyclic-`N` row: the first producer

`docs/dyadic/w75-state-note.md` §3.1 (F2) records `Npc` as the one row with **no** `CAND`
producer at all, and `Main.lean`'s `no_frozen_Npc` is the frozen-table echo of that.  The row is
not, however, missing its inputs: `Instances.NProcyclicCore` already carries the `eta = 1`
dictionary at every handle count (`npcReindexOne`, `npcCoreRelOne`, `npcProTwoWordOne`,
`npcCorePresentationOne`, `Instances/NpcCore.lean:542-593`), and Gate B and the wild discharge
are free in every parameter (`Count.tameSpecializes_npcW`, `Count.hwild_npcW`).  So the producer
exists and this section builds it, at free `(α, r, h, q)` and at the `EtaData` display `⟨1, 1⟩`.

⚠ What is **not** covered: an arbitrary `EtaData`.  `npcCorePresentationUnit`
(`Instances/NpcCore.lean:501`) is the arbitrary-unit presentation at every `h`, but it is stated
over `npcWUnit`, and the `Npc` row's word-syntax residual is the exact analogue of
`GenCertMpcDisplayWordEq`.  Naming it, and the arbitrary-display producer, is W77 work. -/

section NpcRow

open Words Words.Npc Count Instances.NProcyclicCore

/-- **The procyclic-`N` word certificate at `eta = ⟨1, 1⟩`, at free `(α, r, h, q)`.**  The first
`WordCertificate` producer this row has had.  Same posture as the other three: thirteen fields
proved, the four analytic clauses as arguments.

No `α` bound is needed, exactly as on the compact-`N` row. -/
noncomputable def genCertNpcWordCertificate (alpha r h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 + 2 * h)}
    (nuP : ContinuousMonoidHom ((DN alpha h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((npcCorePresentationOne alpha r h).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1),
      nuP ((npcCorePresentationOne alpha r h).mark (.wild j)) = 1)
    (exactLifting : ExactLiftingSemantics (GammaR (2 + 2 * h) q (npcW alpha r h ⟨1, 1⟩))
      (2 + 2 * h) q (DN alpha h) nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 + 2 * h) q (npcW alpha r h ⟨1, 1⟩))
      (2 + 2 * h) q (DN alpha h) nuP SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 + 2 * h) q (npcW alpha r h ⟨1, 1⟩))
      (2 + 2 * h) SN (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 + 2 * h) q (npcW alpha r h ⟨1, 1⟩))
      (2 + 2 * h) q (DN alpha h) nuP SN
      (tameOfSpec (2 + 2 * h) q (npcW alpha r h ⟨1, 1⟩)
        (Count.tameSpecializes_npcW hq0 hqe alpha r h ⟨1, 1⟩))
      (Count.CorePresentation.coreHom (npcCorePresentationOne alpha r h) hq0 hqe)
      (Count.CorePresentation.nu_compat_coreHom (npcCorePresentationOne alpha r h) hq0 hqe
        (Count.tameSpecializes_npcW hq0 hqe alpha r h ⟨1, 1⟩) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 + 2 * h) q (npcW alpha r h ⟨1, 1⟩) (DN alpha h) (isProP_DN alpha h) nuP
      SN where
  tameSpecialization := Count.tameSpecializes_npcW hq0 hqe alpha r h ⟨1, 1⟩
  coreRel := npcCoreRelOne alpha r h
  proTwoWord := fun G _ _ _ _ _ t => npcProTwoWordOne alpha r h G t
  pro2 := Count.CorePresentation.coreHom (npcCorePresentationOne alpha r h) hq0 hqe
  ker_pro2 := Count.CorePresentation.ker_coreHom (npcCorePresentationOne alpha r h) hq0 hqe
  hpro2 := Count.CorePresentation.coreHom_surjective (npcCorePresentationOne alpha r h) hq0 hqe
  compat := Count.CorePresentation.nu_compat_coreHom (npcCorePresentationOne alpha r h) hq0 hqe
    (Count.tameSpecializes_npcW hq0 hqe alpha r h ⟨1, 1⟩) nuP hnuSigma hnuWild
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLifting
  stokes := stokes
  scalar := scalar
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_npcW _

/-- The producer sits over the general constructor table's `Npc α r h ⟨1, 1⟩` row. -/
theorem genCertNpc_row_word (alpha r h : ℕ) :
    (SelectedPresentation.Npc alpha r h ⟨1, 1⟩).word = npcW alpha r h ⟨1, 1⟩ := rfl

/-- …and the same core. -/
theorem genCertNpc_row_core (alpha r h : ℕ) (eta : EtaData) :
    genAsmCore (.Npc alpha r h eta) = DN alpha h := rfl

end NpcRow

/-! ## §9 Axiom pins

One pin per declaration of this file, **44** in all, in declaration order.  The pins were
measured when the module landed (`docs/dyadic/w76-cert-note.md` §6) but were never recorded
here; this block is the record.  Adding these lines changes no statement.

⚠ **This file is not uniformly std-3, and the split is the point.**  Measured against the mirror
at `e6bbd2b9`:

* **42 of the 44** print at most the std-3 set `propext, Classical.choice, Quot.sound`.  That is
  every §1 to §4 transport, `WordCertificate.genCertTransport` itself, and all four row
  producers.  Two of the 42 print less than std-3: `genCert_L_zero_degree` prints **no** axioms
  at all, and `genCertNCoreMark` prints `propext, Quot.sound`.
* **2 carry campaign axioms**, and both are in §5, the `L`-row acceptance test, which is the one
  place this module touches arithmetic rather than plumbing:
  - `genCert_wordCertificate_nonempty_L_zero` adds `dyadicOrientation`, `localReciprocity` and
    `peripheralCyclotomicAction`;
  - `genCert_candidate_equiv_galK_L_zero` adds those three plus `tateDualityAt`,
    `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` and
    `Foundations.absGalQ2_localEulerCharacteristic`, the widest pin in the file.

Each of the two is exactly the print of its own input (`wordCertificate_nonempty_lSq`; that set
united with `genAsm_candidate_equiv_galK_of_supply`'s), so the transports cost **zero** axiom
movement.  The reading a consumer should take: **the certificate plumbing and all four row
producers are axiom-free, and the campaign axioms enter only at the acceptance test.**

⚠ **Count correction.**  `w76-cert-note.md` §6 groups the same four exceptional declarations
correctly but calls the std-3 remainder "the other 44"; the remainder is **40** and the file has
**44** declarations, not 48.  The four sets it names reproduce here exactly. -/

section AxiomPins

#print axioms genCertBdHom
#print axioms genCertFramePull
#print axioms genCertHomOfEquiv
#print axioms genCertBdPull
#print axioms genCertFrameMap_pull
#print axioms genCert_isBoundaryLiftK_congr
#print axioms genCertBdLiftEquiv
#print axioms genCert_exactImageCountK_congr
#print axioms genCert_mBK_congr
#print axioms genCert_gaussZResidueK_congr
#print axioms genCert_exactLiftingSemantics_pull
#print axioms genCert_stokes_pull
#print axioms genCertCompat
#print axioms genCert_determinant_pull
#print axioms WordCertificate.genCertTransport
#print axioms genCertLEquiv
#print axioms genCertLNu
#print axioms genCertLNu_surjective
#print axioms genCert_L_zero_degree
#print axioms genCert_wordCertificate_nonempty_L_zero
#print axioms genCert_candidate_equiv_galK_L_zero
#print axioms genCertNCoreMark
#print axioms genCertNCoreRel
#print axioms genCertNProTwoWord
#print axioms genCertNPro2
#print axioms genCertN_ker_pro2
#print axioms genCertNPro2_surjective
#print axioms genCertNTameSpecializes
#print axioms genCertNCompat
#print axioms genCertNWordCertificate
#print axioms genCertNNuZtwo_surjective
#print axioms genCertNWordCertificateCanonical
#print axioms genCertN_row_word
#print axioms genCertN_row_core
#print axioms WordCertificate.genCertWordTransport
#print axioms GenCertMpcDisplayWordEq
#print axioms genCertMpcDisplayWordEq_hat
#print axioms genCertMpcCore
#print axioms genCertMpcWordCertificate
#print axioms genCertMpc_row_word
#print axioms genCertMpc_row_core
#print axioms genCertNpcWordCertificate
#print axioms genCertNpc_row_word
#print axioms genCertNpc_row_core

end AxiomPins

end GQ2.Dyadic
