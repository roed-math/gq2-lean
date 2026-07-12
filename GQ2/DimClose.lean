import GQ2.DimAssembly
import GQ2.DeepCount

/-!
# P-15f8 (finale): `lemma_6_17_dim`, reduced to the residue-trivial tame lift

The f6/f7/f8 chain is now fully assembled.  This leaf feeds every input of f7's deliverable
`DeepCount.hduality_of_data` from `lemma_6_17_dim`'s own hypotheses, and hands the result to
f8's `DimAssembly.lemma_6_17_dim_of_hduality` (whose `hext` is already discharged by
`ShapiroExtend`).  Concretely:

* the `V^∨` regular-summand package (`lemma_6_11_of_tame_pair` at `dualModule`, via DimAssembly's
  `dual_*` bricks);
* the self-duality `eU`/`heU`/`ht₀U` from the §6.3 invariant form `(q, hq, hns, hinv)`
  (`DeepDuality.dualSelfDual`/`_equivariant`/`exists_dualModule_smul_ne`);
* the B13 unit-filtration bundle for the splitting field `k`, supplied by the
  `GQ2.dyadicUnitFiltration` axiom (already in the census — no new axiom).

**The one input that is not derivable** is a *residue-trivial lift of tame inertia*
`(g₀, hg₀ : ρ g₀ = c tameTau, hg₀rt : IsResidueTrivial (ker ρ) g₀)` — the standard local-field
fact that tame inertia acts trivially on the residue field (Serre, *Local Fields*, Ch. IV).  The
repo works in the spectral-norm vocabulary and carries no residue-field machinery, so this is
threaded **hypothesis-side** here (per the user's decision to keep the assembly axiom-free): the
theorem `lemma_6_17_dim_of_residueLift` is `lemma_6_17_dim` reduced to exactly that lift plus the
standard Galois-correspondence `k`-plumbing (`k`/`FiniteDimensional`/`hker`, threaded as
everywhere in `LocalKummer`/`DeepDualityK`).

Axioms: std-3 + B6 (`tateDualityAt`) + B7 + B11a (`hilbertSymbol_normCriterion_finiteDyadic`)
+ B12 (`kummerClassK_surjective`) + B13 (`dyadicUnitFiltration`) — the §6.3 deep-part budget,
no new axiom.  Closing `SectionSix.lemma_6_17_dim` outright needs the residue-trivial-lift fact
(an axiom-or-infrastructure decision).
-/

namespace GQ2

namespace DimClose

open ContCoh DimAssembly LocalKummer QuadraticFp2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **`lemma_6_17_dim`, reduced to the residue-trivial tame lift** (P-15f8 finale): the §6.3
deep-half dimension identity `#X₊² = #H¹(ℚ₂, V)`, assembled from f7's `hduality_of_data` + f8's
`lemma_6_17_dim_of_hduality`, with the single arithmetic input — a residue-trivial lift of tame
inertia — threaded as a hypothesis, alongside the standard Galois-correspondence `k`-plumbing. -/
theorem lemma_6_17_dim_of_residueLift (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))]
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (g₀ : AbsGalQ2) (hg₀ : ρ g₀ = c tameTau)
    (hg₀rt : IsResidueTrivial (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) g₀) :
    Nat.card (SectionSix.deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  classical
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective B c hc ρ hfac
  have hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤ := gen_of_surjective c hc
  -- the `V^∨` regular-summand package (as in `lemma_6_17_dim_of_hext_hduality`)
  haveI : Finite (V →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  letI : DistribMulAction C (V →+ ZMod 2) := dualModule
  have hV2D : ∀ φ : V →+ ZMod 2, φ + φ = 0 := fun φ => FoxH.ElemDual.add_self_eq_zero φ
  have hfaithD : ∀ h : C, (∀ φ : V →+ ZMod 2, h • φ = φ) → h = 1 := fun h hh =>
    dual_faithful hV2 hfaith h fun φ v => congrArg (fun ψ : V →+ ZMod 2 => ψ v) (hh φ)
  have hsimpleD : ∀ W : AddSubgroup (V →+ ZMod 2),
      (∀ (h : C), ∀ φ ∈ W, h • φ ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
    dual_simple hV2 hsimple W fun h φ hφ => hW h φ hφ
  have hramD : ∃ φ : V →+ ZMod 2, c tameTau • φ ≠ φ := by
    obtain ⟨φ, v, hφv⟩ := dual_ram hV2 hram
    exact ⟨φ, fun heq => hφv (congrArg (fun ψ : V →+ ZMod 2 => ψ v) heq)⟩
  obtain ⟨Nreg, ι, r, hι, hr, hri⟩ :=
    lemma_6_11_of_tame_pair (V := V →+ ZMod 2) hgen (tame_rel_image c) hV2D hfaithD hsimpleD hramD
  have hnt : Nontrivial (V →+ ZMod 2) := by
    obtain ⟨φ, hφ⟩ := hramD
    exact ⟨c tameTau • φ, φ, hφ⟩
  -- the self-duality inputs from the §6.3 invariant form
  have hduality := hduality_of_data (V := V) ρ hρsurj hsimpleD hnt ι r hι hr hri
    (dualSelfDual q hq hns hV2) (fun cc φ => dualSelfDual_equivariant q hq hns hV2 hinv cc φ)
    (c tameTau) (exists_dualModule_smul_ne hV2 (c tameTau) hram)
    g₀ hg₀ hg₀rt k htriv hker
    (dyadicUnitFiltration k).π (dyadicUnitFiltration k).hπ_mem (dyadicUnitFiltration k).hπ_ne
    (dyadicUnitFiltration k).hπ_lt (dyadicUnitFiltration k).hπ_max
    (dyadicUnitFiltration k).he (dyadicUnitFiltration k).he_pos (dyadicUnitFiltration k).hf_pos
    (dyadicUnitFiltration k).card_gr_zero (dyadicUnitFiltration k).card_gr
  exact lemma_6_17_dim_of_hduality B c hc ρ hfac hρ hV2 hfaith hsimple hram hduality

end DimClose

end GQ2
