/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageRegression

/-!
# Reconnaissance: the shape of `HigherKummerArtinSharpPrimitiveRestrictionBridge`

This file contains **no new mathematics**.  It is a scoping artifact for the arithmetic route
to the all-stage residual obligation: it records, as theorems, the exact logical position of
the named bridge

`HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W hfg`
  `= (∀ m, HigherTateKummerArtinCompatibilityAt …) → SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg`

relative to the group-theoretic target `residual ∈ sharpNeutralBracketSpan`.

Four facts are established, all by composing existing in-tree equivalences.

1. `sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan` —
   the bridge's *conclusion* is literally bracket-span membership.  It mentions no
   reciprocity bundle, no Kummer package, and no Tate duality datum.
2. `sharpCyclotomicInflationPrimitiveResidualVanishing_congr_base` —
   the conclusion does not depend on the chosen sharp-admissible base point `W` either.
   Hence the bridge is a statement about `(K, h, k, T)` alone.
3. `higherKummerArtinSharpPrimitiveRestrictionBridge_iff_mem_bracketSpan` and
   `higherKummerArtinSharpPrimitiveRestrictionBridge_of_mem_bracketSpan` —
   the bridge is *equivalent* to the implication
   `FiniteLayerNormReciprocity B → residual ∈ bracketSpan`, and is *implied* by the
   unconditional span membership.  Consequently:
   * proving the bridge is never harder than proving the unconditional statement, but
   * the moment `FiniteLayerNormReciprocity B` becomes available (it is exactly the
     norm-residue clause deliberately omitted from the B5-K bundle), the bridge and the
     unconditional statement are interderivable — see
     `sharpNeutralBracketSpanSupply_of_bridge_of_finiteLayerNormReciprocity`.
   Nothing here shows that the premise supplies *leverage*; the arithmetic route must exhibit
   that separately.
4. `higherKummerArtinSharpPrimitiveRestrictionBridge_bot` —
   an unconditional instance at `K = ⊥`, `h = 0`, every `k ≥ 3`, every `B` and every `W`.
   This certifies that the bridge is neither vacuous nor mis-oriented.

Candidate statements that could NOT be proved during reconnaissance are recorded as prose in a
comment at the end of the file, never as an unproved declaration.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace SqCyclotomicStageTuple

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]

/-! ## 1.  The bridge conclusion is literal bracket-span membership -/

/-- The chain-level primitive-vanishing statement is *equal in strength* to membership of the
stage residual in the literal improved bracket span.  Composing the two in-tree equivalences
makes the cochain-level phrasing a restatement, not a strengthening. -/
theorem sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg ↔
      sharpNeutralResidualElement T hk W ∈ sharpNeutralBracketSpan T hk :=
  (stageResidual_primitiveVanishing_iff_kernelResidualCompatibility W hfg).trans
    (sharpCyclotomicInflationKernelResidualCompatibility_iff_mem_bracketSpan W hfg)

/-! ## 2.  Independence of the sharp-admissible base point -/

/-- The bridge conclusion does not depend on which point of the sharp-admissible affine space
is chosen: changing base point moves the residual by a neutral shift, which lies in the bracket
span.  Hence the `∀ W` and `∃ W` forms of the stage obligation coincide. -/
theorem sharpCyclotomicInflationPrimitiveResidualVanishing_congr_base
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W W' : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg ↔
      SharpCyclotomicInflationPrimitiveResidualVanishing T hk W' hfg := by
  rw [sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan W hfg,
    sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan W' hfg,
    ← nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan (hk := hk) W,
    ← nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan (hk := hk) W']

/-- The base-point-free spelling of the bridge conclusion. -/
theorem sharpNeutralBracketSpanSupply_iff_primitiveResidualVanishing
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    SharpNeutralBracketSpanSupply T hk ↔
      SharpCyclotomicInflationPrimitiveResidualVanishing T hk W hfg := by
  rw [sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan W hfg]
  constructor
  · rintro ⟨W', hW'⟩
    rw [← nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan (hk := hk) W]
    exact (nonempty_coreHandleSharpActualDefectSupply_iff_mem_bracketSpan W').mpr hW'
  · intro h
    exact ⟨W, h⟩

/-! ## 3.  The bridge against the unconditional target

`FiniteLayerNormReciprocity B` is `ReciprocityFiniteTwoKernelAgreement B`, i.e. injectivity of
completed pro-`2` reciprocity (`reciprocityFiniteTwoKernelAgreement_iff_injective`).  It is a
`Prop` parameter, not an axiom: the B5-K bundle deliberately omits the norm-residue clause. -/

/-- The bridge is exactly the implication `FiniteLayerNormReciprocity B → residual ∈ span`. -/
theorem higherKummerArtinSharpPrimitiveRestrictionBridge_iff_mem_bracketSpan
    {R : LocalReciprocity} {B : MarkedRecip R K}
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W hfg ↔
      (FiniteLayerNormReciprocity B →
        sharpNeutralResidualElement T hk W ∈ sharpNeutralBracketSpan T hk) := by
  rw [higherKummerArtinSharpPrimitiveRestrictionBridge_iff_finiteLayerNormReciprocity W hfg]
  exact forall_congr' fun _ ↦
    sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan W hfg

/-- **No-leverage regression, direction one.**  The unconditional group-theoretic target
implies the bridge for every reciprocity bundle.  So a route-`α` proof subsumes route `β`. -/
theorem higherKummerArtinSharpPrimitiveRestrictionBridge_of_mem_bracketSpan
    {R : LocalReciprocity} {B : MarkedRecip R K}
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (H : sharpNeutralResidualElement T hk W ∈ sharpNeutralBracketSpan T hk) :
    HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W hfg :=
  (higherKummerArtinSharpPrimitiveRestrictionBridge_iff_mem_bracketSpan W hfg).mpr fun _ ↦ H

/-- **No-leverage regression, direction two.**  Once `FiniteLayerNormReciprocity B` is
available, the bridge and the unconditional stage obligation are interderivable.  Thus adding
the omitted norm-residue clause to the B5-K bundle does not by itself shrink the remaining
problem: it only moves the same proposition behind a discharged premise. -/
theorem sharpNeutralBracketSpanSupply_of_bridge_of_finiteLayerNormReciprocity
    {R : LocalReciprocity} {B : MarkedRecip R K}
    {h k : ℕ} {T : SqCyclotomicStageTuple K h k} {hk : 3 ≤ k}
    (W : SharpAdmissibleCorrection T (by omega))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (Hrec : FiniteLayerNormReciprocity B)
    (Hbridge : HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W hfg) :
    SharpNeutralBracketSpanSupply T hk :=
  ⟨W, (higherKummerArtinSharpPrimitiveRestrictionBridge_iff_mem_bracketSpan W hfg).mp
    Hbridge Hrec⟩

end SqCyclotomicStageTuple

/-! ## 4.  A non-vacuity certificate at the bottom field -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **The bridge is a theorem at `K = ⊥`, unconditionally, for every bundle and every base
point.**  It is therefore neither vacuous nor mis-oriented: the premise is not being used to
smuggle in a false conclusion, and the rank-one regression
`sqCyclotomicStageTuple_bot_all_defectReachable` is consistent with it.

Note what this does *not* show: the proof discards the premise entirely.  No instance is known
in which `FiniteLayerNormReciprocity` is actually consumed. -/
theorem higherKummerArtinSharpPrimitiveRestrictionBridge_bot
    {R : LocalReciprocity} (B : MarkedRecip R (⊥ : IntermediateField ℚ_[2] ℚ̄₂))
    (k : ℕ) (hk : 3 ≤ k)
    (T : SqCyclotomicStageTuple (⊥ : IntermediateField ℚ_[2] ℚ̄₂) 0 k)
    (W : T.SharpAdmissibleCorrection (by omega)) :
    SqCyclotomicStageTuple.HigherKummerArtinSharpPrimitiveRestrictionBridge B T hk W
      (maxProTwoGalK_isTopologicallyFinGen (⊥ : IntermediateField ℚ_[2] ℚ̄₂)) := by
  obtain ⟨W₀, hW₀⟩ := sqCyclotomicStageTuple_bot_primitiveResidualVanishing k hk T
  exact SqCyclotomicStageTuple.higherKummerArtinSharpPrimitiveRestrictionBridge_of_mem_bracketSpan
    W _
    ((SqCyclotomicStageTuple.sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan
        W _).mp
      ((SqCyclotomicStageTuple.sharpCyclotomicInflationPrimitiveResidualVanishing_congr_base
        W₀ W _).mp hW₀))

#print axioms
  SqCyclotomicStageTuple.sharpCyclotomicInflationPrimitiveResidualVanishing_iff_mem_bracketSpan
#print axioms SqCyclotomicStageTuple.sharpCyclotomicInflationPrimitiveResidualVanishing_congr_base
#print axioms SqCyclotomicStageTuple.sharpNeutralBracketSpanSupply_iff_primitiveResidualVanishing
#print axioms
  SqCyclotomicStageTuple.higherKummerArtinSharpPrimitiveRestrictionBridge_iff_mem_bracketSpan
#print axioms
  SqCyclotomicStageTuple.higherKummerArtinSharpPrimitiveRestrictionBridge_of_mem_bracketSpan
#print axioms
  SqCyclotomicStageTuple.sharpNeutralBracketSpanSupply_of_bridge_of_finiteLayerNormReciprocity
#print axioms higherKummerArtinSharpPrimitiveRestrictionBridge_bot

/-! ## 5.  Candidates that reconnaissance could NOT discharge

These are recorded as prose, deliberately never as unproved declarations.  Each is part of the
missing datum named in the docstring of `HigherKummerArtinSharpPrimitiveRestrictionBridge`.

**(C1) The cochain-level Hilbert-90 datum (the actual gap).**  In mathematical English: for a
degree-one class `x ∈ H¹(Q_k, 𝔽₂)`, B11a returns only the *cohomological* identity
`x ∪ x = κ ∪ x` in `H²(G_K(2), 𝔽₂)`.  What the transgression argument needs is a chosen
`1`-cochain `β ∈ C¹(G_K(2), 𝔽₂)` with `dβ = inf(z_{x∪x - κ∪x})` *together with* the identity

  `β(n) - β(1) = digit_{k+2}(χ_cyc(n))`  for every `n ∈ λ_k(G_K(2))`,

i.e. the normalized restriction of the primitive to the stage layer equals the fresh sharp
cyclotomic digit.  A candidate Lean signature, over the already-built machinery:

```
def SharpCyclotomicPrimitiveDigitSupply
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (k : ℕ) (hk : 2 ≤ k)
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) : Prop :=
  ∀ x : H1 (levelQuot (maxProPQuotient 2 (GalK K)) k) (ZMod 2),
    ∃ (z : Z2 (levelQuot (maxProPQuotient 2 (GalK K)) k) (ZMod 2))
      (b : C1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      H2mk _ _ z = cyclotomicBocksteinDefectAt (K := K) k hk x ∧
      dOne _ _ b.1 = (Z2comap ⟨levelMk _ k, continuous_levelMk _ k⟩
        (AddMonoidHom.id (ZMod 2)) continuous_id (fun _ _ => rfl) z).1 ∧
      ∀ n : twoCentralSeries (maxProPQuotient 2 (GalK K)) k,
        b.1 n.1 - b.1 1 = 0 ↔
          Units.map (PadicInt.toZModPow (k + 2)).toMonoidHom (chiCycKTwo (K := K) n.1) = 1
```

That is exactly the `hsharp` hypothesis of
`cyclotomicBocksteinLayerCharacterAt_eq_zero_iff_sharpShadow_of_primitive`, promoted to an
existential supply.  It is *not* the bridge: it pins down **one** inflation-kernel character
(the cyclotomic Bockstein one).  The bridge quantifies over **all** classes `η` in the
inflation kernel satisfying the five improved-presentation equations.

**(C2) The missing span/exhaustion step.**  Deriving the bridge from (C1) additionally requires

  every `η ∈ ker(H²(Q_k,𝔽₂) → H²(G,𝔽₂))` satisfying the five bracket-atom equations has
  inverse transgression in the span of the cyclotomic Bockstein characters,

a rank statement about `Hom(λ_k/λ_{k+1}, 𝔽₂)` with no arithmetic content.  This is the same
kind of statement a variable-rank SL1/SL2 Labute campaign proves directly, and it is where the
arithmetic route rejoins the group-theoretic route.

**(C3) Normalization hazards, if (C1)/(C2) are attempted.**
* `β(n) - β(1)` rather than `β(n)`: the primitive is only determined up to `Z1`, and only its
  normalized restriction to `λ_k` is well defined (`lowerTwoCentralPrimitive_restriction_uniqueAt`).
* the `k+2` digit, not `k+1`: `sharpCyclotomicLayerShadowAt` targets `(ZMod (2 ^ (k+2)))ˣ`
  and consumes `sharpChiLevel … (k+1)`.  Off-by-one here silently changes the statement.
* `TateDualityG.inv` is unnormalized for `n > 2` (see the B6 note in
  `FiniteTwoLocalReciprocityHigherHilbert90`), so any attempt to import a *scalar* Artin value
  rather than a kernel statement must fix that unit first.
* the third atom `p²[p,x₂]` is inseparable (diagonal plus polarization); it must not be split.
-/

end

end GQ2.Dyadic.LSquare
