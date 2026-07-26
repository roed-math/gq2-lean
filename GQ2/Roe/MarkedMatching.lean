/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.ChiR
import GQ2.Roe.MaxPro2Bridge
import GQ2.LocalMarked

/-!
# The marked matching engine: `ν`-compatible correction of the B-Lab isomorphism  (ticket R15)

Machinery for the fill of `markedPro2_R` (`GQ2/Roe/MarkedPro2.lean`, note §3.3
⟦prop:markedpro2⟧).  Given the abstract B-Lab isomorphism `f : D_R ≅ D₀`, the marked statement
needs a *corrected* isomorphism matching the unramified markings; per the note's proof this
requires (a) functoriality of the canonical (Labute) orientation across `f`, and (b) the
`(u, b)`-correction of `prop_3_8_classification`/`prop_3_8_lift`.  This file provides both and
packages the result as the keystone `exists_matching_iso`.

## (a) Orientation functoriality: `isLabuteOrientation_comp_iso`

`χ₀ ∘ f` is a Labute orientation of `D_R`, for **every** continuous isomorphism
`f : D_R ≅ D₀` — the "canonical orientations are functorial" step of the note's proof.  The
descent characterization (`IsLabuteOrientationDatum`) asks that the `WordLift ℤ₂(χ) ⋊ ℤ₂ˣ`-lift
of the relator die for *arbitrary* derivation generator-values, so the proof must realize
arbitrary values `(Ds, Dx, Dy)` at the transported generators `f⁻¹`-side.  Route:

1. `D₀`-side **master derivations** `masterH c` (`c ∈ ℤ₂³`): continuous homs
   `D₀ → ℤ₂(χ₀) ⋊ ℤ₂ˣ` with base `χ₀` and derivation generator-values `c` — Labute's descent
   *for `D₀`*, i.e. the computation `2·0 + 4·Ds + (η⁻¹ − 1)·Ds = 4Ds − 4Ds = 0` on the relator
   `A²S⁴[S,Y]` at the orientation values `(−1, 1, η)`, fed to the universal property
   `d0LiftHom`.  (The lift group carries the product topology; the pro-2 instance is the
   `ℤ₂-by-ℤ₂ˣ` extension argument `isProP_two_wordLift`.)
2. The evaluation matrix `M : Matrix (Fin 3) (Fin 3) ℤ₂`, `M i j` = value of the `j`-th basis
   master at the `i`-th transported generator `f (s/x/y)`.  **`M` is invertible**: mod 2 the
   masters become genuine (untwisted) `𝔽₂`-characters, and a continuous hom into a finite
   discrete group is determined on the topological generators `f (s), f (x), f (y)`
   (`mem_closure_image_gens`), so the mod-2 rows span `𝔽₂³`; Nakayama-style, `det M ∈ ℤ₂ˣ`.
3. Solve `M c = (Ds, Dx, Dy)`, contract the three basis masters by `c`
   (`masterContract`, a hom by the crossed-derivation product rule), pull back along `f`, and
   evaluate on `dr_relation` via `map_drWord`.

## (b) The `ν`-correction: `exists_matching_iso`

With `χ₀ ∘ f = χ_R` (by (a) + `isLabuteOrientation_ext`), the `Ȳ₀`-coordinate `τ₂` of
`f(x)` in `D₀^{ab}` is a 2-adic **unit**: squaring kills the torsion character, leaving
`X² = (η²)^{τ₂}` with `X ≡ 5 (mod 16)` (`rootX_toZModPow_four`) while an even exponent would
force `X² ≡ 1 (mod 16)`.  The mod-2 row analysis (same engine as (2)) makes the
`(S̄₀, Ȳ₀)`-coordinate matrix of `(f(s), f(x))` invertible, so the linear system
`u·σᵢ + b·τᵢ = ν_R(gen i)` has a solution with `u ∈ ℤ₂ˣ`; `prop_3_8_lift` lifts `(u, b)` to an
automorphism `Ψ` of `D₀`, and `F := Ψ ∘ f` matches the markings:
`ζ ∘ ν_{D_R} = sHom ∘ abMk ∘ F` (`sHom` = the `S̄₀`-coordinate = the `D₀`-side unramified
functional, cf. `GQ2/LocalMarked.lean`).

Everything here is `axiom`-free modulo the June-side inputs it cites (B3c/B8 via
`chiD0`/`prop_3_8_lift`) and the R13b Demushkin fills cited by `MarkedPro2.lean` (landed
2026-07-25, sorry-free); no `BLabHypothesis` occurs — the abstract isomorphism is a
*hypothesis* of the keystone.
-/

namespace GQ2

open FoxH Multiplicative SectionThree Roe

/-! ## The lift group `ℤ₂ ⋊ ℤ₂ˣ` as a profinite 2-group

`FoxH.WordLift ℤ_[2] ℤ_[2]ˣ` (`GQ2/FoxHeisenberg/Basic.lean`) is the crossed-derivation lift
group of `GQ2/Roe/CrossedDerivation.lean`.  There it is used purely algebraically; to run
`D₀`'s universal property into it we equip it (locally — the finite word-cochain theory
`GQ2/WordCohBridge.lean` uses the *discrete* topology on its finite instances, so these
instances stay file-local) with the product topology of `ℤ₂ × ℤ₂ˣ`, under which it is a
profinite 2-group: an extension of the pro-2 `ℤ₂ˣ` by the pro-2 `ℤ₂`. -/

noncomputable local instance instTopWordLift : TopologicalSpace (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  TopologicalSpace.induced (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) inferInstance

private lemma isInducing_equivProd :
    Topology.IsInducing (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)) :=
  ⟨rfl⟩

/-- `WordLift ℤ₂ ℤ₂ˣ ≃ₜ ℤ₂ × ℤ₂ˣ`. -/
private noncomputable def wordLiftHomeo : WordLift ℤ_[2] ℤ_[2]ˣ ≃ₜ ℤ_[2] × ℤ_[2]ˣ :=
  (WordLift.equivProd (A := ℤ_[2]) (C := ℤ_[2]ˣ)).toHomeomorphOfIsInducing isInducing_equivProd

private lemma continuous_wordLift_u : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ => p.u :=
  continuous_fst.comp wordLiftHomeo.continuous

private lemma continuous_wordLift_g : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ => p.g :=
  continuous_snd.comp wordLiftHomeo.continuous

private lemma continuous_wordLift_mk {X : Type*} [TopologicalSpace X]
    {u : X → ℤ_[2]} {g : X → ℤ_[2]ˣ} (hu : Continuous u) (hg : Continuous g) :
    Continuous fun x => (⟨u x, g x⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
  rw [isInducing_equivProd.continuous_iff]
  exact hu.prodMk hg

local instance instTopGroupWordLift : IsTopologicalGroup (WordLift ℤ_[2] ℤ_[2]ˣ) where
  continuous_mul := by
    have : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ × WordLift ℤ_[2] ℤ_[2]ˣ =>
        (⟨p.1.u + p.1.g • p.2.u, p.1.g * p.2.g⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
      refine continuous_wordLift_mk (Continuous.add ?_ ?_) ?_
      · exact continuous_wordLift_u.comp continuous_fst
      · -- `p.1.g • p.2.u = ↑(p.1.g) * p.2.u`
        simp only [Units.smul_def, smul_eq_mul]
        exact (Units.continuous_val.comp (continuous_wordLift_g.comp continuous_fst)).mul
          (continuous_wordLift_u.comp continuous_snd)
      · exact (continuous_wordLift_g.comp continuous_fst).mul
          (continuous_wordLift_g.comp continuous_snd)
    exact this
  continuous_inv := by
    have : Continuous fun p : WordLift ℤ_[2] ℤ_[2]ˣ =>
        (⟨-(p.g⁻¹ • p.u), p.g⁻¹⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) := by
      refine continuous_wordLift_mk (Continuous.neg ?_) continuous_wordLift_g.inv
      simp only [Units.smul_def, smul_eq_mul]
      exact (Units.continuous_val.comp continuous_wordLift_g.inv).mul continuous_wordLift_u
    exact this

local instance : CompactSpace (WordLift ℤ_[2] ℤ_[2]ˣ) := wordLiftHomeo.symm.compactSpace

local instance : T2Space (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  wordLiftHomeo.isEmbedding.t2Space

local instance : TotallyDisconnectedSpace (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  wordLiftHomeo.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- The base projection `ℤ₂ ⋊ ℤ₂ˣ →* ℤ₂ˣ`, `⟨u, g⟩ ↦ g`. -/
private def wordLiftBase : WordLift ℤ_[2] ℤ_[2]ˣ →* ℤ_[2]ˣ where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The offset kernel `{⟨u, 1⟩} = ker (base)` is pro-2: continuous surjective image of
`Multiplicative ℤ₂` under `u ↦ ⟨u, 1⟩`. -/
private lemma isProP_two_wordLiftBase_ker : IsProP 2 wordLiftBase.ker := by
  have hφmul : ∀ u v : Multiplicative ℤ_[2],
      (⟨(u * v).toAdd, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)
        = (⟨u.toAdd, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) * ⟨v.toAdd, 1⟩ := by
    intro u v
    ext
    · show u.toAdd + v.toAdd = u.toAdd + (1 : ℤ_[2]ˣ) • v.toAdd
      rw [one_smul]
    · exact (one_mul _).symm
  set φ : ContinuousMonoidHom (Multiplicative ℤ_[2]) wordLiftBase.ker :=
    { toFun := fun u => ⟨⟨u.toAdd, 1⟩, rfl⟩
      map_one' := rfl
      map_mul' := fun u v => Subtype.ext (hφmul u v)
      continuous_toFun := by
        refine Continuous.subtype_mk ?_ _
        exact continuous_wordLift_mk continuous_toAdd continuous_const } with hφ
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨u, g⟩, hg⟩
    have hg1 : g = 1 := hg
    subst hg1
    exact ⟨ofAdd u, Subtype.ext rfl⟩
  exact SectionThree.isProP_of_surjective φ.toMonoidHom φ.continuous_toFun hsurj
    PropOneOne.isProP_two_multPadicInt

/-- **The lift group is pro-2** — the extension argument: in a finite quotient, the image of
the offset kernel is a 2-group (`isPGroup_map_of_isProP`), and the quotient by it is a finite
discrete quotient of `ℤ₂ˣ`, hence a 2-group (`isProP_two_unitsPadicInt`); finite extensions of
2-groups by 2-groups are 2-groups (`Nat.card` multiplicativity). -/
theorem isProP_two_wordLift : IsProP 2 (WordLift ℤ_[2] ℤ_[2]ˣ) := by
  intro U
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (WordLift ℤ_[2] ℤ_[2]ˣ ⧸ U.toSubgroup) := inferInstance
  set q : WordLift ℤ_[2] ℤ_[2]ˣ →* WordLift ℤ_[2] ℤ_[2]ˣ ⧸ U.toSubgroup :=
    QuotientGroup.mk' U.toSubgroup with hq
  have hqcont : Continuous q := continuous_quot_mk
  -- the image `N` of the offset kernel is a normal 2-subgroup
  set N : Subgroup (WordLift ℤ_[2] ℤ_[2]ˣ ⧸ U.toSubgroup) := wordLiftBase.ker.map q with hN
  have hNpgroup : IsPGroup 2 N :=
    SectionThree.isPGroup_map_of_isProP isProP_two_wordLiftBase_ker q hqcont
  haveI hNnormal : N.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  -- the quotient by `N` is covered by `ℤ₂ˣ` through the splitting `g ↦ ⟨0, g⟩`
  set σ : ContinuousMonoidHom ℤ_[2]ˣ (WordLift ℤ_[2] ℤ_[2]ˣ) :=
    { toFun := fun g => ⟨0, g⟩
      map_one' := rfl
      map_mul' := fun g h => by
        ext
        · show (0 : ℤ_[2]) = 0 + g • 0
          rw [smul_zero, add_zero]
        · rfl
      continuous_toFun := continuous_wordLift_mk continuous_const continuous_id } with hσ
  set ψ : ℤ_[2]ˣ →* (WordLift ℤ_[2] ℤ_[2]ˣ ⧸ U.toSubgroup) ⧸ N :=
    ((QuotientGroup.mk' N).comp q).comp σ.toMonoidHom with hψ
  have hψsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup y
    refine ⟨w.g, ?_⟩
    show QuotientGroup.mk' N (q (σ w.g)) = QuotientGroup.mk' N (q w)
    rw [QuotientGroup.mk'_eq_mk']
    refine ⟨q (⟨0, w.g⟩⁻¹ * w), Subgroup.mem_map_of_mem q ?_, ?_⟩
    swap
    · rw [← map_mul]
      show q ((⟨0, w.g⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) * ((⟨0, w.g⟩ : WordLift ℤ_[2] ℤ_[2]ˣ)⁻¹ * w))
        = q w
      rw [mul_inv_cancel_left]
    show wordLiftBase (⟨0, w.g⟩⁻¹ * w) = 1
    rw [map_mul, map_inv]
    show (w.g)⁻¹ * w.g = 1
    exact inv_mul_cancel _
  -- `ker ψ` is open: it is the preimage of the (discrete) set `N` under the continuous `q ∘ σ`
  have hker_eq : (ψ.ker : Set ℤ_[2]ˣ) = (fun g => q (σ g)) ⁻¹' (N : Set _) := by
    ext g
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, hψ, MonoidHom.coe_comp,
      Function.comp_apply, ContinuousMonoidHom.coe_toMonoidHom, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hker_open : IsOpen (ψ.ker : Set ℤ_[2]ˣ) := by
    rw [hker_eq]
    exact (isOpen_discrete (N : Set (WordLift ℤ_[2] ℤ_[2]ˣ ⧸ U.toSubgroup))).preimage
      (hqcont.comp σ.continuous_toFun)
  -- so the `N`-quotient is a finite discrete quotient of the pro-2 `ℤ₂ˣ`, hence a 2-group
  set O : OpenNormalSubgroup ℤ_[2]ˣ := ⟨⟨ψ.ker, hker_open⟩, inferInstance⟩ with hO
  have hQpgroup : IsPGroup 2 ((WordLift ℤ_[2] ℤ_[2]ˣ ⧸ U.toSubgroup) ⧸ N) := by
    have h1 : IsPGroup 2 (ℤ_[2]ˣ ⧸ O.toSubgroup) := isProP_two_unitsPadicInt O
    exact h1.of_surjective (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toMonoidHom
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).surjective
  -- extension bookkeeping: `#(W/U) = #((W/U)/N) · #N`, both factors 2-powers
  haveI : Finite N := Subtype.finite
  obtain ⟨a, ha⟩ := (IsPGroup.iff_card (p := 2)).mp hNpgroup
  obtain ⟨b, hb⟩ := (IsPGroup.iff_card (p := 2)).mp hQpgroup
  refine (IsPGroup.iff_card (p := 2)).mpr ⟨b + a, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, ha, hb, pow_add]

/-! ## Small local copies of private June-side value facts

`unitNegThree_val`, `topAbCongr_abMk` and (later) the `sHom`/`yHom` generator values are
`private` in their home files (`GQ2/PropOneOneAssembly.lean`, `GQ2/SectionThree.lean`); their
proofs are one-liners over public definitions, so we re-derive them here rather than widen the
June API.  The `d0LiftHom` generator values were in the same situation when this file was
written and are copied below too, but they have since been de-privatized as
`SectionThree.d0LiftHom_A`/`_S`/`_Y` (L6 cleanup), so those three copies are now redundant and
could be dropped in a later pass. -/

private lemma unitNegThree_val' : ((unitNegThree : ℤ_[2]ˣ) : ℤ_[2]) = -3 := by
  rw [unitNegThree, IsUnit.unit_spec]
  push_cast
  ring

private lemma topAbCongr_abMk' {G H : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H] [T2Space H]
    [TotallyDisconnectedSpace H] (φ : ContinuousMulEquiv G H) (g : G) :
    topAbCongr φ (abMk g) = abMk (φ g) := rfl

private lemma isUnit_of_toZModPow_one_eq_one' {x : ℤ_[2]}
    (h : PadicInt.toZModPow 1 x = 1) : IsUnit x := by
  rw [PadicInt.isUnit_iff]
  by_contra hne
  have hlt : ‖x‖ < 1 := lt_of_le_of_ne (PadicInt.norm_le_one x) hne
  have hdvd : (2 : ℤ_[2]) ∣ x := by
    have h2 := (PadicInt.norm_lt_one_iff_dvd x).mp hlt
    exact_mod_cast h2
  obtain ⟨y, rfl⟩ := hdvd
  rw [map_mul] at h
  have h2 : (PadicInt.toZModPow (p := 2) 1) 2 = 0 := by
    rw [show ((2 : ℤ_[2])) = ((2 : ℕ) : ℤ_[2]) by push_cast; ring, map_natCast]
    decide
  rw [h2, zero_mul] at h
  exact absurd h (by decide)

section Masters

/-! ## The `D₀`-side universal-property value lemmas (local copies) -/

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

private lemma d0LiftHom_A' (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0LiftHom hH m hrel d0A = m 0 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

private lemma d0LiftHom_S' (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0LiftHom hH m hrel d0S = m 1 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = m 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

private lemma d0LiftHom_Y' (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0LiftHom hH m hrel d0Y = m 2 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2))) = m 2
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-! ## The master crossed derivations -/

/-- **The relator dies in the lift group at the orientation values, for every derivation
vector**: `A²S⁴[S,Y]` evaluated at `(⟨c₀, −1⟩, ⟨c₁, 1⟩, ⟨c₂, η⟩)`, `η = (−3)⁻¹`, is trivial —
the `A²`-factor contributes `(1 + χ(A))·c₀ = 0`, the `S⁴`-factor `4c₁`, and the commutator
`(η⁻¹ − 1)·c₁ = −4c₁` (note ⟦eq:commderivative⟧).  This is Labute's descent property for `D₀`'s
own presentation at its canonical orientation — the engine of the functoriality argument. -/
private lemma masterRel (c : Fin 3 → ℤ_[2]) :
    (⟨c 0, -1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ 2 * (⟨c 1, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ^ 4
      * commP (⟨c 1, 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨c 2, unitNegThree⁻¹⟩ = 1 := by
  rw [commP_wordLift]
  ext
  · simp only [pow_succ, pow_zero, one_mul, WordLift.mul_u, WordLift.mul_g, WordLift.one_u,
      Units.smul_def, smul_eq_mul, Units.val_mul, Units.val_one, Units.val_neg, inv_inv,
      inv_one, mul_one]
    rw [unitNegThree_val']
    ring
  · simp only [pow_succ, pow_zero, one_mul, WordLift.mul_g, WordLift.one_g, commP, inv_one,
      mul_one, one_mul, neg_mul_neg, inv_mul_cancel]

/-! ## The group-level canonical orientation of `D₀` -/

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- The canonical orientation of `D₀` at the group level: `χ₀ = chiD0 ∘ abMk`
(generator values `(−1, 1, (−3)⁻¹)`, from the B3c bundle). -/
noncomputable def chiD0G : ContinuousMonoidHom (D0 : Type) ℤ_[2]ˣ :=
  chiD0.comp ⟨abMk, continuous_abMk⟩

private lemma chiD0G_abMk (d : (D0 : Type)) : chiD0G d = chiD0 (abMk d) := rfl

private lemma chiD0G_A : chiD0G d0A = -1 := orientBundle.chi_A

private lemma chiD0G_S : chiD0G d0S = 1 := orientBundle.chi_S

private lemma chiD0G_Y : chiD0G d0Y = unitNegThree⁻¹ :=
  orientBundle.chi_Y unitNegThree unitNegThree_val'

/-- The master crossed derivation with derivation generator-values `c` — a continuous hom
`D₀ → ℤ₂(χ₀) ⋊ ℤ₂ˣ` over the canonical orientation, via `d0LiftHom` and `masterRel`. -/
private noncomputable def masterH (c : Fin 3 → ℤ_[2]) :
    ContinuousMonoidHom (D0 : Type) (WordLift ℤ_[2] ℤ_[2]ˣ) :=
  d0LiftHom isProP_two_wordLift ![⟨c 0, -1⟩, ⟨c 1, 1⟩, ⟨c 2, unitNegThree⁻¹⟩] (by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons]
    exact masterRel c)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma masterH_A (c : Fin 3 → ℤ_[2]) : masterH c d0A = ⟨c 0, -1⟩ := by
  rw [masterH, d0LiftHom_A']
  simp

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma masterH_S (c : Fin 3 → ℤ_[2]) : masterH c d0S = ⟨c 1, 1⟩ := by
  rw [masterH, d0LiftHom_S']
  simp

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma masterH_Y (c : Fin 3 → ℤ_[2]) : masterH c d0Y = ⟨c 2, unitNegThree⁻¹⟩ := by
  rw [masterH, d0LiftHom_Y']
  simp

/-- The base component of every master is the canonical orientation (they agree on the three
topological generators). -/
private lemma masterH_base (c : Fin 3 → ℤ_[2]) (d : (D0 : Type)) :
    (masterH c d).g = chiD0G d := by
  have h := SectionThree.monoidHom_eq_of_topGen
    (f := wordLiftBase.comp (masterH c).toMonoidHom) (g := chiD0G.toMonoidHom)
    (continuous_wordLift_g.comp (masterH c).continuous_toFun) chiD0G.continuous_toFun
    SectionThree.topGen_d0 ?_
  · exact h d
  · rintro z (rfl | rfl | rfl)
    · show (masterH c d0A).g = chiD0G d0A
      rw [masterH_A, chiD0G_A]
    · show (masterH c d0S).g = chiD0G d0S
      rw [masterH_S, chiD0G_S]
    · show (masterH c d0Y).g = chiD0G d0Y
      rw [masterH_Y, chiD0G_Y]

/-- The crossed-derivation product rule for the derivation component of a master. -/
private lemma masterH_mul_u (c : Fin 3 → ℤ_[2]) (g h : (D0 : Type)) :
    (masterH c (g * h)).u = (masterH c g).u + chiD0G g • (masterH c h).u := by
  rw [map_mul, WordLift.mul_u, masterH_base]

/-- **The `c`-contraction of the basis masters**: `g ↦ ⟨∑ⱼ cⱼ·Dⱼ(g), χ₀(g)⟩`, a group
homomorphism by the crossed-derivation product rule (`ℤ₂`-linear combinations of crossed
derivations over a common character are crossed derivations).  This makes the derivation
generator-values manifestly `ℤ₂`-linear in `c`, which is what the matrix argument needs. -/
private noncomputable def masterContract (c : Fin 3 → ℤ_[2]) :
    (D0 : Type) →* WordLift ℤ_[2] ℤ_[2]ˣ where
  toFun g := ⟨∑ j, c j * (masterH (Pi.single j 1) g).u, chiD0G g⟩
  map_one' := by
    refine WordLift.ext ?_ ?_
    · show (∑ j, c j * (masterH (Pi.single j 1) (1 : (D0 : Type))).u) = (0 : ℤ_[2])
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [map_one]
      show c j * (1 : WordLift ℤ_[2] ℤ_[2]ˣ).u = 0
      rw [WordLift.one_u, mul_zero]
    · show chiD0G 1 = 1
      exact map_one _
  map_mul' g h := by
    refine WordLift.ext ?_ ?_
    · show (∑ j, c j * (masterH (Pi.single j 1) (g * h)).u)
        = (∑ j, c j * (masterH (Pi.single j 1) g).u)
          + chiD0G g • ∑ j, c j * (masterH (Pi.single j 1) h).u
      simp only [masterH_mul_u, Units.smul_def, smul_eq_mul, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    · show chiD0G (g * h) = chiD0G g * chiD0G h
      exact map_mul _ _ _

private lemma masterContract_apply_u (c : Fin 3 → ℤ_[2]) (g : (D0 : Type)) :
    (masterContract c g).u = ∑ j, c j * (masterH (Pi.single j 1) g).u := rfl

private lemma masterContract_apply_g (c : Fin 3 → ℤ_[2]) (g : (D0 : Type)) :
    (masterContract c g).g = chiD0G g := rfl

/-! ## The mod-2 reduction of the masters and the generation engine -/

local instance instTopZModTwo : TopologicalSpace (ZMod (2 ^ 1)) := ⊥

local instance : DiscreteTopology (ZMod (2 ^ 1)) := ⟨rfl⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma continuous_toZModPow_one : Continuous (PadicInt.toZModPow (p := 2) 1) := by
  rw [continuous_def]
  intro T _
  exact isOpen_preimage_toZModPow 1 T

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma zmod2_eq_one_of_isUnit {z : ZMod (2 ^ 1)} (hz : IsUnit z) : z = 1 := by
  haveI : Fact (1 < 2 ^ 1) := ⟨by norm_num⟩
  have hne := hz.ne_zero
  have h : ∀ w : ZMod (2 ^ 1), w ≠ 0 → w = 1 := by decide
  exact h z hne

/-- The mod-2 reduction of the master triple, `g ↦ (D̄₀ g, D̄₁ g, D̄₂ g)`.  Because every 2-adic
unit is `≡ 1 (mod 2)`, the `χ₀`-twist disappears and this is a genuine (continuous)
homomorphism into `𝔽₂³` — the joint `𝔽₂`-character the generation engine feeds on. -/
private noncomputable def masterMod2 : (D0 : Type) →* Multiplicative (Fin 3 → ZMod (2 ^ 1)) where
  toFun g := ofAdd fun j => PadicInt.toZModPow 1 (masterH (Pi.single j 1) g).u
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext j
    rw [map_one]
    show PadicInt.toZModPow 1 (1 : WordLift ℤ_[2] ℤ_[2]ˣ).u = 0
    rw [WordLift.one_u, map_zero]
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    funext j
    rw [masterH_mul_u, map_add]
    congr 1
    rw [Units.smul_def, smul_eq_mul, map_mul,
      zmod2_eq_one_of_isUnit ((chiD0G g).isUnit.map (PadicInt.toZModPow (p := 2) 1)), one_mul]

private lemma continuous_masterMod2 : Continuous masterMod2 := by
  refine continuous_ofAdd.comp (continuous_pi fun j => ?_)
  exact continuous_toZModPow_one.comp
    (continuous_wordLift_u.comp (masterH (Pi.single j 1)).continuous_toFun)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Topological generation of `D₀` by the transported generators `f(s), f(x), f(y)`. -/
private lemma topGen_d0_of_iso (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    (Subgroup.closure {f drS, f drX, f drY}).topologicalClosure = ⊤ := by
  have h := topGen_map (f := f.toMulEquiv.toMonoidHom) f.continuous_toFun
    (EquivLike.surjective f) dr_topGen
  rwa [Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton] at h

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The generation engine**: the value anywhere of a continuous hom from `D₀` into a
finite discrete group lies in the subgroup generated by its values on the transported
generators `f(s), f(x), f(y)`. -/
private lemma mem_closure_gens_of_iso {T : Type} [Group T] [TopologicalSpace T]
    [DiscreteTopology T] (φ : (D0 : Type) →* T) (hφ : Continuous φ)
    (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) (d : (D0 : Type)) :
    φ d ∈ Subgroup.closure {φ (f drS), φ (f drX), φ (f drY)} := by
  set K : Subgroup (D0 : Type) :=
    (Subgroup.closure {φ (f drS), φ (f drX), φ (f drY)}).comap φ with hK
  have hKclosed : IsClosed (K : Set (D0 : Type)) := by
    have hset : (K : Set (D0 : Type))
        = ⇑φ ⁻¹' (Subgroup.closure {φ (f drS), φ (f drX), φ (f drY)} : Set T) := rfl
    rw [hset]
    exact (isClosed_discrete _).preimage hφ
  have hle : Subgroup.closure {f drS, f drX, f drY} ≤ K := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  have htop : (⊤ : Subgroup (D0 : Type)) ≤ K := by
    rw [← topGen_d0_of_iso f]
    exact Subgroup.topologicalClosure_minimal _ hle hKclosed
  exact htop (Subgroup.mem_top d)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- Multiplicative-closure membership in `𝔽₂ⁿ` becomes span membership additively. -/
private lemma toAdd_mem_span_of_mem_closure {n : ℕ}
    {a b c₀ w : Multiplicative (Fin n → ZMod (2 ^ 1))}
    (hw : w ∈ Subgroup.closure {a, b, c₀}) :
    w.toAdd ∈ Submodule.span (ZMod (2 ^ 1))
      ({a.toAdd, b.toAdd, c₀.toAdd} : Set (Fin n → ZMod (2 ^ 1))) := by
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl | rfl
    · exact Submodule.subset_span (Set.mem_insert _ _)
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    · exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))
  | one => exact Submodule.zero_mem _
  | mul x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | inv x _ hx => exact Submodule.neg_mem _ hx

/-! ## The evaluation matrix and its invertibility -/

/-- The evaluation matrix of the basis masters at the transported generators:
`M i j = Dⱼ(f(genᵢ))`. -/
private noncomputable def evalMatrix (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    Matrix (Fin 3) (Fin 3) ℤ_[2] :=
  Matrix.of fun i j => (masterH (Pi.single j 1) (f (![drS, drX, drY] i))).u

private lemma evalMatrixMod_row (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) (i : Fin 3) :
    ((evalMatrix f).map (PadicInt.toZModPow 1)) i = (masterMod2 (f (![drS, drX, drY] i))).toAdd :=
  rfl

private lemma masterMod2_d0A :
    (masterMod2 d0A).toAdd = Pi.single (0 : Fin 3) (1 : ZMod (2 ^ 1)) := by
  funext j
  show PadicInt.toZModPow 1 (masterH (Pi.single j 1) d0A).u = _
  rw [masterH_A]
  show PadicInt.toZModPow 1 ((Pi.single j (1 : ℤ_[2]) : Fin 3 → ℤ_[2]) 0) = _
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · rw [Pi.single_eq_of_ne (Ne.symm hj), Pi.single_eq_of_ne hj, map_zero]

private lemma masterMod2_d0S :
    (masterMod2 d0S).toAdd = Pi.single (1 : Fin 3) (1 : ZMod (2 ^ 1)) := by
  funext j
  show PadicInt.toZModPow 1 (masterH (Pi.single j 1) d0S).u = _
  rw [masterH_S]
  show PadicInt.toZModPow 1 ((Pi.single j (1 : ℤ_[2]) : Fin 3 → ℤ_[2]) 1) = _
  rcases eq_or_ne j 1 with rfl | hj
  · simp
  · rw [Pi.single_eq_of_ne (Ne.symm hj), Pi.single_eq_of_ne hj, map_zero]

private lemma masterMod2_d0Y :
    (masterMod2 d0Y).toAdd = Pi.single (2 : Fin 3) (1 : ZMod (2 ^ 1)) := by
  funext j
  show PadicInt.toZModPow 1 (masterH (Pi.single j 1) d0Y).u = _
  rw [masterH_Y]
  show PadicInt.toZModPow 1 ((Pi.single j (1 : ℤ_[2]) : Fin 3 → ℤ_[2]) 2) = _
  rcases eq_or_ne j 2 with rfl | hj
  · simp
  · rw [Pi.single_eq_of_ne (Ne.symm hj), Pi.single_eq_of_ne hj, map_zero]

/-- **The evaluation matrix is invertible** — mod 2 its rows span `𝔽₂³` by the generation
engine (the mod-2 masters hit the standard basis at `A, S₀, Y₀`), and a matrix over `ℤ₂` with
mod-2-invertible reduction is invertible (`det` is a unit). -/
private lemma isUnit_evalMatrix (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    IsUnit (evalMatrix f) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  set Mb : Matrix (Fin 3) (Fin 3) (ZMod (2 ^ 1)) := (evalMatrix f).map (PadicInt.toZModPow 1)
    with hMb
  -- mod-2 rows span, via the engine at the three `D₀`-generators
  have hspan : ∀ v : Fin 3 → ZMod (2 ^ 1),
      v ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range Mb.row) := by
    have hmem : ∀ d : (D0 : Type), (masterMod2 d).toAdd
        ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range Mb.row) := by
      intro d
      have h1 := mem_closure_gens_of_iso masterMod2 continuous_masterMod2 f d
      have h2 := toAdd_mem_span_of_mem_closure h1
      refine Submodule.span_mono ?_ h2
      rintro z (rfl | rfl | rfl)
      · exact ⟨0, (evalMatrixMod_row f 0).symm⟩
      · exact ⟨1, (evalMatrixMod_row f 1).symm⟩
      · exact ⟨2, (evalMatrixMod_row f 2).symm⟩
    intro v
    have hv : v = ∑ i, v i • Pi.single (M := fun _ => ZMod (2 ^ 1)) i 1 := by
      funext k
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    fin_cases i
    · exact masterMod2_d0A ▸ hmem d0A
    · exact masterMod2_d0S ▸ hmem d0S
    · exact masterMod2_d0Y ▸ hmem d0Y
  have hMbUnit : IsUnit Mb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    have hv := hspan v
    rw [← range_vecMulLinear, LinearMap.mem_range] at hv
    obtain ⟨c, hc⟩ := hv
    exact ⟨c, hc⟩
  -- transfer unit-ness of the determinant through the mod-2 reduction
  have hdet2 : PadicInt.toZModPow 1 ((evalMatrix f).det) = 1 := by
    have hmap : PadicInt.toZModPow 1 ((evalMatrix f).det) = Mb.det := by
      rw [hMb, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [hmap]
    exact zmod2_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det Mb).mp hMbUnit)
  exact isUnit_of_toZModPow_one_eq_one' hdet2

/-! ## Orientation functoriality -/

/-- **Canonical orientations are functorial across the B-Lab isomorphism** (note §3.3, step
"canonical orientations are functorial"): for every continuous isomorphism `f : D_R ≅ D₀`, the
pullback `χ₀ ∘ f` of the canonical orientation of `D₀` is a Labute orientation of `D_R` — every
prescribed derivation triple `(Ds, Dx, Dy)` is realized by contracting the `D₀`-side master
derivations against a solution of the (invertible) evaluation-matrix system and pulling back
along `f`, and then `drWord` dies on `dr_relation` by naturality (`map_drWord`). -/
theorem isLabuteOrientation_comp_iso (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    IsLabuteOrientation (chiD0G.toMonoidHom.comp f.toMulEquiv.toMonoidHom) := by
  intro Ds Dx Dy
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr (isUnit_evalMatrix f)) ![Ds, Dx, Dy]
  set h : (DR : Type) →* WordLift ℤ_[2] ℤ_[2]ˣ :=
    (masterContract c).comp f.toMulEquiv.toMonoidHom with hh
  have hval : ∀ i : Fin 3,
      h (![drS, drX, drY] i) = ⟨![Ds, Dx, Dy] i, chiD0G (f (![drS, drX, drY] i))⟩ := by
    intro i
    refine WordLift.ext ?_ rfl
    show (masterContract c (f (![drS, drX, drY] i))).u = ![Ds, Dx, Dy] i
    rw [masterContract_apply_u]
    have hci := congrFun hc i
    simp only [Matrix.mulVec, dotProduct] at hci
    rw [← hci]
    exact Finset.sum_congr rfl fun j _ => (mul_comm _ _)
  have hword : drWord (h drS) (h drX) (h drY) = 1 := by
    rw [← map_drWord, dr_relation, map_one]
  rw [show h drS = ⟨Ds, chiD0G (f drS)⟩ from hval 0,
    show h drX = ⟨Dx, chiD0G (f drX)⟩ from hval 1,
    show h drY = ⟨Dy, chiD0G (f drY)⟩ from hval 2] at hword
  exact hword

/-! ## Local copies of the `sHom`/`yHom` generator values (private in `GQ2/SectionThree.lean`) -/

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The `sHom`-defining relator computation, reusable for both coordinate homs (the target is
abelian, so the commutator dies and the relation is `2·a + 4·s = 0` on the exponents). -/
private lemma coordRel (a s y : ℤ_[2]) (h : 2 * a + 4 * s = 0) :
    (![ofAdd a, ofAdd s, ofAdd y] : Fin 3 → Multiplicative ℤ_[2]) 0 ^ 2
        * ![ofAdd a, ofAdd s, ofAdd y] 1 ^ 4
        * commP (![ofAdd a, ofAdd s, ofAdd y] 1) (![ofAdd a, ofAdd s, ofAdd y] 2) = 1 := by
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, commP, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
  rw [← ofAdd_zero]
  congr 1
  simp only [nsmul_eq_mul]
  push_cast
  linear_combination h

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma sHom_A' : sHom (abMk d0A) = ofAdd (-2 : ℤ_[2]) :=
  d0LiftHom_A' PropOneOne.isProP_two_multPadicInt
    ![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] (coordRel _ _ _ (by ring))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma sHom_S' : sHom (abMk d0S) = ofAdd (1 : ℤ_[2]) :=
  d0LiftHom_S' PropOneOne.isProP_two_multPadicInt
    ![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] (coordRel _ _ _ (by ring))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma sHom_Y' : sHom (abMk d0Y) = ofAdd (0 : ℤ_[2]) :=
  d0LiftHom_Y' PropOneOne.isProP_two_multPadicInt
    ![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] (coordRel _ _ _ (by ring))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma yHom_A' : yHom (abMk d0A) = ofAdd (0 : ℤ_[2]) :=
  d0LiftHom_A' PropOneOne.isProP_two_multPadicInt
    ![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] (coordRel _ _ _ (by ring))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma yHom_S' : yHom (abMk d0S) = ofAdd (0 : ℤ_[2]) :=
  d0LiftHom_S' PropOneOne.isProP_two_multPadicInt
    ![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] (coordRel _ _ _ (by ring))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma yHom_Y' : yHom (abMk d0Y) = ofAdd (1 : ℤ_[2]) :=
  d0LiftHom_Y' PropOneOne.isProP_two_multPadicInt
    ![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] (coordRel _ _ _ (by ring))

/-! ## The identification `χ₀ ∘ f = χ_R` and the `Ȳ₀`-coordinate parity -/

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma rootX_unique_pair : ∀ a b : ℤ_[2]ˣ,
    (↑a : ℤ_[2]) ^ 3 + 2 * (↑a : ℤ_[2]) ^ 2 + 1 = 0 →
    (↑b : ℤ_[2]) ^ 3 + 2 * (↑b : ℤ_[2]) ^ 2 + 1 = 0 → a = b := fun _ _ ha hb =>
  Units.ext ((rootX_unique ha).trans (rootX_unique hb).symm)

/-- **`χ₀ ∘ f = χ_R`**: the pullback of `D₀`'s canonical orientation along the B-Lab
isomorphism is the Roe orientation, by uniqueness of Labute orientations of `D_R`
(`isLabuteOrientation_ext`, fed by `isLabuteOrientation_comp_iso` and R11's
`isLabuteOrientation_chiR`). -/
private lemma chiD0G_comp_iso_eq_chiR (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    chiD0G.toMonoidHom.comp f.toMulEquiv.toMonoidHom = chiR.toMonoidHom :=
  isLabuteOrientation_ext rootX_unique_pair
    (chiD0G.continuous_toFun.comp f.continuous_toFun) chiR.continuous_toFun
    (isLabuteOrientation_comp_iso f) isLabuteOrientation_chiR

private lemma chiD0_abMk_iso_drX (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    chiD0 (abMk (f drX)) = rootXUnit := by
  have h := DFunLike.congr_fun (chiD0G_comp_iso_eq_chiR f) drX
  exact h.trans chiR_drX

/-- The squared canonical orientation, as a continuous hom. -/
private noncomputable def chiSqHom :
    ContinuousMonoidHom (topAbelianization (D0 : Type)) ℤ_[2]ˣ where
  toFun w := chiD0 w ^ 2
  map_one' := by rw [map_one, one_pow]
  map_mul' a b := by rw [map_mul, mul_pow]
  continuous_toFun := (continuous_pow 2).comp chiD0.continuous_toFun

/-- The `(η²)`-power of the `Ȳ₀`-coordinate, as a continuous hom. -/
private noncomputable def etaYHom :
    ContinuousMonoidHom (topAbelianization (D0 : Type)) ℤ_[2]ˣ where
  toFun w := zpowZtwoHom isProP_two_unitsPadicInt (unitNegThree⁻¹ ^ 2) (yHom w)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  continuous_toFun := (zpowZtwoHom isProP_two_unitsPadicInt
    (unitNegThree⁻¹ ^ 2)).continuous_toFun.comp yHom.continuous_toFun

/-- The squared canonical orientation kills the torsion and reads off the `Ȳ₀`-coordinate:
`χ₀(z)² = (η²)^{Ȳ₀-coordinate of z}`. -/
private lemma chiD0_sq_eq (z : topAbelianization (D0 : Type)) :
    chiD0 z ^ 2 = zpowZtwoHom isProP_two_unitsPadicInt (unitNegThree⁻¹ ^ 2) (yHom z) := by
  have h := d0ab_hom_ext isProP_two_unitsPadicInt chiSqHom etaYHom ?_ ?_ ?_ z
  · exact h
  · show chiD0 (abMk d0A) ^ 2
      = zpowZtwoHom isProP_two_unitsPadicInt (unitNegThree⁻¹ ^ 2) (yHom (abMk d0A))
    rw [show chiD0 (abMk d0A) = chiD0G d0A from rfl, chiD0G_A, yHom_A', neg_one_sq,
      show ofAdd (0 : ℤ_[2]) = (1 : Multiplicative ℤ_[2]) from rfl, map_one]
  · show chiD0 (abMk d0S) ^ 2
      = zpowZtwoHom isProP_two_unitsPadicInt (unitNegThree⁻¹ ^ 2) (yHom (abMk d0S))
    rw [show chiD0 (abMk d0S) = chiD0G d0S from rfl, chiD0G_S, yHom_S', one_pow,
      show ofAdd (0 : ℤ_[2]) = (1 : Multiplicative ℤ_[2]) from rfl, map_one]
  · show chiD0 (abMk d0Y) ^ 2
      = zpowZtwoHom isProP_two_unitsPadicInt (unitNegThree⁻¹ ^ 2) (yHom (abMk d0Y))
    rw [show chiD0 (abMk d0Y) = chiD0G d0Y from rfl, chiD0G_Y, yHom_Y',
      zpowZtwoHom_ofAdd_one]

/-! ## `τ₂` is odd: the mod-16 argument -/

local instance instTopZModSixteen : TopologicalSpace (ZMod (2 ^ 4)) := ⊥

local instance : DiscreteTopology (ZMod (2 ^ 4)) := ⟨rfl⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma continuous_toZModPow_four : Continuous (PadicInt.toZModPow (p := 2) 4) := by
  rw [continuous_def]
  intro T _
  exact isOpen_preimage_toZModPow 4 T

/-- Reduction mod 16 of `ℤ₂ˣ`, as a continuous hom into the finite 2-group `(ℤ/16)ˣ`. -/
private noncomputable def unitsMod16 : ContinuousMonoidHom ℤ_[2]ˣ (ZMod (2 ^ 4))ˣ where
  toMonoidHom := Units.map (PadicInt.toZModPow (p := 2) 4).toMonoidHom
  continuous_toFun := Units.continuous_iff.mpr
    ⟨continuous_toZModPow_four.comp Units.continuous_val,
      continuous_toZModPow_four.comp (Units.continuous_val.comp continuous_inv)⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma isProP_two_unitsZMod16 : IsProP 2 (ZMod (2 ^ 4))ˣ :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 3)
    (by rw [Nat.card_eq_fintype_card]; decide))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma unitsMod16_val (x : ℤ_[2]ˣ) :
    ((unitsMod16 x : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) = PadicInt.toZModPow 4 (x : ℤ_[2]) :=
  rfl

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `η⁴ ≡ 1 (mod 16)`: the value of `unitsMod16` at `(η²)²` is trivial (`η ≡ 5`,
`5⁴ = 625 ≡ 1`). -/
private lemma unitsMod16_eta_four :
    unitsMod16 (((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2) ^ (2 : ℕ)) = 1 := by
  refine Units.ext ?_
  rw [unitsMod16_val]
  have hval : ((((unitNegThree⁻¹ : ℤ_[2]ˣ) ^ 2) ^ (2 : ℕ) : ℤ_[2]ˣ) : ℤ_[2])
      = ((unitNegThree⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ^ 4 := by
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul]
  rw [hval, map_pow]
  -- `v · 13 = 1` in `ℤ/16`, and `13⁴ = 1`
  have hmul : ((unitNegThree⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((unitNegThree : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h13 : PadicInt.toZModPow 4 ((unitNegThree : ℤ_[2]ˣ) : ℤ_[2]) = 13 := by
    rw [unitNegThree_val', show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) from by push_cast; ring,
      map_intCast]
    decide
  have hv : PadicInt.toZModPow 4 ((unitNegThree⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * 13 = 1 := by
    have := congrArg (PadicInt.toZModPow (p := 2) 4) hmul
    rwa [map_mul, map_one, h13] at this
  set v := PadicInt.toZModPow 4 ((unitNegThree⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) with hvdef
  have h134 : (13 : ZMod (2 ^ 4)) ^ 4 = 1 := by decide
  calc v ^ 4 = v ^ 4 * (13 : ZMod (2 ^ 4)) ^ 4 := by rw [h134, mul_one]
    _ = (v * 13) ^ 4 := by ring
    _ = 1 := by rw [hv, one_pow]

/-- **The `Ȳ₀`-coordinate of `f(x)` is odd**: `X² = (η²)^{τ₂}` with `X ≡ 5 (mod 16)`, while
an even `τ₂` would give `X² = (η⁴)^{t} ≡ 1 (mod 16)` — but `X² ≡ 25 ≡ 9`. -/
private lemma toZModPow_one_tau (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    PadicInt.toZModPow 1 ((yHom (abMk (f drX))).toAdd) = 1 := by
  by_contra hne
  have h0 : PadicInt.toZModPow 1 ((yHom (abMk (f drX))).toAdd) = 0 := by
    have hall : ∀ w : ZMod (2 ^ 1), w ≠ 1 → w = 0 := by decide
    exact hall _ hne
  obtain ⟨t, ht⟩ : (2 : ℤ_[2]) ∣ (yHom (abMk (f drX))).toAdd := by
    have hker : (yHom (abMk (f drX))).toAdd
        ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := h0
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hker
    obtain ⟨w, hw⟩ := hker
    exact ⟨w, by rw [hw]; ring⟩
  have hsq' : rootXUnit ^ 2
      = zpowZtwo isProP_two_unitsPadicInt (unitNegThree⁻¹ ^ 2)
        ((yHom (abMk (f drX))).toAdd) := by
    have h := chiD0_sq_eq (abMk (f drX))
    rw [chiD0_abMk_iso_drX f] at h
    exact h
  rw [ht, show (2 : ℤ_[2]) * t = ((2 : ℕ) : ℤ_[2]) * t from by push_cast; ring,
    ← zpowZtwo_zpowZtwo, zpowZtwo_natCast] at hsq'
  -- push through the mod-16 reduction
  have hR : unitsMod16 (zpowZtwo isProP_two_unitsPadicInt
      ((unitNegThree⁻¹ ^ 2) ^ (2 : ℕ)) t) = 1 := by
    rw [map_zpowZtwo isProP_two_unitsPadicInt isProP_two_unitsZMod16 unitsMod16 _ t,
      show unitsMod16 ((unitNegThree⁻¹ ^ 2) ^ (2 : ℕ)) = 1 from unitsMod16_eta_four,
      zpowZtwo_one_base]
  have h1 : unitsMod16 (rootXUnit ^ 2) = 1 := by rw [hsq']; exact hR
  have h9 : ((unitsMod16 (rootXUnit ^ 2) : (ZMod (2 ^ 4))ˣ) : ZMod (2 ^ 4)) = 9 := by
    rw [unitsMod16_val, Units.val_pow_eq_pow_val, map_pow, val_rootXUnit,
      rootX_toZModPow_four]
    decide
  rw [h1] at h9
  exact absurd h9 (by decide)

/-! ## The `(u, b)`-correction data -/

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The torsion-square trick**: for any continuous isomorphism `e : D_R ≅ D₀` and any
`ℤ₂`-valued coordinate `κ` of `D₀^{ab}`, the relation `ȳ = t·x̄²` of `B_R` (with `t` of
order 2 and `ℤ₂` torsion-free) forces `κ(e(y)) = κ(e(x))²`. -/
private lemma coordHom_abMk_iso_drY
    (κ : ContinuousMonoidHom (topAbelianization (D0 : Type)) (Multiplicative ℤ_[2]))
    (e : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    κ (abMk (e drY)) = κ (abMk (e drX)) ^ 2 := by
  obtain ⟨BR⟩ := br_decomposition
  have htors : (abMk (drY * (drX ^ 2)⁻¹) : topAbelianization (DR : Type)) ^ 2 = 1 := by
    refine EquivLike.injective BR.e ?_
    rw [map_pow, BR.map_t, map_one, pow_two, ← ofAdd_add]
    rw [show ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2])) + (1, 0, 0) = (0, 0, 0) from by
      refine Prod.ext (by decide) (Prod.ext (by norm_num) (by norm_num))]
    rfl
  have htors' : (abMk (e (drY * (drX ^ 2)⁻¹)) : topAbelianization (D0 : Type)) ^ 2 = 1 := by
    have h2 : (abMk (e (drY * (drX ^ 2)⁻¹)) : topAbelianization (D0 : Type))
        = topAbCongr e (abMk (drY * (drX ^ 2)⁻¹)) := (topAbCongr_abMk' e _).symm
    rw [h2, ← map_pow, htors, map_one]
  have hval : κ (abMk (e (drY * (drX ^ 2)⁻¹))) = 1 := by
    have h3 := congrArg κ htors'
    rw [map_pow, map_one] at h3
    have h4 : (2 : ℕ) • (κ (abMk (e (drY * (drX ^ 2)⁻¹)))).toAdd = 0 := by
      rw [← toAdd_pow, h3, toAdd_one]
    rw [nsmul_eq_mul] at h4
    have h5 : (κ (abMk (e (drY * (drX ^ 2)⁻¹)))).toAdd = 0 := by
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd (by exact_mod_cast h) (two_ne_zero (α := ℤ_[2]))
      · exact h
    have h6 : κ (abMk (e (drY * (drX ^ 2)⁻¹)))
        = ofAdd (κ (abMk (e (drY * (drX ^ 2)⁻¹)))).toAdd := rfl
    rw [h6, h5, ofAdd_zero]
  have hfact : e drY = e (drY * (drX ^ 2)⁻¹) * e drX ^ 2 := by
    rw [← map_pow, ← map_mul, inv_mul_cancel_right]
  rw [hfact, map_mul, map_mul, map_pow, map_pow, hval, one_mul]

/-- The pair of mod-2 coordinates `(S̄₀, Ȳ₀) (mod 2)` of the abelianization, as a continuous
hom into `𝔽₂²`. -/
private noncomputable def pairMod2 : (D0 : Type) →* Multiplicative (Fin 2 → ZMod (2 ^ 1)) where
  toFun g := ofAdd ![PadicInt.toZModPow 1 ((sHom (abMk g)).toAdd),
    PadicInt.toZModPow 1 ((yHom (abMk g)).toAdd)]
  map_one' := by
    rw [← ofAdd_zero]
    congr 1
    funext j
    fin_cases j
    · show PadicInt.toZModPow 1 ((sHom (abMk (1 : (D0 : Type)))).toAdd) = 0
      rw [map_one, map_one, toAdd_one, map_zero]
    · show PadicInt.toZModPow 1 ((yHom (abMk (1 : (D0 : Type)))).toAdd) = 0
      rw [map_one, map_one, toAdd_one, map_zero]
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    funext j
    fin_cases j
    · show PadicInt.toZModPow 1 ((sHom (abMk (g * h))).toAdd)
        = PadicInt.toZModPow 1 ((sHom (abMk g)).toAdd)
          + PadicInt.toZModPow 1 ((sHom (abMk h)).toAdd)
      rw [map_mul, map_mul, toAdd_mul, map_add]
    · show PadicInt.toZModPow 1 ((yHom (abMk (g * h))).toAdd)
        = PadicInt.toZModPow 1 ((yHom (abMk g)).toAdd)
          + PadicInt.toZModPow 1 ((yHom (abMk h)).toAdd)
      rw [map_mul, map_mul, toAdd_mul, map_add]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma continuous_pairMod2 : Continuous pairMod2 := by
  refine continuous_ofAdd.comp (continuous_pi fun j => ?_)
  fin_cases j
  · exact continuous_toZModPow_one.comp (continuous_toAdd.comp
      (sHom.continuous_toFun.comp continuous_abMk))
  · exact continuous_toZModPow_one.comp (continuous_toAdd.comp
      (yHom.continuous_toFun.comp continuous_abMk))

/-- The `(S̄₀, Ȳ₀)`-coordinate matrix of `(f(s), f(x))`. -/
private noncomputable def coordMatrix (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    Matrix (Fin 2) (Fin 2) ℤ_[2] :=
  Matrix.of ![![(sHom (abMk (f drS))).toAdd, (yHom (abMk (f drS))).toAdd],
    ![(sHom (abMk (f drX))).toAdd, (yHom (abMk (f drX))).toAdd]]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma pairMod2_d0S : (pairMod2 d0S).toAdd = Pi.single (0 : Fin 2) (1 : ZMod (2 ^ 1)) := by
  funext j
  fin_cases j
  · show PadicInt.toZModPow 1 ((sHom (abMk d0S)).toAdd) = 1
    rw [sHom_S']
    show PadicInt.toZModPow 1 (1 : ℤ_[2]) = 1
    rw [map_one]
  · show PadicInt.toZModPow 1 ((yHom (abMk d0S)).toAdd) = 0
    rw [yHom_S']
    show PadicInt.toZModPow 1 (0 : ℤ_[2]) = 0
    rw [map_zero]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
private lemma pairMod2_d0Y : (pairMod2 d0Y).toAdd = Pi.single (1 : Fin 2) (1 : ZMod (2 ^ 1)) := by
  funext j
  fin_cases j
  · show PadicInt.toZModPow 1 ((sHom (abMk d0Y)).toAdd) = 0
    rw [sHom_Y']
    show PadicInt.toZModPow 1 (0 : ℤ_[2]) = 0
    rw [map_zero]
  · show PadicInt.toZModPow 1 ((yHom (abMk d0Y)).toAdd) = 1
    rw [yHom_Y']
    show PadicInt.toZModPow 1 (1 : ℤ_[2]) = 1
    rw [map_one]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The third transported generator has trivial mod-2 pair coordinates (`ȳ = t·x̄²`). -/
private lemma pairMod2_iso_drY (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    pairMod2 (f drY) = 1 := by
  have hs := coordHom_abMk_iso_drY sHom f
  have hy := coordHom_abMk_iso_drY yHom f
  rw [← ofAdd_zero]
  show ofAdd _ = _
  congr 1
  funext j
  fin_cases j
  · show PadicInt.toZModPow 1 ((sHom (abMk (f drY))).toAdd) = 0
    rw [hs, toAdd_pow, nsmul_eq_mul, map_mul,
      show ((2 : ℕ) : ℤ_[2]) = 2 from by push_cast; ring]
    rw [show PadicInt.toZModPow (p := 2) 1 (2 : ℤ_[2]) = 0 from by
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from by push_cast; ring, map_natCast]; decide]
    rw [zero_mul]
  · show PadicInt.toZModPow 1 ((yHom (abMk (f drY))).toAdd) = 0
    rw [hy, toAdd_pow, nsmul_eq_mul, map_mul,
      show ((2 : ℕ) : ℤ_[2]) = 2 from by push_cast; ring]
    rw [show PadicInt.toZModPow (p := 2) 1 (2 : ℤ_[2]) = 0 from by
      rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) from by push_cast; ring, map_natCast]; decide]
    rw [zero_mul]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The coordinate matrix is invertible** (same engine as `isUnit_evalMatrix`, with the
`ȳ`-row degenerate). -/
private lemma isUnit_coordMatrix (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    IsUnit (coordMatrix f) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  set Nb : Matrix (Fin 2) (Fin 2) (ZMod (2 ^ 1)) := (coordMatrix f).map (PadicInt.toZModPow 1)
    with hNb
  have hrow0 : Nb.row 0 = (pairMod2 (f drS)).toAdd := by
    funext j
    fin_cases j <;> rfl
  have hrow1 : Nb.row 1 = (pairMod2 (f drX)).toAdd := by
    funext j
    fin_cases j <;> rfl
  have hspan : ∀ v : Fin 2 → ZMod (2 ^ 1),
      v ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range Nb.row) := by
    have hmem : ∀ d : (D0 : Type), (pairMod2 d).toAdd
        ∈ Submodule.span (ZMod (2 ^ 1)) (Set.range Nb.row) := by
      intro d
      have h1 := mem_closure_gens_of_iso pairMod2 continuous_pairMod2 f d
      have h2 := toAdd_mem_span_of_mem_closure h1
      refine (Submodule.span_le.mpr ?_) h2
      rintro z (rfl | rfl | rfl)
      · exact Submodule.subset_span ⟨0, hrow0⟩
      · exact Submodule.subset_span ⟨1, hrow1⟩
      · rw [pairMod2_iso_drY f]
        show (1 : Multiplicative (Fin 2 → ZMod (2 ^ 1))).toAdd ∈ _
        exact Submodule.zero_mem _
    intro v
    have hv : v = ∑ i, v i • Pi.single (M := fun _ => ZMod (2 ^ 1)) i 1 := by
      funext k
      simp [Pi.single_apply]
    rw [hv]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    fin_cases i
    · exact pairMod2_d0S ▸ hmem d0S
    · exact pairMod2_d0Y ▸ hmem d0Y
  have hNbUnit : IsUnit Nb := by
    rw [← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    have hv := hspan v
    rw [← range_vecMulLinear, LinearMap.mem_range] at hv
    obtain ⟨c, hc⟩ := hv
    exact ⟨c, hc⟩
  have hdet2 : PadicInt.toZModPow 1 ((coordMatrix f).det) = 1 := by
    have hmap : PadicInt.toZModPow 1 ((coordMatrix f).det) = Nb.det := by
      rw [hNb, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [hmap]
    exact zmod2_eq_one_of_isUnit ((Matrix.isUnit_iff_isUnit_det Nb).mp hNbUnit)
  exact isUnit_of_toZModPow_one_eq_one' hdet2

/-- **The correction data**: `(u, b)` with `σ₁u + τ₁b = 1`, `σ₂u + τ₂b = 0`, and `u` odd. -/
private lemma exists_correction (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    ∃ u b : ℤ_[2],
      (sHom (abMk (f drS))).toAdd * u + (yHom (abMk (f drS))).toAdd * b = 1 ∧
      (sHom (abMk (f drX))).toAdd * u + (yHom (abMk (f drX))).toAdd * b = 0 ∧
      PadicInt.toZModPow 1 u = 1 := by
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr (isUnit_coordMatrix f)) ![1, 0]
  have h0 := congrFun hc 0
  have h1 := congrFun hc 1
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  have hS1 : (sHom (abMk (f drS))).toAdd * c 0 + (yHom (abMk (f drS))).toAdd * c 1 = 1 := h0
  have hX0 : (sHom (abMk (f drX))).toAdd * c 0 + (yHom (abMk (f drX))).toAdd * c 1 = 0 := h1
  refine ⟨c 0, c 1, hS1, hX0, ?_⟩
  -- mod-2 parity: `τ₂ = 1 (mod 2)` forces `u` odd
  have hm1 := congrArg (PadicInt.toZModPow (p := 2) 1) hS1
  have hm2 := congrArg (PadicInt.toZModPow (p := 2) 1) hX0
  rw [map_add, map_mul, map_mul, map_one] at hm1
  rw [map_add, map_mul, map_mul, map_zero, toZModPow_one_tau f] at hm2
  have hdec : ∀ s1 t1 s2 uu bb : ZMod (2 ^ 1),
      s1 * uu + t1 * bb = 1 → s2 * uu + 1 * bb = 0 → uu = 1 := by decide
  exact hdec _ _ _ _ _ hm1 hm2

/-! ## The corrected isomorphism and the keystone -/

/-- The middle (`S̄₀`)-coordinate functional of the coordinate group. -/
private noncomputable def midCoordHom :
    ContinuousMonoidHom (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) (Multiplicative ℤ_[2]) where
  toFun z := ofAdd z.toAdd.2.1
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_ofAdd.comp
    (continuous_fst.comp (continuous_snd.comp continuous_toAdd))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The forced `Ā`-row of the coordinate frame: `Ā = t − 2S̄ ↦ (1, −2, 0)`. -/
private lemma bE_A (B0 : BDecomposition) :
    B0.e (abMk d0A) = ofAdd ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2])) := by
  have hdec : (abMk d0A : topAbelianization (D0 : Type))
      = abMk (d0A * d0S ^ 2) * ((abMk d0S) ^ 2)⁻¹ := by
    rw [map_mul, map_pow, mul_inv_cancel_right]
  rw [hdec, map_mul, map_inv, map_pow, B0.map_t, B0.map_S, pow_two, ← ofAdd_add, ← ofAdd_neg,
    ← ofAdd_add]
  congr 1
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · show (1 : ZMod 2) + -((0 : ZMod 2) + 0) = 1
    decide
  · show (0 : ℤ_[2]) + -((1 : ℤ_[2]) + 1) = -2
    ring
  · show (0 : ℤ_[2]) + -((0 : ℤ_[2]) + 0) = 0
    ring

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `sHom` reads off the middle `B0.e`-coordinate. -/
private lemma sHom_eq_mid (B0 : BDecomposition) (z : topAbelianization (D0 : Type)) :
    sHom z = midCoordHom (B0.e z) := by
  have h := d0ab_hom_ext PropOneOne.isProP_two_multPadicInt sHom
    (midCoordHom.comp ⟨B0.e.toMulEquiv.toMonoidHom, B0.e.continuous_toFun⟩) ?_ ?_ ?_ z
  · exact h
  · show sHom (abMk d0A) = midCoordHom (B0.e (abMk d0A))
    rw [sHom_A', bE_A B0]
    rfl
  · show sHom (abMk d0S) = midCoordHom (B0.e (abMk d0S))
    rw [sHom_S', B0.map_S]
    rfl
  · show sHom (abMk d0Y) = midCoordHom (B0.e (abMk d0Y))
    rw [sHom_Y', B0.map_Y]
    rfl

/-- The `(u, b)`-combination functional `z ↦ σ(z)·u + τ(z)·b` (multiplicatively). -/
private noncomputable def comboHom (u b : ℤ_[2]) :
    ContinuousMonoidHom (topAbelianization (D0 : Type)) (Multiplicative ℤ_[2]) where
  toFun z := ofAdd ((sHom z).toAdd * u + (yHom z).toAdd * b)
  map_one' := by
    show ofAdd ((sHom (1 : topAbelianization (D0 : Type))).toAdd * u
      + (yHom (1 : topAbelianization (D0 : Type))).toAdd * b) = 1
    rw [show sHom (1 : topAbelianization (D0 : Type)) = 1 from map_one _,
      show yHom (1 : topAbelianization (D0 : Type)) = 1 from map_one _,
      toAdd_one, zero_mul, zero_mul, add_zero, ofAdd_zero]
  map_mul' a c := by
    show ofAdd ((sHom (a * c)).toAdd * u + (yHom (a * c)).toAdd * b) = _
    rw [show sHom (a * c) = sHom a * sHom c from map_mul _ _ _,
      show yHom (a * c) = yHom a * yHom c from map_mul _ _ _, toAdd_mul, toAdd_mul,
      ← ofAdd_add]
    congr 1
    ring
  continuous_toFun := continuous_ofAdd.comp (Continuous.add
    ((continuous_toAdd.comp sHom.continuous_toFun).mul continuous_const)
    ((continuous_toAdd.comp yHom.continuous_toFun).mul continuous_const))

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The `prop_3_8_lift` automorphism's `S̄₀`-coordinate is the `(u, b)`-combination of the
original coordinates — the abelianized action of the correction. -/
private lemma sHom_psi (B0 : BDecomposition) (Ψ : ContinuousMulEquiv (D0 : Type) (D0 : Type))
    (u b : ℤ_[2])
    (hA : B0.e (abMk (Ψ d0A)) = Multiplicative.ofAdd (1, -2 * u, 0))
    (hS : B0.e (abMk (Ψ d0S)) = Multiplicative.ofAdd (0, u, 0))
    (hY : B0.e (abMk (Ψ d0Y)) = Multiplicative.ofAdd (0, b, 1))
    (z : topAbelianization (D0 : Type)) :
    sHom (topAbCongr Ψ z) = comboHom u b z := by
  have h := d0ab_hom_ext PropOneOne.isProP_two_multPadicInt
    (sHom.comp ⟨(topAbCongr Ψ).toMulEquiv.toMonoidHom, (topAbCongr Ψ).continuous_toFun⟩)
    (comboHom u b) ?_ ?_ ?_ z
  · exact h
  · show sHom (topAbCongr Ψ (abMk d0A)) = comboHom u b (abMk d0A)
    rw [topAbCongr_abMk', sHom_eq_mid B0, hA]
    show ofAdd (-2 * u)
      = ofAdd ((sHom (abMk d0A)).toAdd * u + (yHom (abMk d0A)).toAdd * b)
    rw [sHom_A', yHom_A']
    show ofAdd (-2 * u) = ofAdd ((-2 : ℤ_[2]) * u + (0 : ℤ_[2]) * b)
    congr 1
    ring
  · show sHom (topAbCongr Ψ (abMk d0S)) = comboHom u b (abMk d0S)
    rw [topAbCongr_abMk', sHom_eq_mid B0, hS]
    show ofAdd u = ofAdd ((sHom (abMk d0S)).toAdd * u + (yHom (abMk d0S)).toAdd * b)
    rw [sHom_S', yHom_S']
    show ofAdd u = ofAdd ((1 : ℤ_[2]) * u + (0 : ℤ_[2]) * b)
    congr 1
    ring
  · show sHom (topAbCongr Ψ (abMk d0Y)) = comboHom u b (abMk d0Y)
    rw [topAbCongr_abMk', sHom_eq_mid B0, hY]
    show ofAdd b = ofAdd ((sHom (abMk d0Y)).toAdd * u + (yHom (abMk d0Y)).toAdd * b)
    rw [sHom_Y', yHom_Y']
    show ofAdd b = ofAdd ((0 : ℤ_[2]) * u + (1 : ℤ_[2]) * b)
    congr 1
    ring

/-- **The matching isomorphism** (⟦prop:markedpro2⟧ engine, note §3.3): from any abstract
continuous isomorphism `D_R ≅ D₀` (the B-Lab input) there is a **marked** one — a corrected
`F = Ψ_{u,b} ∘ f` whose `S̄₀`-coordinate takes the unramified marking values `(1, 0, 0)` on
the generators of `D_R`.  (Stated on generator values; the consumer `markedPro2_R` runs the
`dr_topGen` density argument against `ν_{D_R}`, which lives downstream.)  Everything upstream
(orientation functoriality, the `τ₂`-parity, the coordinate solve, `prop_3_8_lift`) is
packaged here. -/
theorem exists_matching_iso (hex : Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type))) :
    ∃ F : ContinuousMulEquiv (DR : Type) (D0 : Type),
      sHom (abMk (F drS)) = ofAdd (1 : ℤ_[2]) ∧
      sHom (abMk (F drX)) = 1 ∧ sHom (abMk (F drY)) = 1 := by
  obtain ⟨f⟩ := hex
  obtain ⟨B0⟩ := b_decomposition
  obtain ⟨u, b, hS1, hX0, humod⟩ := exists_correction f
  have huUnit : IsUnit u := isUnit_of_toZModPow_one_eq_one' humod
  obtain ⟨Ψ, hΨA, hΨS, hΨY⟩ := SectionThree.prop_3_8_lift B0 huUnit.unit b
  rw [huUnit.unit_spec] at hΨA hΨS
  refine ⟨f.trans Ψ, ?_, ?_, ?_⟩
  · show sHom (abMk (Ψ (f drS))) = ofAdd (1 : ℤ_[2])
    rw [← topAbCongr_abMk' Ψ (f drS), sHom_psi B0 Ψ u b hΨA hΨS hΨY]
    show ofAdd ((sHom (abMk (f drS))).toAdd * u + (yHom (abMk (f drS))).toAdd * b)
      = ofAdd (1 : ℤ_[2])
    rw [hS1]
  · show sHom (abMk (Ψ (f drX))) = 1
    rw [← topAbCongr_abMk' Ψ (f drX), sHom_psi B0 Ψ u b hΨA hΨS hΨY]
    show ofAdd ((sHom (abMk (f drX))).toAdd * u + (yHom (abMk (f drX))).toAdd * b) = 1
    rw [hX0, ofAdd_zero]
  · have hY2 := coordHom_abMk_iso_drY sHom (f.trans Ψ)
    rw [hY2]
    have hvX : sHom (abMk ((f.trans Ψ) drX)) = 1 := by
      show sHom (abMk (Ψ (f drX))) = 1
      rw [← topAbCongr_abMk' Ψ (f drX), sHom_psi B0 Ψ u b hΨA hΨS hΨY]
      show ofAdd ((sHom (abMk (f drX))).toAdd * u + (yHom (abMk (f drX))).toAdd * b) = 1
      rw [hX0, ofAdd_zero]
    rw [hvX, one_pow]

/-- **The `prop_1_1` unramified rows compute `sHom`** — the `D₀`-side density bridge the
`markedPro2_R` assembly consumes: if `e₁ : G_{ℚ₂}(2) ≅ D₀` has the `prop_1_1` unramified
coordinates `(−2, 1, 0)` at `(A, S₀, Y₀)` (read through arbitrary lifts), then
`ν̄_ur ∘ e₁⁻¹ = sHom ∘ abMk` everywhere (density over `topGen_d0`). -/
theorem nuUrBar_symm_eq_sHom (R : LocalReciprocity)
    (e₁ : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (D0 : Type))
    (hA : ∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e₁.symm d0A →
      R.nu_ur (toAb g) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2]))
    (hS : ∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e₁.symm d0S →
      R.nu_ur (toAb g) = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2]))
    (hY : ∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e₁.symm d0Y →
      R.nu_ur (toAb g) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2]))
    (d : (D0 : Type)) : PropOneOne.nuUrBar R (e₁.symm d) = sHom (abMk d) := by
  have h := monoidHom_eq_of_topGen
    (f := (PropOneOne.nuUrBar R).toMonoidHom.comp e₁.symm.toMulEquiv.toMonoidHom)
    (g := sHom.toMonoidHom.comp abMk)
    ((PropOneOne.nuUrBar R).continuous_toFun.comp e₁.symm.continuous_toFun)
    (sHom.continuous_toFun.comp continuous_abMk)
    topGen_d0 ?_
  · exact h d
  · rintro w (rfl | rfl | rfl)
    · show PropOneOne.nuUrBar R (e₁.symm d0A) = sHom (abMk d0A)
      obtain ⟨gA, hgA⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) (e₁.symm d0A)
      have hgA' : maxProPMk 2 AbsGalQ2 gA = e₁.symm d0A := hgA
      rw [← hgA', PropOneOne.nuUrBar_maxProPMk, hA gA hgA', sHom_A']
      exact congrArg ofAdd (by push_cast; ring)
    · show PropOneOne.nuUrBar R (e₁.symm d0S) = sHom (abMk d0S)
      obtain ⟨gS, hgS⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) (e₁.symm d0S)
      have hgS' : maxProPMk 2 AbsGalQ2 gS = e₁.symm d0S := hgS
      rw [← hgS', PropOneOne.nuUrBar_maxProPMk, hS gS hgS', sHom_S']
      exact congrArg ofAdd (by push_cast; ring)
    · show PropOneOne.nuUrBar R (e₁.symm d0Y) = sHom (abMk d0Y)
      obtain ⟨gY, hgY⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) (e₁.symm d0Y)
      have hgY' : maxProPMk 2 AbsGalQ2 gY = e₁.symm d0Y := hgY
      rw [← hgY', PropOneOne.nuUrBar_maxProPMk, hY gY hgY', sHom_Y']
      exact congrArg ofAdd (by push_cast; ring)

/-! ## Stress lemmas (plan rule 9) -/

/-- **Stress test (group-level orientation values)** ⟦eq:chi0⟧:
`χ₀(A, S₀, Y₀) = (−1, 1, (−3)⁻¹)`. -/
theorem chiD0G_values :
    chiD0G d0A = -1 ∧ chiD0G d0S = 1 ∧ chiD0G d0Y = unitNegThree⁻¹ :=
  ⟨chiD0G_A, chiD0G_S, chiD0G_Y⟩

/-- **Stress test (orientation functoriality, `X`-value)**: the pulled-back canonical
orientation agrees with `χ_R` on the wild generator — `χ₀(f(x)) = χ_R(x) = X`, the Hensel
root, for **every** continuous isomorphism `f : D_R ≅ D₀`. -/
theorem chiD0G_iso_drX (f : ContinuousMulEquiv (DR : Type) (D0 : Type)) :
    chiD0G (f drX) = chiR drX :=
  DFunLike.congr_fun (chiD0G_comp_iso_eq_chiR f) drX

end Masters
