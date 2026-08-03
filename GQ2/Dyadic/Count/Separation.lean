/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.HTwo
import GQ2.Dyadic.Recursion.Phase140Assembly
import GQ2.Dyadic.LiftingDualityG
import GQ2.Half139Local

/-!
# Dyadic campaign, ticket CB-4: the separation clauses

The two `SourceDataN` clauses that are **not** counts:

* `hpartial : ∀ χ ≠ 0, ∃ c, β_χ(c) ≠ β_χ(0)`  (`GQ2/Dyadic/SourceDataN.lean:243`) — §3/§4;
* `hsep     : (∀ χ, β_χ(c) = 0) → TLiftable c` (`GQ2/Dyadic/SourceDataN.lean:229`) — §6/§7.

Both are proved over the abstract carrier `(D : RadicalCoverData Bg, DD : DescData D)` at a
variable source group `Γ`, so **one theorem each serves both sides of the two-sided comparison
and all five frozen branch families**: neither clause mentions the branch word, the marking, or
any numeric leaf, so there is nothing per-family to specialize.

## The degree check, done before any porting  (the CB-SG discipline)

CB-SG proved that a verbatim `ℚ₂ → K` transcription of the *count* clause is **false**: the
`ℚ₂` Euler characteristic carries `2^{v₂(#A)}` and `G_K`'s carries `2^{d·v₂(#A)}`, so `#Z¹(A)`
reads `#A^{d+1}·#fixedPts`, not `#A²·#fixedPts`.  So no `ℚ₂` counting statement may be ported
without checking its exponents first.  For these two clauses the check comes out **clean, and
provably so** — for three independent reasons:

1. **Neither statement contains a cardinality.**  `hpartial` concludes `∃ c, β_χ c ≠ β_χ 0`;
   `hsep` concludes `TLiftable hσ c`.  Neither mentions `Nat.card`, `SN`, or `n`.  There is no
   exponent to shift.
2. **`standardNumerics` agrees.**  `SourceNumerics` has exactly five moving leaves —
   `homScalar`, `mMult`, `tMult`, `h1Mult`, `gaussUnram`/`gaussRam` — and every one of them is
   a count.  `SourceDataN`'s own field-delta docstring (`SourceDataN.lean:41-46`) lists `hsep`
   and `hpartial` under **"unchanged — verbatim"**, never under "revalued".  Had the generic
   statement here disagreed with `standardNumerics`, the statement would have been the wrong
   one; it does not disagree, because these clauses read no numeric leaf at all.
3. **Their cohomological input is degree-uniform, and this file makes that machine-checked.**
   The `ℚ₂` proofs run on `prop_5_16`'s cup clause (iv).  CB-SG's `Γ`-generic
   `bijective_cup11_dualEvalG` (`GQ2/Dyadic/LiftingDualityG.lean:421`) carries the degree as
   `{d : ℕ} (hE : LocalEulerChar Γ d)` with `d` **implicit and absent from the conclusion**,
   while the count clause `card_Z1_eqG` (`:265`) has `d` in the exponent.  §2's
   `cup11_rightSepG` is sharper still: the right-slot half needs **no Euler hypothesis at
   all**, so the separation input is not merely degree-uniform, it is degree-*free*.  The
   degree lives in the counts and nowhere else — perfectness of Tate's pairings holds over
   every local field.

## What is generic, and where the fork is

The whole `TCharC`/`VCocycle`/`betaChi`/`TLiftable` layer (`GQ2/VLiftCount.lean`,
`GQ2/KeystoneDelta/*`, `GQ2/Phase140/Obstruction.lean`) is **already** stated over a variable
source group `Γ` and an abstract `(D : RadicalCoverData Bg, DD : DescData D)`.  What was pinned
is only the *inputs*, and the `ℚ₂` campaign supplies them twice, by two disjoint routes:

| input | `G_ℚ₂` route (`Phase140/Local.lean`) | `Γ_A` route (`Phase140/GammaA/Hsep.lean`) |
|---|---|---|
| the ambient action is trivial | `htriv_local'` | `htriv_gammaA` |
| `#H²(Γ,𝔽₂) = 2` | `card_H2_zmod2_eq_two` (B6/B7) | `CardH2GammaA.card_H2_gammaA` (word) |
| right-slot separation | `cup11_dualEval_right_separating` (B6) | `b1_of_pair_cochain_B2` (`prop_5_15`) |
| `(M^∨)^C = 0` (Lemma 7.1) | `mchar_conj_invariant_eq_zero` | the same lemma |

Rows one and two are *other fields of the same record* (`SourceDataN.htriv`,
`SourceDataN.cardH2` — the latter proved over this same carrier by CB-H2), and row four is
**frame-level**: source-free, shared verbatim by both sides.  So exactly one input forks, and
§2 names it: `IsRightSeparating Γ A`, stated **cup-free** so that neither side's vocabulary
appears in it.  `hpartialN` (§3) takes it as a binder; §2 supplies it from a `TateDualityG`
bundle at *any* degree (the arithmetic side, hence ASK at every `K`), and the candidate side
supplies the same proposition from `IsSelfDualN`'s clause-3 right-slot nondegeneracy through
CB-1's comparison — which is why the clause is generic across all five frozen branch families
in one theorem: **neither clause mentions the branch word**, so there is nothing per-family to
specialize.

## The `hsimp` ruling

Owner ruling B1/Q3: module simplicity is threaded as a hypothesis and never an axiom.  It is
not needed here — neither `hpartialN` nor its field goal carries a simplicity binder.  The
`ℚ₂` proofs of these two clauses do not use `hsimple` either (only `hZcard` and the Gauss
leaves do).  Nothing was assumed and nothing was axiomatized.

## Section map

| § | content | status |
|---|---|---|
| 1 | the `(t,v)`-coordinatization of `M` over the abstract carrier | new, 12 ln |
| 2 | `IsRightSeparating` — `hpartial`'s fork, named; arithmetic supplier, **degree-free** | closed |
| 3 | **`hpartialN`** — the clause over the abstract carrier | **CLOSED** (3 binders) |
| 4 | the verbatim `SourceDataN.hpartial` field goal at a frame | closed |
| 5 | `IsTwoSeparating` — `hsep`'s fork, named; arithmetic supplier | closed |
| 6 | **`hsepN`** — the clause over the abstract carrier | **CLOSED** (3 binders) |
| 7 | the verbatim `SourceDataN.hsep` field goal at a frame | closed |

## The sizing prediction was inverted

CB-2 sized `hpartial` at ≈700 generic lines and `hsep` at ≈1500+, and named `hsep` as where the
count lane's real risk sits — on the ground that `hsep` has *two disjoint* `ℚ₂` proofs "with no
common generic core".  Measured here, the opposite holds, and for a reason worth recording:
once the fork is spelled **cup-free**, `hsep`'s body loses its entire `cup20`/`H2mk` layer —
stage 4 collapses to the observation that the invariant-dual pushforward of `tDef` *is* `chiDef`
at the induced character, definitionally.  `hsepN` therefore carries **three** binders and
**none** of `#H²(Γ,𝔽₂) = 2`, `htriv`, `hpair`, or module simplicity, where `hpartialN` needs
the first two.  `hsep` is the lighter clause.

CB-2's "no common generic core" reading is still correct about the *`ℚ₂` proofs*: the marking
route and the `cup20` route share nothing. What it missed is that they share a **statement** —
and the statement, not the proof, is what a generic clause needs to factor through.  The
`ℚ₂` audit corroborates the second half of this: `sep_word` (the marking route's engine)
consumes **only** `IsSelfDual`'s clause 1, `#H²w(A) = #H⁰w(A^∨)` — `wTrace_surjective`
destructures the payload as `⟨hsd_card, -, -⟩` and discards clauses 2 and 3.  Clause 1 is
exactly `IsSelfDualN.cardH2`, which is *not* the clause carrying the degree.  So the count
clause's `#A^{n+1}` trap is provably off `hsep`'s path.

## Import discipline

Plain-import.  `GQ2.Dyadic.Count.HTwo` (CB-H2) is plain; `GQ2.Dyadic.Recursion.Phase140Assembly`
(SD-R3) is plain and carries the `rhoPrimeK`/`BoundaryLiftsK` vocabulary the field goal is
stated in, together with `GQ2/Phase140/Assembly.lean`'s `descSections`/`descSigma_spec`;
`GQ2.Half139Local` carries the frame-level `(M^∨)^C = 0`.  `GQ2.Dyadic.LiftingDualityG` (CB-SG)
is a `module` file, and a plain file may import a module file — the module rule is one-way.

Axioms: **no new axioms, no `sorry`**.  All fifteen declarations print exactly the standard three
(`propext`, `Classical.choice`, `Quot.sound`) — measured, not budgeted.  `decide` occurs only
at kernel-decidable `ZMod 2` character identities (the `hchar`/`hfin` steps), as in the `ℚ₂`
proof.
-/

namespace GQ2.Dyadic.Count

open GQ2 GQ2.SectionEight GQ2.SectionEight.CentralObstruction GQ2.SectionEight.AffineTLift
open GQ2.FoxH ContCoh GQ2.Dyadic.LiftingDualityG GQ2.LocalLiftingDuality

/-! ## §1. The `(t, v)`-coordinatization of `M`, over the abstract carrier -/

section Coordinatization

variable {Bg : Type} [Group Bg] [Finite Bg] {D : RadicalCoverData Bg} {DD : DescData D}
  {σ : DD.C0 →* Bg ⧸ D.T}

/-- **The `T`-part of the `(t, v)`-coordinatization**: for `m ∈ M`, dividing off the `V`-section
`mV (descend m)` lands in the polar radical `T = ker descend`. -/
theorem tPartN (S : CountSections DD σ) (m : ↥D.M) :
    ((m * (S.mV (Multiplicative.toAdd (DD.descend m)))⁻¹ : ↥D.M) : Bg) ∈ D.T := by
  refine (DD.hdesc_ker _).mp ?_
  rw [map_mul, map_inv, S.descend_mV, ofAdd_toAdd, mul_inv_cancel]

/-- The `V`-coordinate `vco m := toAdd (descend m)` is additive. -/
theorem vcoMulN (m m' : ↥D.M) :
    Multiplicative.toAdd (DD.descend (m * m'))
      = Multiplicative.toAdd (DD.descend m) + Multiplicative.toAdd (DD.descend m') := by
  rw [map_mul]; rfl

end Coordinatization

/-! ## §2. The fork, named — and its arithmetic supplier -/

section RightSeparatingDef

variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] [DistribMulAction Γ (ZMod 2)]
  (A : Type) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction Γ (ElemDual A)]

/-- **Right-slot separation for `(Γ, A)`** — the one input on which the two `ℚ₂` proofs of
`hpartial` diverge, isolated and stated *cup-free*: a continuous dual `1`-cocycle `ξ` whose pair
cochain `(a, b) ↦ ξ(a)(a • z(b))` is a continuous coboundary against **every** `A`-cocycle `z` is
itself a coboundary.

The elementary spelling is deliberate.  The arithmetic side reads it as the right-slot half of
Tate's `(1,1)` pairing (§2, `isRightSeparating_of_tateDualityG`); the candidate side reads the
*same* proposition as the right-slot half of the word pairing `stokesChi1` through CB-1's
comparison.  Neither vocabulary appears here, so one binder serves both — and, on the candidate
side, all five frozen branch families at once. -/
def IsRightSeparating : Prop :=
  ∀ ξ : ↥(Z1 Γ (ElemDual A)),
    (∀ zc : ↥(Z1 Γ A), (fun p : Γ × Γ => (ξ.1 p.1) (p.1 • zc.1 p.2)) ∈ B2 Γ (ZMod 2)) →
    ∃ n : ElemDual A, dZero Γ (ElemDual A) n = ξ.1

end RightSeparatingDef

section RightSeparation

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  [DistribMulAction Γ (ZMod 2)]
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction Γ (ElemDual A)] [ContinuousSMul Γ (ElemDual A)]

/-- **`cup11` right-slot separation at a general `Γ`**. -/
theorem cup11_rightSepG (Dl : TateDualityG Γ 2)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam)
    (ξ : H1 Γ (ElemDual A))
    (hvan : ∀ z : H1 Γ A, cup11 (dualEval A) hpair z ξ = 0) :
    ξ = 0 := by
  classical
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => (two_nsmul x).trans (hA₂ x)
  have hμNe := muNTwoEquiv_equivariantG (Γ := Γ) htriv
  have heD := edEquivariantG hpair htriv
  obtain ⟨d'', rfl⟩ := (H1congr dualAddEquiv heD).surjective ξ
  have key : ∀ z : H1 Γ A,
      cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' z = 0 := by
    intro z
    have h1 : cup11 (dualEval A) hpair z (H1congr dualAddEquiv heD d'')
        = H2congr muNTwoEquiv hμNe
            (cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' z) := by
      rw [cup11_comm (dualEval A) hpair (fun p => CharTwo.add_self_eq_zero p) z
        (H1congr dualAddEquiv heD d'')]
      obtain ⟨a', rfl⟩ := H1mk_surjective (G := Γ) (M := MuDual 2 A) d''
      obtain ⟨bz, rfl⟩ := H1mk_surjective (G := Γ) (M := A) z
      rw [H1congr_mk, cup11_mk_mk, cup11_mk_mk, H2congr_mk]
      congr 1
    have h2 := hvan z
    rw [h1] at h2
    exact (AddEquiv.map_eq_zero_iff _).mp h2
  have hd0 : d'' = 0 := by
    refine (Dl.perfect11 A htor).1 ?_
    ext z
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, key z, map_zero,
      AddMonoidHom.zero_apply]
  rw [hd0, map_zero]

/-- **The arithmetic supplier of the fork.**  A Tate-duality bundle at `Γ` gives
`IsRightSeparating Γ A`: the pair cochain `(a, b) ↦ ξ(a)(a • z(b))` **is** the flipped
`cup11` cochain, so universal `B²`-membership is universal cup-vanishing, `cup11_rightSepG`
kills the class, and `B¹`-extraction returns the `n`.

**No `LocalEulerChar`, no degree.**  This is the Lean-checked form of this file's degree check:
where CB-SG's count clause needed `#A^{d+1}`, the separation clause needs nothing about `d` at
all.  Instantiating `Dl` at `tateDualityGalK K` (FD1) supplies `hpartial` at every `K`. -/
theorem isRightSeparating_of_tateDualityG (Dl : TateDualityG Γ 2)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    IsRightSeparating Γ A := by
  intro ξ hvan
  have hξ0 : H1mk Γ (ElemDual A) ξ = 0 := by
    refine cup11_rightSepG Dl hA₂ htriv hpair _ ?_
    intro z
    obtain ⟨zc, rfl⟩ := H1mk_surjective (G := Γ) (M := A) z
    rw [cup11_comm (dualEval A) hpair (fun p => CharTwo.add_self_eq_zero p)
      (H1mk Γ A zc) (H1mk Γ (ElemDual A) ξ), cup11_mk_mk, H2mk_eq_zero_iff]
    show cup11Fun ((dualEval A).flip) ξ.1 zc.1 ∈ B2 Γ (ZMod 2)
    have hid : cup11Fun ((dualEval A).flip) ξ.1 zc.1
        = fun p : Γ × Γ => (ξ.1 p.1) (p.1 • zc.1 p.2) := by
      funext p
      show ((dualEval A).flip (ξ.1 p.1)) (p.1 • zc.1 p.2) = _
      rw [AddMonoidHom.flip_apply, dualEval_apply]
    rw [hid]
    exact hvan zc
  exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff ξ).mp hξ0)

end RightSeparation

/-! ## §3. `SourceDataN.hpartial`, over the abstract carrier -/

section HPartial

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
  [DistribMulAction Γ DD.Vmod] [ContinuousSMul Γ DD.Vmod]
  [TopologicalSpace (ElemDual DD.Vmod)] [DiscreteTopology (ElemDual DD.Vmod)]
  [ContinuousSMul Γ (ElemDual DD.Vmod)]
  {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
  (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
  {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

omit [ContinuousSMul Γ (ZMod 2)] [ContinuousSMul Γ DD.Vmod]
  [ContinuousSMul Γ (ElemDual DD.Vmod)] in
/-- **`SourceDataN.hpartial` over the abstract carrier** — nondegeneracy of the obstruction
pairing in the character: every nonzero `χ ∈ (T^∨)^C` is detected by some `V`-coordinate.

`Phase140.Local.hpartial_local`'s nine stages with `AbsGalQ2` replaced by a variable `Γ` and
the three `ℚ₂`-specific inputs promoted to binders: `htriv` (the ambient scalar action is
trivial — `SourceDataN.htriv`), `hH2` (`#H²(Γ,𝔽₂) = 2` — `SourceDataN.cardH2`, which CB-H2
proves over this same carrier), and `hrsep` (**the fork**).  `hMchar` is Lemma 7.1,
`(M^∨)^C = 0`; it is frame-level and source-free, so at the recursion frame it is the theorem
`GQ2.SectionEight.mchar_conj_invariant_eq_zero RF En l h`, shared by both sides verbatim.

Everything else is `Γ`-generic already: `exists_splitting_of_symm_zero_diag`,
`isEquivariantFactorSet_datChi`, `chiDef_decomp`, `cupChi_zero`, `gPart_mem_B2`,
`chiDef_mem_Z2`, `iotaB_add`.  No exponent occurs anywhere in the statement, so there is no
degree to shift (see the file header). -/
theorem hpartialN
    (hact : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD rho γ • v)
    (hrhosurj : Function.Surjective (rho0 DD rho))
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hrsep : IsRightSeparating Γ DD.Vmod)
    (hMchar : ∀ ψ : ↥D.M → ZMod 2, (∀ m m' : ↥D.M, ψ (m * m') = ψ m + ψ m') →
      (∀ (bb : Bg) (m : ↥D.M) (hm : bb * (m : Bg) * bb⁻¹ ∈ D.M),
        ψ ⟨bb * (m : Bg) * bb⁻¹, hm⟩ = ψ m) → ∀ m : ↥D.M, ψ m = 0)
    (χ : ↥(TCharC D)) (hχ : χ ≠ 0) :
    ∃ c : VCocycle DD rho, betaChi S hσ χ c ≠ betaChi S hσ χ (0 : VCocycle DD rho) := by
  classical
  by_contra hno
  rw [not_exists] at hno
  have hall : ∀ c : VCocycle DD rho, betaChi S hσ χ c = betaChi S hσ χ 0 :=
    fun c => not_not.mp (hno c)
  have hA₂ : ∀ v : DD.Vmod, v + v = 0 := fun v => Vmod_exp2 DD v
  -- ### Stage 1: split `χ ∘ mDef` (the `betaChi_affine` splitting)
  obtain ⟨gχ, hg0, hg⟩ := exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => χ.1 (mDef DD S v w))
    (fun v w x => (isEquivariantFactorSet_datChi S hσ χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])
  -- ### Stage 2: the cup part of every difference vanishes
  have hiotaB_shift : ∀ (φ β : Γ × Γ → ZMod 2),
      β ∈ B2 Γ (ZMod 2) → iotaB (φ + β) = iotaB φ := by
    intro φ β hβ
    unfold iotaB
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((AddSubgroup.add_mem_cancel_right _ hβ).mp h1) h2
    · exact absurd ((AddSubgroup.add_mem_cancel_right _ hβ).mpr h2) h1
    · rfl
  have hcup : ∀ c : VCocycle DD rho, iotaB (cupChi DD S rho hσ gχ χ c) = 0 := by
    intro c
    have hB : ((fun p : Γ × Γ => gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
        + (fun p : Γ × Γ =>
          gχ ((0 : VCocycle DD rho).c (p.1 * p.2)) + gχ ((0 : VCocycle DD rho).c p.1)
            + gχ ((0 : VCocycle DD rho).c p.2))) ∈ B2 Γ (ZMod 2) :=
      AddSubgroup.add_mem _ (gPart_mem_B2 hσ htriv gχ c) (gPart_mem_B2 hσ htriv gχ 0)
    have hdecomp : chiDef S hσ χ c + chiDef S hσ χ (0 : VCocycle DD rho)
        = cupChi DD S rho hσ gχ χ c
          + ((fun p : Γ × Γ => gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
            + (fun p : Γ × Γ =>
              gχ ((0 : VCocycle DD rho).c (p.1 * p.2)) + gχ ((0 : VCocycle DD rho).c p.1)
                + gχ ((0 : VCocycle DD rho).c p.2))) := by
      funext p
      have h1 := chiDef_decomp S hσ χ gχ hg c p
      have h2 := chiDef_decomp S hσ χ gχ hg (0 : VCocycle DD rho) p
      have h3 := cupChi_zero (ρ := rho) S hσ χ gχ hg0 p
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]; try ring_nf))
        h1 + h2 + h3
    have hiota : iotaB (chiDef S hσ χ c + chiDef S hσ χ (0 : VCocycle DD rho)) = 0 := by
      rw [iotaB_add hH2 (chiDef_mem_Z2 S hσ htriv χ c)
        (chiDef_mem_Z2 S hσ htriv χ (0 : VCocycle DD rho))]
      have hbc : iotaB (chiDef S hσ χ c)
          = iotaB (chiDef S hσ χ (0 : VCocycle DD rho)) := hall c
      rw [hbc, CharTwo.add_self_eq_zero]
    rw [hdecomp, hiotaB_shift _ _ hB] at hiota
    exact hiota
  -- ### Stage 3: the dual-connecting cochain `ξ`
  have hξadd : ∀ (y : DD.C0) (w w' : DD.Vmod),
      (χ.1 (conjDef DD S hσ y (y⁻¹ • (w + w'))) + gχ (w + w') + gχ (y⁻¹ • (w + w')))
      = (χ.1 (conjDef DD S hσ y (y⁻¹ • w)) + gχ w + gχ (y⁻¹ • w))
        + (χ.1 (conjDef DD S hσ y (y⁻¹ • w')) + gχ w' + gχ (y⁻¹ • w')) := by
    intro y w w'
    have hq : χ.1 (conjDef DD S hσ y (y⁻¹ • w + y⁻¹ • w'))
        + χ.1 (conjDef DD S hσ y (y⁻¹ • w)) + χ.1 (conjDef DD S hσ y (y⁻¹ • w'))
        = χ.1 (mDef DD S (y • (y⁻¹ • w)) (y • (y⁻¹ • w')))
          + χ.1 (mDef DD S (y⁻¹ • w) (y⁻¹ • w')) :=
      (isEquivariantFactorSet_datChi S hσ χ).m_quad y (y⁻¹ • w) (y⁻¹ • w')
    rw [smul_inv_smul, smul_inv_smul] at hq
    rw [show y⁻¹ • (w + w') = y⁻¹ • w + y⁻¹ • w' from smul_add _ _ _]
    have hchar : ∀ A B C F G P Q R T U V : ZMod 2,
        A + B + C = F + G → F = P + Q + R → G = T + U + V →
        A + P + T = (B + Q + U) + (C + R + V) := by decide
    exact hchar _ _ _ _ _ _ _ _ _ _ _ hq (hg w w') (hg (y⁻¹ • w) (y⁻¹ • w'))
  set Fξ : DD.C0 → ElemDual DD.Vmod := fun y =>
    AddMonoidHom.mk' (fun w => χ.1 (conjDef DD S hσ y (y⁻¹ • w)) + gχ w + gχ (y⁻¹ • w))
      (fun w w' => hξadd y w w') with hFdef
  have hFval : ∀ (y : DD.C0) (w : DD.Vmod),
      Fξ y w = χ.1 (conjDef DD S hσ y (y⁻¹ • w)) + gχ w + gχ (y⁻¹ • w) := fun _ _ => rfl
  set ξfun : Γ → ElemDual DD.Vmod := fun γ => Fξ (rho0 DD rho γ) with hξdef
  -- ### Stage 4: `ξ` is a continuous 1-cocycle for the contragredient action
  have hξZ1 : ξfun ∈ Z1 Γ (ElemDual DD.Vmod) := by
    haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
    refine mem_Z1_iff.mpr ⟨?_, ?_⟩
    · exact (continuous_of_discreteTopology
        (f := fun x : Bg ⧸ D.M => Fξ (liftC0 DD x))).comp rho.continuous_toFun
    · intro γ δ
      refine DFunLike.ext _ _ fun w => ?_
      rw [show ξfun (γ * δ) = Fξ (rho0 DD rho (γ * δ)) from rfl,
        show (ξfun γ + γ • ξfun δ) w = ξfun γ w + (γ • ξfun δ) w from rfl,
        ElemDual.smul_apply]
      have hγinv : γ⁻¹ • w = (rho0 DD rho γ)⁻¹ • w := by rw [hact, map_inv]
      rw [hγinv, show ξfun γ = Fξ (rho0 DD rho γ) from rfl,
        show ξfun δ = Fξ (rho0 DD rho δ) from rfl, hFval, hFval, hFval, map_mul, mul_inv_rev,
        mul_smul]
      have hmul : χ.1 (conjDef DD S hσ (rho0 DD rho γ * rho0 DD rho δ)
            ((rho0 DD rho δ)⁻¹ • ((rho0 DD rho γ)⁻¹ • w)))
          = χ.1 (conjDef DD S hσ (rho0 DD rho γ)
              (rho0 DD rho δ • ((rho0 DD rho δ)⁻¹ • ((rho0 DD rho γ)⁻¹ • w))))
            + χ.1 (conjDef DD S hσ (rho0 DD rho δ)
              ((rho0 DD rho δ)⁻¹ • ((rho0 DD rho γ)⁻¹ • w))) :=
        (isEquivariantFactorSet_datChi S hσ χ).m_mul (rho0 DD rho γ) (rho0 DD rho δ)
          ((rho0 DD rho δ)⁻¹ • ((rho0 DD rho γ)⁻¹ • w))
      rw [smul_inv_smul] at hmul
      rw [hmul]
      have hchar : ∀ X Y P Q R : ZMod 2, (X + Y) + P + R = (X + P + Q) + (Y + Q + R) := by
        decide
      exact hchar _ _ _ _ _
  -- ### Stage 5: the pair cochain against every `V`-cocycle is a coboundary
  have hvan : ∀ zc : ↥(Z1 Γ DD.Vmod),
      (fun p : Γ × Γ => (ξfun p.1) (p.1 • zc.1 p.2)) ∈ B2 Γ (ZMod 2) := by
    intro zc
    set c : VCocycle DD rho :=
      { c := fun γ => (zc.1 γ : DD.Vmod)
        cont := by
          have hc : Continuous (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
            continuous_of_discreteTopology
          exact hc.comp (mem_Z1_iff.mp zc.2).1
        crossed := fun γ δ => by
          have hz := (mem_Z1_iff.mp zc.2).2 γ δ
          rw [hact γ (zc.1 δ)] at hz
          exact hz } with hcdef
    have hident : (fun p : Γ × Γ => (ξfun p.1) (p.1 • zc.1 p.2))
        = cupChi DD S rho hσ gχ χ c := by
      funext p
      rw [show ξfun p.1 = Fξ (rho0 DD rho p.1) from rfl, hFval]
      show χ.1 (conjDef DD S hσ (rho0 DD rho p.1) ((rho0 DD rho p.1)⁻¹ • (p.1 • zc.1 p.2)))
          + gχ (p.1 • zc.1 p.2) + gχ ((rho0 DD rho p.1)⁻¹ • (p.1 • zc.1 p.2))
        = χ.1 (conjDef DD S hσ (rho0 DD rho p.1) (c.c p.2))
          + gχ (rho0 DD rho p.1 • c.c p.2) + gχ (c.c p.2)
      rw [hact p.1, inv_smul_smul]
    rw [hident]
    exact iotaB_eq_zero_iff.mp (hcup c)
  -- ### Stage 6+7: the fork — right-slot separation and `B¹`-extraction, fused
  obtain ⟨n, hn'⟩ := hrsep ⟨ξfun, hξZ1⟩ hvan
  have hn : dZero Γ (ElemDual DD.Vmod) n = ξfun := hn'
  -- ### Stage 8: the invariant `M`-character `ψ` and its vanishing
  have hψ : ∀ t : ↥D.T, χ.1 t = 0 := by
    have hkey : ∀ (cc : DD.C0) (v : DD.Vmod),
        χ.1 (conjDef DD S hσ cc v) + gχ (cc • v) + gχ v = n v + n (cc • v) := by
      intro cc v
      obtain ⟨γ, hγ⟩ := hrhosurj cc
      have h2 : γ • n = ξfun γ + n := by
        rw [← congrFun hn γ]
        show γ • n = γ • n - n + n
        abel
      have h4 : (γ • n) (cc • v) = n v := by
        rw [ElemDual.smul_apply]
        congr 1
        rw [hact, map_inv, hγ, inv_smul_smul]
      have h5 : ξfun γ (cc • v)
          = χ.1 (conjDef DD S hσ cc v) + gχ (cc • v) + gχ v := by
        rw [show ξfun γ = Fξ (rho0 DD rho γ) from rfl, hFval, hγ, inv_smul_smul]
      have h3 : (γ • n) (cc • v) = ξfun γ (cc • v) + n (cc • v) := by rw [h2]; rfl
      rw [← h5, ← h4, h3]
      have hchar : ∀ X Y : ZMod 2, X = X + Y + Y := by decide
      exact hchar _ _
    have htmem := tPartN (DD := DD) S
    have hvco_mul := vcoMulN (DD := DD)
    set ψ : ↥D.M → ZMod 2 := fun m =>
      χ.1 ⟨_, htmem m⟩ + gχ (Multiplicative.toAdd (DD.descend m))
        + n (Multiplicative.toAdd (DD.descend m)) with hψdef
    -- **`T`-part product law** (`M` abelian)
    have ht : ∀ m m' : ↥D.M, (⟨_, htmem (m * m')⟩ : ↥D.T)
        = ⟨_, htmem m⟩ * ⟨_, htmem m'⟩
          * mDef DD S (Multiplicative.toAdd (DD.descend m))
              (Multiplicative.toAdd (DD.descend m')) := by
      intro m m'
      apply Subtype.ext
      show (↑m * ↑m' : Bg) * (↑(S.mV (Multiplicative.toAdd (DD.descend (m * m')))))⁻¹
        = ↑m * (↑(S.mV (Multiplicative.toAdd (DD.descend m))))⁻¹
          * (↑m' * (↑(S.mV (Multiplicative.toAdd (DD.descend m'))))⁻¹)
          * (↑(S.mV (Multiplicative.toAdd (DD.descend m)))
            * ↑(S.mV (Multiplicative.toAdd (DD.descend m')))
            * (↑(S.mV (Multiplicative.toAdd (DD.descend m)
                + Multiplicative.toAdd (DD.descend m'))))⁻¹)
      rw [hvco_mul]
      set a : Bg := (↑m : Bg) with ha
      set b : Bg := (↑m' : Bg) with hb
      set p : Bg := (↑(S.mV (Multiplicative.toAdd (DD.descend m))) : Bg) with hp
      set q : Bg := (↑(S.mV (Multiplicative.toAdd (DD.descend m'))) : Bg) with hq
      set r : Bg := (↑(S.mV (Multiplicative.toAdd (DD.descend m)
          + Multiplicative.toAdd (DD.descend m'))) : Bg) with hr
      have hpM : p ∈ D.M := (S.mV _).2
      have hqM : q ∈ D.M := (S.mV _).2
      have hbM : b ∈ D.M := m'.2
      have c1 : p⁻¹ * b = b * p⁻¹ := D.hcomm _ (inv_mem hpM) _ hbM
      have c2 : q⁻¹ * p = p * q⁻¹ := D.hcomm _ (inv_mem hqM) _ hpM
      symm
      calc a * p⁻¹ * (b * q⁻¹) * (p * q * r⁻¹)
          = a * (p⁻¹ * b) * q⁻¹ * p * q * r⁻¹ := by group
        _ = a * (b * p⁻¹) * q⁻¹ * p * q * r⁻¹ := by rw [c1]
        _ = a * b * (p⁻¹ * (q⁻¹ * p)) * q * r⁻¹ := by group
        _ = a * b * (p⁻¹ * (p * q⁻¹)) * q * r⁻¹ := by rw [c2]
        _ = a * b * r⁻¹ := by group
    -- `ψ` is additive
    have hadd : ∀ m m' : ↥D.M, ψ (m * m') = ψ m + ψ m' := by
      intro m m'
      have hmD : χ.1 (mDef DD S (Multiplicative.toAdd (DD.descend m))
            (Multiplicative.toAdd (DD.descend m')))
          = gχ (Multiplicative.toAdd (DD.descend m) + Multiplicative.toAdd (DD.descend m'))
            + gχ (Multiplicative.toAdd (DD.descend m))
            + gχ (Multiplicative.toAdd (DD.descend m')) := hg _ _
      have hnv : n (Multiplicative.toAdd (DD.descend (m * m')))
          = n (Multiplicative.toAdd (DD.descend m))
            + n (Multiplicative.toAdd (DD.descend m')) :=
        (congrArg n (hvco_mul m m')).trans (n.map_add _ _)
      have hgv : gχ (Multiplicative.toAdd (DD.descend (m * m')))
          = gχ (Multiplicative.toAdd (DD.descend m)
              + Multiplicative.toAdd (DD.descend m')) :=
        congrArg gχ (hvco_mul m m')
      show χ.1 ⟨_, htmem (m * m')⟩ + gχ (Multiplicative.toAdd (DD.descend (m * m')))
          + n (Multiplicative.toAdd (DD.descend (m * m'))) = _
      rw [ht, TCharC.map_mul, TCharC.map_mul, hmD, hnv, hgv]
      have hchar : ∀ A B P Q R T FF : ZMod 2,
          A + B + (FF + P + Q) + FF + (R + T) = (A + P + R) + (B + Q + T) := by decide
      exact hchar _ _ _ _ _ _ _
    -- `ψ` is `Y`-conjugation-invariant
    have hconj : ∀ (bb : Bg) (m : ↥D.M) (hm : bb * (m : Bg) * bb⁻¹ ∈ D.M),
        ψ ⟨bb * (m : Bg) * bb⁻¹, hm⟩ = ψ m := by
      intro bb m hm
      set cc : DD.C0 := DD.piC0 bb with hcc
      set v : DD.Vmod := Multiplicative.toAdd (DD.descend m) with hvdef
      have hvc : Multiplicative.toAdd (DD.descend ⟨bb * (m : Bg) * bb⁻¹, hm⟩) = cc • v := by
        rw [DD.hdesc_conj bb m hm]; rfl
      have hpiC0uσ : DD.piC0 (S.uσ cc) = cc := by
        have h1 := piQbar_mk DD (S.uσ cc)
        rw [S.piT_uσ] at h1
        rw [← h1, hσ]
      have hkM : (S.uσ cc)⁻¹ * bb ∈ D.M := by
        rw [← DD.hkerC0, MonoidHom.mem_ker, map_mul, map_inv, hpiC0uσ, hcc, inv_mul_cancel]
      have hbbdecomp : bb = S.uσ cc * ((S.uσ cc)⁻¹ * bb) := by group
      have hsecconj : bb * (↑(S.mV v) : Bg) * bb⁻¹
          = S.uσ cc * (↑(S.mV v) : Bg) * (S.uσ cc)⁻¹ := by
        conv_lhs => rw [hbbdecomp]
        set k : Bg := (S.uσ cc)⁻¹ * bb with hkdef
        have hcomm_k : k * (↑(S.mV v) : Bg) = (↑(S.mV v) : Bg) * k :=
          D.hcomm _ hkM _ (S.mV v).2
        calc S.uσ cc * k * (↑(S.mV v) : Bg) * (S.uσ cc * k)⁻¹
            = S.uσ cc * (k * (↑(S.mV v) : Bg)) * k⁻¹ * (S.uσ cc)⁻¹ := by group
          _ = S.uσ cc * ((↑(S.mV v) : Bg) * k) * k⁻¹ * (S.uσ cc)⁻¹ := by rw [hcomm_k]
          _ = _ := by group
      have htsplit : (⟨_, htmem ⟨bb * (m : Bg) * bb⁻¹, hm⟩⟩ : ↥D.T)
          = ⟨bb * (⟨_, htmem m⟩ : ↥D.T).1 * bb⁻¹,
              D.hT.conj_mem _ (⟨_, htmem m⟩ : ↥D.T).2 _⟩ * conjDef DD S hσ cc v := by
        apply Subtype.ext
        show (bb * (m : Bg) * bb⁻¹)
            * (↑(S.mV (Multiplicative.toAdd (DD.descend ⟨bb * (m : Bg) * bb⁻¹, hm⟩))))⁻¹
          = bb * ((m : Bg) * (↑(S.mV v))⁻¹) * bb⁻¹
            * (S.uσ cc * (↑(S.mV v) : Bg) * (S.uσ cc)⁻¹ * (↑(S.mV (cc • v)))⁻¹)
        rw [hvc]
        rw [← hsecconj]
        group
      have hlhs : ψ ⟨bb * (m : Bg) * bb⁻¹, hm⟩
          = χ.1 (⟨_, htmem m⟩ : ↥D.T) + χ.1 (conjDef DD S hσ cc v) + gχ (cc • v)
            + n (cc • v) := by
        rw [hψdef]
        show χ.1 ⟨_, htmem ⟨bb * (m : Bg) * bb⁻¹, hm⟩⟩
            + gχ (Multiplicative.toAdd (DD.descend ⟨bb * (m : Bg) * bb⁻¹, hm⟩))
            + n (Multiplicative.toAdd (DD.descend ⟨bb * (m : Bg) * bb⁻¹, hm⟩))
          = χ.1 (⟨_, htmem m⟩ : ↥D.T) + χ.1 (conjDef DD S hσ cc v) + gχ (cc • v) + n (cc • v)
        rw [htsplit, TCharC.map_mul, TCharC.conj_invariant χ bb (⟨_, htmem m⟩ : ↥D.T),
          congrArg gχ hvc]
        congr 1
        exact congrArg n hvc
      have hrhs : ψ m = χ.1 (⟨_, htmem m⟩ : ↥D.T) + gχ v + n v := rfl
      rw [hlhs, hrhs]
      have hk := hkey cc v
      have hfin : ∀ (TP CJ GCV NCV GV NV : ZMod 2),
          CJ + GCV + GV = NV + NCV → TP + CJ + GCV + NCV = TP + GV + NV := by decide
      exact hfin _ _ _ _ _ _ hk
    -- conclude: `ψ` vanishes on `M`, so `χ` vanishes on `T`
    intro t₀
    have h0 := hMchar ψ hadd hconj ⟨t₀.1, D.hTM t₀.2⟩
    have hdesc1 : DD.descend ⟨t₀.1, D.hTM t₀.2⟩ = 1 := (DD.hdesc_ker _).mpr t₀.2
    have harg : (⟨_, htmem ⟨t₀.1, D.hTM t₀.2⟩⟩ : ↥D.T) = t₀ := by
      apply Subtype.ext
      show ((t₀ : Bg))
          * (↑(S.mV (Multiplicative.toAdd (DD.descend ⟨t₀.1, D.hTM t₀.2⟩))))⁻¹ = (t₀ : Bg)
      rw [hdesc1, show Multiplicative.toAdd (1 : Multiplicative DD.Vmod)
          = (0 : DD.Vmod) from toAdd_one, S.mV_zero]
      simp
    have hval : ψ ⟨t₀.1, D.hTM t₀.2⟩ = χ.1 t₀ := by
      show χ.1 ⟨_, htmem ⟨t₀.1, D.hTM t₀.2⟩⟩
          + gχ (Multiplicative.toAdd (DD.descend ⟨t₀.1, D.hTM t₀.2⟩))
          + n (Multiplicative.toAdd (DD.descend ⟨t₀.1, D.hTM t₀.2⟩)) = χ.1 t₀
      have hg0' : gχ (Multiplicative.toAdd (DD.descend ⟨t₀.1, D.hTM t₀.2⟩)) = 0 := by
        rw [hdesc1, toAdd_one]; exact hg0
      have hn0' : n (Multiplicative.toAdd (DD.descend ⟨t₀.1, D.hTM t₀.2⟩)) = 0 := by
        conv_lhs => rw [hdesc1]
        exact map_zero n
      rw [harg, hg0', hn0', add_zero, add_zero]
    exact hval.symm.trans h0
  -- ### Stage 9: contradiction with `hχ`
  apply hχ
  apply Subtype.ext
  funext t
  exact hψ t

end HPartial

/-! ## §4. The verbatim `SourceDataN.hpartial` field goal

The record's field (`GQ2/Dyadic/SourceDataN.lean:243`) is the statement below `∀`-generalized
over `H`, `E`, `Y`, `T`, `Blk`, `RF`, `b`, `F`, `En`, `l`, `h`, `Dsc`, `ρ`.  Fixing those and
writing the goal in the recursion's own vocabulary (`BoundaryLiftsK`, `rhoPrimeK`,
`descSections`, `descSigma_spec`) is the consumer check CB-1 and CB-H2 both perform; here it
closes off `hpartialN` with **no transport at all**, because `hpartialN` is stated at exactly
the `(D, DD, S, hσ, ρ)` the field instantiates.

The three `letI`s are the recursion's standing discrete-module conventions, not new data:
`En.Vmod` and its dual carry `⊥`, and the `Γ`-action is the pullback of the `C₀`-action along
`rho0` — which `rho0_descData_rhoPrimeK` identifies with `ρ.1.1`, so `hact` is `rfl` and
`hrhosurj` is `ρ.1.2`. -/
section FieldGoal

open GQ2.Dyadic

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
  {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
  {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **`SourceDataN.hpartial`, verbatim at one frame** (`GQ2/Dyadic/SourceDataN.lean:243`),
including the record's own `letI := smulZmod2`.  Closed, with three binders: `htriv` and `hH2`
are two *other* fields of the very same record (`SourceDataN.htriv`, `SourceDataN.cardH2`), so
the only genuinely new input a source must produce for this clause is `hrsep`. -/
theorem hpartial_field_goal
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (smulZmod2 : DistribMulAction Γ (ZMod 2))
    (htriv : letI := smulZmod2; ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : letI := smulZmod2; Nat.card (H2 Γ (ZMod 2)) = 2)
    (hrsep :
      letI := smulZmod2
      letI : TopologicalSpace (En.descData l h).Vmod := ⊥
      haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
      letI : DistribMulAction Γ (En.descData l h).Vmod :=
        DistribMulAction.compHom (En.descData l h).Vmod
          (rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
      letI : TopologicalSpace (ElemDual (En.descData l h).Vmod) := ⊥
      haveI : DiscreteTopology (ElemDual (En.descData l h).Vmod) := ⟨rfl⟩
      IsRightSeparating Γ (En.descData l h).Vmod)
    (χ : ↥(TCharC (En.radData l h))) (hχ : χ ≠ 0) :
    letI := smulZmod2
    ∃ c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ),
      betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c
        ≠ betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ
            (0 : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ)) := by
  letI := smulZmod2
  letI : TopologicalSpace (En.descData l h).Vmod := ⊥
  haveI : DiscreteTopology (En.descData l h).Vmod := ⟨rfl⟩
  letI : DistribMulAction Γ (En.descData l h).Vmod :=
    DistribMulAction.compHom (En.descData l h).Vmod
      (rho0 (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
  letI : TopologicalSpace (ElemDual (En.descData l h).Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual (En.descData l h).Vmod) := ⟨rfl⟩
  refine hpartialN (descSections En l h Dsc) (descSigma_spec En l h Dsc)
    (fun _ _ => rfl) (fun cc => ?_) htriv hH2 hrsep
    (fun ψ hadd hconj => mchar_conj_invariant_eq_zero RF En l h ψ hadd hconj) χ hχ
  obtain ⟨γ, hγ⟩ := ρ.1.2 cc
  exact ⟨γ, (rho0_descData_rhoPrimeK b F En l h ρ γ).trans hγ⟩

end FieldGoal

/-! ## §5. The `hsep` fork, and its arithmetic supplier -/

section TwoSeparatingDef

variable (Γ : Type) [Group Γ] [TopologicalSpace Γ] [DistribMulAction Γ (ZMod 2)]
  (A : Type) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]
  [DistribMulAction Γ A]

/-- **Degree-`2` separation for `(Γ, A)`** — the one input on which the two `ℚ₂` proofs of
`hsep` diverge, isolated and stated *cup-free*: a continuous `2`-cocycle `φ` all of whose
invariant-dual pushforwards `p ↦ n(φ p)` are `𝔽₂`-coboundaries is itself a coboundary.

Equivalently: the pairing `H²(Γ, A) × H⁰(Γ, A^∨) → 𝔽₂` is nondegenerate in the **left** slot.
The arithmetic side reads it off Tate's `(2,0)` clause (`isTwoSeparating_of_tateDualityG`); the
candidate side reads the same proposition off the word-side `#H²w(A) = #H⁰w(A^∨)` — which is
`IsSelfDualN`'s clause 1, the *only* clause `ℚ₂`'s `sep_word` consumes.  As with
`IsRightSeparating`, neither vocabulary appears here, so one binder serves both sides and all
five frozen branch families at once. -/
def IsTwoSeparating : Prop :=
  ∀ φ : ↥(Z2 Γ A),
    (∀ n : ElemDual A, (∀ γ : Γ, γ • n = n) →
      (fun p : Γ × Γ => n (φ.1 p)) ∈ B2 Γ (ZMod 2)) →
    (φ.1 : Γ × Γ → A) ∈ B2 Γ A

end TwoSeparatingDef

section TwoSeparation

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [ContinuousSMul Γ (ElemDual A)]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [TopologicalSpace A] [DiscreteTopology A] [Finite A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [ContinuousSMul Γ (ElemDual A)] in
/-- An invariant elementary dual is `Γ`-equivariant for the trivial target action. -/
theorem elemDual_apply_smul {n : ElemDual A} (hn : ∀ γ : Γ, γ • n = n) (g : Γ) (a : A) :
    n (g • a) = n a := by
  conv_lhs => rw [← hn g]
  rw [ElemDual.smul_apply, inv_smul_smul]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
  [ContinuousSMul Γ (ZMod 2)] [Finite A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [ContinuousSMul Γ (ElemDual A)] in
/-- The pushforward of a continuous `2`-cocycle along an invariant elementary dual is a
continuous `𝔽₂`-valued `2`-cocycle. -/
theorem pushforward_mem_Z2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (φ : ↥(Z2 Γ A))
    {n : ElemDual A} (hn : ∀ γ : Γ, γ • n = n) :
    (fun p : Γ × Γ => n (φ.1 p)) ∈ Z2 Γ (ZMod 2) := by
  refine mem_Z2_iff.mpr ⟨(continuous_of_discreteTopology (f := fun a : A => n a)).comp
    (mem_Z2_iff.mp φ.2).1, fun g h k => ?_⟩
  have hφ := congrArg n ((mem_Z2_iff.mp φ.2).2 g h k)
  rw [map_add, map_add, elemDual_apply_smul hn g (φ.1 (h, k))] at hφ
  rw [htriv]
  exact hφ

omit [ContinuousSMul Γ (ZMod 2)] in
/-- Tate's `(0,2)` perfectness already makes `H²(Γ,A)` finite for every finite elementary
coefficient module `A`.  Indeed, perfectness identifies its elementary dual with the finite
group `H⁰(Γ, μ₂-dual A)`, and elementary functionals separate points of `H²(Γ,A)`.

This is the missing Euler-free finiteness input for the `(2,0)` separation clause. -/
theorem finite_H2_of_tateDualityG (Dl : TateDualityG Γ 2)
    (hA₂ : ∀ a : A, a + a = 0) : Finite (H2 Γ A) := by
  let htor : ∀ a : A, (2 : ℕ) • a = 0 := fun a => by
    rw [two_nsmul]
    exact hA₂ a
  let f : H0 Γ (MuDual 2 A) → (H2 Γ A →+ ZMod 2) := fun c =>
    Dl.inv.toAddMonoidHom.comp
      (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) c)
  letI hfinDual : Finite (ElemDual (H2 Γ A)) := by
    change Finite (H2 Γ A →+ ZMod 2)
    exact Finite.of_surjective f (Dl.perfect02 A htor).2
  letI : Finite (ElemDual (H2 Γ A) →+ ZMod 2) :=
    Finite.of_injective
      (fun lam : ElemDual (H2 Γ A) →+ ZMod 2 =>
        (lam : ElemDual (H2 Γ A) → ZMod 2)) DFunLike.coe_injective
  apply Finite.of_injective (dualEval (H2 Γ A))
  intro x y hxy
  have heq : ∀ lam : ElemDual (H2 Γ A), lam x = lam y := fun lam => by
    simpa using DFunLike.congr_fun hxy lam
  by_contra hne
  obtain ⟨lam, hlam⟩ := elemDual_separates (H2_two_torsionG hA₂)
    (sub_ne_zero_of_ne hne)
  exact hlam (by rw [map_sub, heq lam, sub_self])

/-- **The arithmetic supplier of the `hsep` fork.**  Injectivity of the `(2,0)` evaluation cup
(`prop_5_16` clause (vi), `Γ`-generically CB-SG's `bijective_cup20_dualEvalG_of_finite`) is exactly
`IsTwoSeparating`: the cup value at an invariant `n` is the class of the pushforward `n ∘ φ`,
so universal `B²`-membership is universal cup-vanishing.

Unlike the numeric clauses, this uses no Euler characteristic: `finite_H2_of_tateDualityG`
extracts the sole finiteness input directly from Tate `(0,2)` perfectness. -/
theorem isTwoSeparating_of_tateDualityG (Dl : TateDualityG Γ 2)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    IsTwoSeparating Γ A := by
  intro φ hvan
  have hzero : H2mk Γ A φ = 0 := by
    letI : Finite (H2 Γ A) := finite_H2_of_tateDualityG Dl hA₂
    apply (bijective_cup20_dualEvalG_of_finite Dl hA₂ htriv hpair).1
    show cup20 (dualEval A) hpair _ = cup20 (dualEval A) hpair 0
    rw [map_zero]
    refine AddMonoidHom.ext fun n => ?_
    show cup20 (dualEval A) hpair (H2mk Γ A φ) n = 0
    have hnn : ∀ γ : Γ, γ • n.1 = n.1 := fun γ => n.2 γ
    have hval : cup20 (dualEval A) hpair (H2mk Γ A φ) n
        = H2mk Γ (ZMod 2) ⟨fun p : Γ × Γ => n.1 (φ.1 p), pushforward_mem_Z2 htriv φ hnn⟩ := by
      apply congrArg (H2mk Γ (ZMod 2))
      apply Subtype.ext
      funext gd
      show dualEval A (φ.1 gd) ((gd.1 * gd.2) • n.1) = n.1 (φ.1 gd)
      rw [n.2 (gd.1 * gd.2)]
      rfl
    rw [hval, H2mk_eq_zero_iff]
    exact hvan n.1 hnn
  exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff φ).mp hzero)

end TwoSeparation

/-! ## §6. `SourceDataN.hsep`, over the abstract carrier -/

section HSep

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)]
  {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
  (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
  {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
  (hcompT : ∀ (γ : Γ) (a : Additive ↥D.T), γ • a = rho γ • a)

omit [DiscreteTopology Bg] [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
  [DistribMulAction Γ (Additive ↥D.T)] [ContinuousSMul Γ (Additive ↥D.T)] in
include hσ in
/-- **`mk_M (fLift γ) = ρ γ`**: the pointwise lift of a `V`-cocycle reduces mod `M` to the lower
map (`mV (c γ) ∈ M` kills its coset, `uσ` is a `piC0`-section, `liftC0` is injective).
Abstract-carrier form of `Phase140.Local`'s `private fLift_mk_M`. -/
theorem fLift_mk_MN (c : VCocycle DD rho) (γ : Γ) :
    (QuotientGroup.mk (fLift S c γ) : Bg ⧸ D.M) = rho γ := by
  have hinj : Function.Injective (liftC0 DD) := by
    intro x y hxy
    induction x using QuotientGroup.induction_on with
    | H bx =>
      induction y using QuotientGroup.induction_on with
      | H by' =>
        rw [liftC0_mk, liftC0_mk] at hxy
        apply (QuotientGroup.eq (s := D.M)).mpr
        rw [← DD.hkerC0, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  apply hinj
  rw [liftC0_mk]
  show DD.piC0 ((S.mV (c.c γ) : Bg) * S.uσ (rho0 DD rho γ)) = rho0 DD rho γ
  rw [map_mul,
    MonoidHom.mem_ker.mp (show ((S.mV (c.c γ) : Bg)) ∈ DD.piC0.ker by
      rw [DD.hkerC0]; exact (S.mV (c.c γ)).2),
    one_mul, ← piQbar_mk DD, S.piT_uσ, hσ]

omit [ContinuousSMul Γ (ZMod 2)] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (Additive ↥D.T)] in
include hσ hcompT in
/-- **The `T`-valued defect is a `Z²`-cocycle**: pushing `tDef` into `Additive ↥D.T` gives a
continuous inhomogeneous `2`-cocycle for the conjugation action (`M` abelian collapses the
sign).  Abstract-carrier form of `Phase140.Local`'s `private tDef_mem_Z2`; the action is the
campaign's canonical `cActT`, reconciled with an arbitrary representative by CB-1's
`smul_eq_conj`. -/
theorem tDef_mem_Z2N (c : VCocycle DD rho) :
    (fun p : Γ × Γ => Additive.ofMul (tDef S hσ c p)) ∈ Z2 Γ (Additive ↥D.T) := by
  have hfLmk := fLift_mk_MN S hσ c
  refine mem_Z2_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_of_discreteTopology (f := Additive.ofMul)).comp
      (tDef_continuous S hσ c)
  · intro γ δ ε
    rw [smul_eq_conj rho hcompT γ (fLift S c γ) (Additive.ofMul (tDef S hσ c (δ, ε)))
        (hfLmk γ)]
    apply Additive.toMul.injective
    apply Subtype.ext
    show fLift S c γ * (tDef S hσ c (δ, ε) : Bg) * (fLift S c γ)⁻¹
          * (tDef S hσ c (γ, δ * ε) : Bg)
        = (tDef S hσ c (γ * δ, ε) : Bg) * (tDef S hσ c (γ, δ) : Bg)
    have hraw : (tDef S hσ c (γ, δ) : Bg) * (tDef S hσ c (γ * δ, ε) : Bg)
        = fLift S c γ * (tDef S hσ c (δ, ε) : Bg) * (fLift S c γ)⁻¹
            * (tDef S hσ c (γ, δ * ε) : Bg) := by
      show fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹
            * (fLift S c (γ * δ) * fLift S c ε * (fLift S c (γ * δ * ε))⁻¹)
          = fLift S c γ * (fLift S c δ * fLift S c ε * (fLift S c (δ * ε))⁻¹)
              * (fLift S c γ)⁻¹ * (fLift S c γ * fLift S c (δ * ε) * (fLift S c (γ * (δ * ε)))⁻¹)
      rw [show γ * δ * ε = γ * (δ * ε) from mul_assoc γ δ ε]
      group
    rw [← hraw]
    exact D.hcomm _ (D.hTM (tDef S hσ c (γ, δ)).2) _ (D.hTM (tDef S hσ c (γ * δ, ε)).2)

omit [ContinuousSMul Γ (ZMod 2)] [ContinuousSMul Γ (Additive ↥D.T)] in
include hσ hcompT in
/-- **`SourceDataN.hsep` over the abstract carrier** — the `(T^∨)^C`-separation: a `V`-cocycle
whose `χ`-obstructions all vanish is `T`-liftable.

`Phase140.Local.hsep_local`'s seven stages with `AbsGalQ2` replaced by a variable `Γ`, the
frame data replaced by `(D, DD, S, hσ, rho)`, and the **one** divergent input promoted to the
binder `h2sep`.  Note what is *not* here: no `#H²(Γ,𝔽₂) = 2`, no `htriv`, no `hpair`, no
simplicity — the cup-free spelling of the fork removes the entire `cup20`/`H2mk` layer from
the body, so stage 4 becomes the observation that the invariant-dual pushforward of `tDef`
**is** `chiDef` at the induced character, definitionally.

Stage 7 (the direct `M`-lift `f γ = ψγ · fLift γ`) is the genuinely bespoke part at `ℚ₂` and
stays bespoke here; everything it uses (`T` abelian, `T` of exponent `2`, the split relation)
is `RadicalCoverData`-level. -/
theorem hsepN (hrhosurj : Function.Surjective rho)
    (h2sep : IsTwoSeparating Γ (Additive ↥D.T))
    (c : VCocycle DD rho)
    (hc : ∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) :
    TLiftable hσ c := by
  classical
  have hfLmk := fLift_mk_MN S hσ c
  have tDefZ2 := tDef_mem_Z2N S hσ hcompT c
  -- STAGE 4: every invariant-dual pushforward of `tDef` is a coboundary
  have hcup : ∀ n : ElemDual (Additive ↥D.T), (∀ γ : Γ, γ • n = n) →
      (fun p : Γ × Γ => n (Additive.ofMul (tDef S hσ c p))) ∈ B2 Γ (ZMod 2) := by
    intro n hn
    have hconjinv : ∀ (bb : Bg) (t : ↥D.T),
        n (Additive.ofMul (⟨bb * (t : Bg) * bb⁻¹, D.hT.conj_mem t.1 t.2 bb⟩ : ↥D.T))
          = n (Additive.ofMul t) := by
      intro bb t
      obtain ⟨γ, hγ⟩ := hrhosurj (QuotientGroup.mk bb)
      have hmk : (QuotientGroup.mk bb⁻¹ : Bg ⧸ D.M) = rho γ⁻¹ := by
        rw [QuotientGroup.mk_inv, map_inv, hγ]
      have h3 : γ⁻¹ • Additive.ofMul (⟨bb * (t : Bg) * bb⁻¹,
            D.hT.conj_mem t.1 t.2 bb⟩ : ↥D.T) = Additive.ofMul t := by
        rw [smul_eq_conj rho hcompT γ⁻¹ bb⁻¹ _ hmk]
        apply Additive.toMul.injective
        apply Subtype.ext
        show bb⁻¹ * (bb * (t : Bg) * bb⁻¹) * bb⁻¹⁻¹ = (t : Bg)
        group
      conv_lhs => rw [← hn γ]
      rw [ElemDual.smul_apply, h3]
    let χn : ↥(TCharC D) :=
      ⟨fun t => n (Additive.ofMul t),
        ⟨fun t t' => by
          show n (Additive.ofMul (t * t')) = n (Additive.ofMul t) + n (Additive.ofMul t')
          exact map_add n (Additive.ofMul t) (Additive.ofMul t'), hconjinv⟩⟩
    show (fun p : Γ × Γ => χn.1 (tDef S hσ c p)) ∈ B2 Γ (ZMod 2)
    exact iotaB_eq_zero_iff.mp (hc χn)
  -- STAGE 5+6: the defect class vanishes, and `B²`-extraction produces `ψ`
  obtain ⟨ψ, hψC1, hψeq⟩ := h2sep ⟨_, tDefZ2⟩ hcup
  -- STAGE 7: `f γ := ψγ · fLift γ` is a genuine `M`-lift with `redTLift f = qOfCocycle c`
  have hψT : ∀ γ : Γ, ((Additive.toMul (ψ γ) : ↥D.T) : Bg) ∈ D.T :=
    fun γ => (Additive.toMul (ψ γ)).2
  have hsplitT : ∀ γ δ : Γ,
      ((Additive.toMul (γ • ψ δ) : ↥D.T) : Bg)
        * ((Additive.toMul (ψ (γ * δ)) : ↥D.T) : Bg)⁻¹
        * ((Additive.toMul (ψ γ) : ↥D.T) : Bg) = (tDef S hσ c (γ, δ) : Bg) := by
    intro γ δ
    have hdo := congrFun hψeq (γ, δ)
    have h := congrArg (fun a : Additive ↥D.T => ((Additive.toMul a : ↥D.T) : Bg)) hdo
    simpa only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, toMul_add, toMul_sub, toMul_ofMul,
      Subgroup.coe_mul, Subgroup.coe_div, div_eq_mul_inv, Subgroup.coe_inv, mul_assoc] using h
  have hconjT : ∀ γ δ : Γ,
      ((Additive.toMul (γ • ψ δ) : ↥D.T) : Bg)
        = fLift S c γ * ((Additive.toMul (ψ δ) : ↥D.T) : Bg) * (fLift S c γ)⁻¹ := by
    intro γ δ
    rw [smul_eq_conj rho hcompT γ (fLift S c γ) (ψ δ) (hfLmk γ)]
    rfl
  have hsplit : ∀ γ δ : Γ,
      fLift S c γ * ((Additive.toMul (ψ δ) : ↥D.T) : Bg) * (fLift S c γ)⁻¹
        = (tDef S hσ c (γ, δ) : Bg) * ((Additive.toMul (ψ γ) : ↥D.T) : Bg)⁻¹
            * ((Additive.toMul (ψ (γ * δ)) : ↥D.T) : Bg) := by
    intro γ δ
    have hs := hsplitT γ δ
    rw [hconjT γ δ] at hs
    rw [← hs]; group
  have hcomm2 : ∀ x y : Bg, x ∈ D.T → y ∈ D.T → x * y = y * x :=
    fun x y hx hy => D.hcomm x (D.hTM hx) y (D.hTM hy)
  have hsq : ∀ x : Bg, x ∈ D.T → x * x = 1 := fun x hx => D.helem x (D.hTM hx)
  refine ⟨⟨⟨MonoidHom.mk'
      (fun γ => ((Additive.toMul (ψ γ) : ↥D.T) : Bg) * fLift S c γ) ?_, ?_⟩, ?_⟩, ?_⟩
  · intro γ δ
    have htd : fLift S c γ * fLift S c δ = (tDef S hσ c (γ, δ) : Bg) * fLift S c (γ * δ) := by
      show _ = (fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹) * fLift S c (γ * δ)
      group
    set pγ := ((Additive.toMul (ψ γ) : ↥D.T) : Bg) with hpγ
    set pδ := ((Additive.toMul (ψ δ) : ↥D.T) : Bg) with hpδ
    set pe := ((Additive.toMul (ψ (γ * δ)) : ↥D.T) : Bg) with hpe
    set td := (tDef S hσ c (γ, δ) : Bg) with htdd
    have htdT : td ∈ D.T := (tDef S hσ c (γ, δ)).2
    have hTarith : pγ * td * pγ⁻¹ * pe * td = pe := by
      rw [hcomm2 pγ td (hψT γ) htdT, mul_inv_cancel_right,
        hcomm2 td pe htdT (hψT (γ * δ)), mul_assoc, hsq td htdT, mul_one]
    symm
    calc (pγ * fLift S c γ) * (pδ * fLift S c δ)
        = pγ * (fLift S c γ * pδ * (fLift S c γ)⁻¹) * (fLift S c γ * fLift S c δ) := by group
      _ = pγ * (td * pγ⁻¹ * pe) * (td * fLift S c (γ * δ)) := by rw [hsplit γ δ, htd]
      _ = (pγ * td * pγ⁻¹ * pe * td) * fLift S c (γ * δ) := by group
      _ = pe * fLift S c (γ * δ) := by rw [hTarith]
  · exact (continuous_subtype_val.comp (continuous_of_discreteTopology.comp hψC1)).mul
      (fLift_continuous S c)
  · intro γ
    show (QuotientGroup.mk (((Additive.toMul (ψ γ) : ↥D.T) : Bg) * fLift S c γ) : Bg ⧸ D.M)
      = rho γ
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (D.hTM (hψT γ)), one_mul,
      hfLmk γ]
  · apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro γ
    show (QuotientGroup.mk (((Additive.toMul (ψ γ) : ↥D.T) : Bg) * fLift S c γ) : Bg ⧸ D.T)
      = (qOfCocycle DD rho σ hσ c).1 γ
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr (hψT γ), one_mul,
      show (QuotientGroup.mk (fLift S c γ) : Bg ⧸ D.T) = piT (D := D) (fLift S c γ) from rfl,
      fLift_mk S hσ c γ]

end HSep

/-! ## §7. The verbatim `SourceDataN.hsep` field goal

Same shape as §4: the record's field (`GQ2/Dyadic/SourceDataN.lean:229`) is the statement below
`∀`-generalized over the frame data, and fixing that data lets `hsepN` close it with no
transport.  The three `letI`s are the recursion's standing conventions for the `T`-layer module
(`⊥`-topology on `Additive ↥T`, and the `Γ`-action pulled back from the campaign's canonical
`cActT` along `rhoPrimeK`), so `hcompT` is `rfl`; `hrhosurj` is SD-R3's `rhoPrimeK_surjective`;
and the record's own `smulZmod2` supplies the `𝔽₂`-action.  **`h2sep` is the only new input.** -/
section HSepFieldGoal

open GQ2.Dyadic

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
  {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
  {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

/-- **`SourceDataN.hsep`, verbatim at one frame** (`GQ2/Dyadic/SourceDataN.lean:229`), including
the record's own `letI := smulZmod2`.  Closed, with one binder beyond the record's own data. -/
theorem hsep_field_goal
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (En : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR)
    (Dsc : Descent (En.radData l h)) (ρ : BoundaryLiftsK b F RF.TC)
    (smulZmod2 : DistribMulAction Γ (ZMod 2))
    (h2sep :
      letI := smulZmod2
      letI : TopologicalSpace (Additive ↥(En.radData l h).T) := ⊥
      haveI : DiscreteTopology (Additive ↥(En.radData l h).T) := ⟨rfl⟩
      letI : DistribMulAction Γ (Additive ↥(En.radData l h).T) :=
        DistribMulAction.compHom (Additive ↥(En.radData l h).T)
          (rhoPrimeK RF b F (En.radData l h) rfl ρ).toMonoidHom
      IsTwoSeparating Γ (Additive ↥(En.radData l h).T))
    (c : VCocycle (En.descData l h) (rhoPrimeK RF b F (En.radData l h) rfl ρ))
    (hc : letI := smulZmod2
      ∀ χ : ↥(TCharC (En.radData l h)),
        betaChi (descSections En l h Dsc) (descSigma_spec En l h Dsc) χ c = 0) :
    letI := smulZmod2
    TLiftable (descSigma_spec En l h Dsc) c := by
  letI := smulZmod2
  letI : TopologicalSpace (Additive ↥(En.radData l h).T) := ⊥
  haveI : DiscreteTopology (Additive ↥(En.radData l h).T) := ⟨rfl⟩
  letI : DistribMulAction Γ (Additive ↥(En.radData l h).T) :=
    DistribMulAction.compHom (Additive ↥(En.radData l h).T)
      (rhoPrimeK RF b F (En.radData l h) rfl ρ).toMonoidHom
  exact hsepN (descSections En l h Dsc) (descSigma_spec En l h Dsc) (fun _ _ => rfl)
    (rhoPrimeK_surjective RF b F (En.radData l h) rfl ρ) h2sep c hc

end HSepFieldGoal


end GQ2.Dyadic.Count
