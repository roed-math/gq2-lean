/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import GQ2.ProfinitePresentation
public import GQ2.Subdirect
public import GQ2.MaxProP
public import GQ2.ZtwoPowering
public import GQ2.Roe.Words

@[expose] public section

/-!
# The Roe pro-2 presentation `D_R = ⟨s, x, y | (x^s)⁻¹x⁻³y²[y,y^s]⟩`  (Roe note §3.1)

The maximal pro-2 quotient of the Roe candidate `Γ_R` collapses to a three-generator
one-relator pro-2 group (Roe note, eq. (3.1) ⟦lem:pro2word⟧, verbatim):

```
\DR=
\angles{s,x,y\ \middle|\
r_2=(x^s)^{-1}x^{-3}y^2[y,y^s]=1}_{\mathrm{pro}\text{-}2},
```

with `s = σ`, `x = x₀`, `y = x₁` (`τ` dies in any pro-2 quotient and `ω₂`-powers are
identities there).  This file constructs `D_R` 1:1 on the pattern of `GQ2/DyadicPresentation.lean`
(the `D₀ = ⟨A,S,Y | A²S⁴[S,Y]⟩` file): the relator as a word in the free profinite group on
`Fin 3`, the full profinite presentation `DRFull`, the pro-2 group `DR = maxProPQuotient 2 DRFull`,
the marked generators `drS, drX, drY` at both levels, and the relation lemmas.

Conventions match the note exactly: `x ^ g = g⁻¹xg` (`GQ2.conjP`), `[x,y] = x⁻¹y⁻¹xy`
(`GQ2.commP`), and `x⁻³ = (x³)⁻¹`.

## The word shape `drWord`

The relator's *shape* is factored out as `drWord s x y = (x^s)⁻¹ · (x³)⁻¹ · y² · [y, y^s]`,
a computable word in any group.  This single definition is evaluated in three regimes:

* at the free profinite generators — the relator `drRelator` itself;
* in finite (2-)groups — the `decide`-checked stress tests below, and the Demushkin/`H²`
  computations of `GQ2/Roe/DRDemushkin.lean`;
* at `WordLift ℤ₂ ℤ₂ˣ`-lifts — the χ-twisted crossed-derivation calculus of
  `GQ2/Roe/CrossedDerivation.lean` (the note's Prop. 3.3 ⟦prop:orientation⟧), where
  `(drWord ⟨Ds,S⟩ ⟨Dx,X⟩ ⟨Dy,Y⟩).u` *is* `D(r₂)`.

Naturality (`map_drWord`) makes the relation lemmas and every downstream evaluation one-line
transports of each other.

## Universal property

`drLiftHom` (the `d0LiftHom` clone, `GQ2/SectionThree.lean:444`): a triple in a pro-2 group
killing `drWord` classifies a continuous hom out of `DR`.  This is the workhorse for the
`𝔽₂`-characters of `DRDemushkin.lean`, the unramified marking `ν_R` of `MarkedPro2.lean`, and
the canonical orientation `χ_R` (ticket R11).

## Stress tests

* `drWord_comm`: abelian collapse `drWord s x y = (x⁴)⁻¹y²` — the abelianized relation
  `−4x̄ + 2ȳ = 0` of the note's eq. (3.4) ⟦eq:BR⟧ (pins the exponents `−1 − 3 = −4` and `2`).
* `drWord_zmod8` / `drWord_zmod8_y1`: numeric pins in `Multiplicative (ZMod 8)` — the marking
  `(s,x,y) = (3,1,2)` (additive) kills the relator (`−4·1 + 2·2 = 0`) while `(3,1,1)` evaluates
  to `−2 ≡ 6`, pinning both exponents against sign slips.
* `drWord_d4`: the relator dies at the *generating, non-abelian* marking
  `(s,x,y) = (r 2, r 1, sr 0)` of `D₄ = DihedralGroup 4` — so `D₄` is a genuine finite quotient
  of `D_R` (cf. the R2 spike's `#Hom`-count corroboration on all 2-groups of order ≤ 128).
-/

open CategoryTheory

namespace GQ2

/-! ## The word shape -/

/-- The **Roe pro-2 relator word shape** `drWord s x y = (x^s)⁻¹ · (x³)⁻¹ · y² · [y, y^s]`
(note eq. (3.1) ⟦lem:pro2word⟧, verbatim `r_2=(x^s)^{-1}x^{-3}y^2[y,y^s]`), as a word in any
group, with the paper's conventions `x ^ g = g⁻¹xg` (`conjP`) and `[x,y] = x⁻¹y⁻¹xy` (`commP`).
Evaluated at the free profinite generators it is the relator `drRelator`; at `WordLift`-lifts it
computes the χ-twisted Fox row (`GQ2/Roe/CrossedDerivation.lean`). -/
def drWord {G : Type*} [Group G] (s x y : G) : G :=
  (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)

/-- **Naturality of the word shape** under any monoid-hom-like map: `drWord` uses only `*`,
`⁻¹`, `^`, so it pushes through unconditionally (no `ω₂`-powers — contrast
`Marking.map_wildValueR`, which needs a finite source). -/
theorem map_drWord {F G H : Type*} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]
    (φ : F) (s x y : G) : φ (drWord s x y) = drWord (φ s) (φ x) (φ y) := by
  simp only [drWord, conjP, commP, map_mul, map_inv, map_pow]

/-- **Stress test (abelian collapse)** ⟦eq:BR⟧: in a commutative group the conjugations collapse
and the commutator dies, so `drWord s x y = (x⁴)⁻¹ · y²` — the abelianized relation
`−4x̄ + 2ȳ = 0` of note eq. (3.4), pinning the exponent sum `−1 − 3 = −4` on `x` and `2` on `y`
(and the independence from `s`). -/
theorem drWord_comm {G : Type*} [CommGroup G] (s x y : G) :
    drWord s x y = (x ^ 4)⁻¹ * y ^ 2 := by
  rw [drWord, conjP_eq_self, conjP_eq_self, commP_eq_one, mul_one, ← mul_inv_rev, ← pow_succ]

/-! ## The relator and the presented group -/

/-- The **Roe pro-2 relator** `r₂ = (x^s)⁻¹x⁻³y²[y,y^s]` — note eq. (3.1) ⟦lem:pro2word⟧ —
as a word in the free profinite group on `Fin 3` with `s = of 0`, `x = of 1`, `y = of 2`.
It is `ω₂`-free (profinite exponentiation by `ω₂` is the identity on pro-2 elements), hence a
bare word: `drWord` at the generators. -/
noncomputable def drRelator : FreeProfiniteGroup (Fin 3) :=
  drWord (FreeProfiniteGroup.of 0) (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 2)

/-- The full profinite presentation `⟨s, x, y | r₂⟩` (before taking the pro-2 quotient).
The note's `D_R` is **pro-2**, so `D_R` is the maximal pro-2 quotient of this (`DR` below); the
bare presentation is *not* pro-2 — e.g. in an abelian target the relator collapses to
`x⁻⁴y²` (`drWord_comm`), which dies under `x ↦ 0, y ↦ 1` in `ℤ/3`, so the full presentation
surjects onto `ℤ/3` and its abelianization carries an odd part.  Taking the pro-2 quotient is
what makes `B_R = D_R^{ab} = ℤ/2 ⊕ ℤ₂ ⊕ ℤ₂` (note eq. (3.4)–(3.6)) correct. -/
noncomputable def DRFull : ProfiniteGrp := profinitePresentation {drRelator}

/-- **`D_R`** (note eq. (3.1) ⟦lem:pro2word⟧): the **pro-2** group
`⟨s, x, y | (x^s)⁻¹x⁻³y²[y,y^s] = 1⟩_pro-2`, encoded as the maximal pro-2 quotient of the
profinite presentation — the same encoding as `D₀` (`GQ2.D0`) and `Π` (`GQ2.PiBd`). -/
noncomputable def DR : ProfiniteGrp := maxProPQuotient 2 DRFull

/-- The relator holds in the full presentation: `r₂ = 1` in `DRFull`. -/
theorem drRelator_quotientMk_eq_one :
    quotientMk (relatorSubgroup {drRelator}) drRelator = 1 :=
  relator_quotientMk_eq_one {drRelator} rfl

/-! ### The marked generators -/

/-- The generator `s ∈ DRFull` (image of `of 0`; the note's `s = σ`). -/
noncomputable def drFullS : DRFull :=
  quotientMk (relatorSubgroup {drRelator}) (FreeProfiniteGroup.of 0)
/-- The generator `x ∈ DRFull` (image of `of 1`; the note's `x = x₀`). -/
noncomputable def drFullX : DRFull :=
  quotientMk (relatorSubgroup {drRelator}) (FreeProfiniteGroup.of 1)
/-- The generator `y ∈ DRFull` (image of `of 2`; the note's `y = x₁`). -/
noncomputable def drFullY : DRFull :=
  quotientMk (relatorSubgroup {drRelator}) (FreeProfiniteGroup.of 2)

/-- The Roe relation `(x^s)⁻¹x⁻³y²[y,y^s] = 1` already in the full presentation `DRFull`. -/
theorem drFull_relation : drWord drFullS drFullX drFullY = 1 := by
  have h := drRelator_quotientMk_eq_one
  rw [drRelator, map_drWord] at h
  exact h

/-- The generator `s ∈ D_R` (image of `s` under the pro-2 quotient map). -/
noncomputable def drS : DR := maxProPMk 2 DRFull drFullS
/-- The generator `x ∈ D_R`. -/
noncomputable def drX : DR := maxProPMk 2 DRFull drFullX
/-- The generator `y ∈ D_R`. -/
noncomputable def drY : DR := maxProPMk 2 DRFull drFullY

/-- **The Roe relation on the named generators** ⟦lem:pro2word⟧:
`(x^s)⁻¹ · x⁻³ · y² · [y, y^s] = 1` in `D_R`, in `drWord` form.  It holds already in the full
presentation (`drFull_relation`) and is pushed through the pro-2 quotient by `map_drWord`. -/
theorem dr_relation : drWord drS drX drY = 1 := by
  have h : maxProPMk 2 DRFull (drWord drFullS drFullX drFullY) = 1 := by
    rw [drFull_relation, map_one]
  rwa [map_drWord] at h

/-- The Roe relation, spelled out: `(x^s)⁻¹ · (x³)⁻¹ · y² · [y, y^s] = 1` in `D_R`. -/
theorem dr_relation_expanded :
    (conjP drX drS)⁻¹ * (drX ^ 3)⁻¹ * drY ^ 2 * commP drY (conjP drY drS) = 1 :=
  dr_relation

/-- `D_R` is pro-2 (re-export of `isProP_maxProPQuotient` at this instance, for readability at
use sites: characters, `ν_R`, `χ_R`, and the Demushkin package all consume it). -/
theorem isProP_DR : IsProP 2 (DR : Type) := isProP_maxProPQuotient

/-! ## Universal property of `D_R`

A triple in a pro-2 group killing the relator word classifies a continuous hom `D_R → H` —
the local replica of `d0LiftHom` (`GQ2/SectionThree.lean:444`), placed here because every
`D_R`-character in the Route-L development (the `𝔽₂`-dual basis, `ν_R`, `χ_R`) is built from
it. -/

section Lifts

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `D_R`**: a triple `m 0, m 1, m 2` in a pro-2 group `H` with
`drWord (m 0) (m 1) (m 2) = 1` classifies a continuous hom `D_R → H` sending `s, x, y` to
`m 0, m 1, m 2` (`drLiftHom_S/X/Y`). -/
noncomputable def drLiftHom (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : drWord (m 0) (m 1) (m 2) = 1) :
    ContinuousMonoidHom DR H :=
  (maxProPHomEquiv hH).symm
    (quotientLift (relatorSubgroup {drRelator})
      ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom
      (by
        set f := ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom
        have hone : f.toMonoidHom drRelator = 1 := by
          have h0 : f.toMonoidHom (FreeProfiniteGroup.of 0) = m 0 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          have h1 : f.toMonoidHom (FreeProfiniteGroup.of 1) = m 1 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          have h2 : f.toMonoidHom (FreeProfiniteGroup.of 2) = m 2 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          rw [drRelator, map_drWord, h0, h1, h2]
          exact hrel
        refine Subgroup.topologicalClosure_minimal _
          (Subgroup.normalClosure_le_normal ?_) ?_
        · intro r hr
          rw [Set.mem_singleton_iff.mp hr, SetLike.mem_coe, MonoidHom.mem_ker]
          exact hone
        · have hker : (f.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3)))
              = ⇑f ⁻¹' {1} := by
            ext w
            simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
              Set.mem_singleton_iff]
            rfl
          rw [hker]
          exact isClosed_singleton.preimage f.continuous_toFun))

@[simp] lemma drLiftHom_S (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : drWord (m 0) (m 1) (m 2) = 1) :
    drLiftHom hH m hrel drS = m 0 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 DRFull
    (quotientMk (relatorSubgroup {drRelator}) (FreeProfiniteGroup.of 0))) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] lemma drLiftHom_X (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : drWord (m 0) (m 1) (m 2) = 1) :
    drLiftHom hH m hrel drX = m 1 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 DRFull
    (quotientMk (relatorSubgroup {drRelator}) (FreeProfiniteGroup.of 1))) = m 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] lemma drLiftHom_Y (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : drWord (m 0) (m 1) (m 2) = 1) :
    drLiftHom hH m hrel drY = m 2 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 DRFull
    (quotientMk (relatorSubgroup {drRelator}) (FreeProfiniteGroup.of 2))) = m 2
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

end Lifts

/-! ## Stress tests: concrete finite 2-group markings (`decide`)

`drWord` is a computable word (no `ω₂`), so finite evaluations are `decide`-checked directly —
the transcription-slip guard of plan rule 9 (cf. the `Γ_A` campaign's `h₀` erratum). -/

section StressTests

/-- **Stress test (numeric pin, `ℤ/8`)**: at the additive marking `(s, x, y) = (3, 1, 2)` the
relator dies — `−4·1 + 2·2 = 0` — pinning the abelianized exponents of ⟦eq:BR⟧. -/
theorem drWord_zmod8 :
    drWord (Multiplicative.ofAdd (3 : ZMod 8)) (Multiplicative.ofAdd 1)
      (Multiplicative.ofAdd 2) = 1 := by decide

/-- **Stress test (negative pin, `ℤ/8`)**: moving `y` to `1` gives `−4 + 2 = −2 ≡ 6 (mod 8)` —
the relator does *not* die, pinning the `y`-exponent `2` (a bare `y` would give `−3 ≡ 5`, and
`x²` in place of `x³` in the middle factor would give `1·... = 7`). -/
theorem drWord_zmod8_y1 :
    drWord (Multiplicative.ofAdd (3 : ZMod 8)) (Multiplicative.ofAdd 1)
      (Multiplicative.ofAdd 1) = Multiplicative.ofAdd (6 : ZMod 8) := by decide

/-- **Stress test (non-abelian 2-group quotient)**: the marking
`(s, x, y) = (r 2, r 1, sr 0)` of `D₄ = DihedralGroup 4` kills the relator — `s` is central, so
`(x^s)⁻¹x⁻³ = x⁻⁴ = 1` and `[y, y^s] = [y, y] = 1`, while `y² = 1` for the reflection — and
`{r 2, r 1, sr 0}` generates `D₄`.  So the order-8 dihedral group is a genuine non-abelian
finite quotient of `D_R` (the R2 spike's `#Hom(D_R, ·)`-count data confirms
`#Hom(D_R, D₄) = #Hom(D₀, D₄)`). -/
theorem drWord_d4 :
    drWord (DihedralGroup.r 2) (DihedralGroup.r 1) (DihedralGroup.sr 0 : DihedralGroup 4)
      = 1 := by decide

end StressTests

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (3.1) = ⟦lem:pro2word⟧ (`eq:DR`)
  * Lemma 3.2 = ⟦lem:initial⟧ (consumer: `GQ2/Roe/DRDemushkin.lean`)
  * eq. (3.4)–(3.6) = ⟦eq:BR⟧/⟦eq:tR⟧/⟦eq:BRsplit⟧ (abelian collapse stress test)
-/
