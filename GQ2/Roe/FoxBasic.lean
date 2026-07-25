/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Words
public import GQ2.MixedBilinear

@[expose] public section

/-!
# The `r_R` Fox spine: the Roe word complex and the traced mixed coordinate  (Roe note §4)

The `Γ_R` counterparts of the `Γ_A` spine objects of `GQ2.FoxHeisenberg.Basic` (the word complex
(30)/(31) built on the wild relator) and `GQ2.FoxHeisenberg.Heisenberg` (the traced mixed central
coordinate `mixedB`), for the Roe candidate presentation

  `Γ_R = ⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^{ω₂} · x₁² · [x₁, x₁^{σ₂}]⟩`

(note eq. (1.2) ⟦eq:relators⟧, `GQ2.Roe.Words`).  The tame relator is **shared** with `Γ_A`, so
the tame component of every object below is *definitionally* the `Γ_A` one (`d1FunR_fst`,
`d1FunR_tame` — reused, never re-proved); only the wild component changes,
`Marking.wildValue → Marking.wildValueR`.

Provided here, mirroring `Basic.lean`'s names with an `R` suffix:

* **`d1FunR`/`d1R`** — the note §4 differential "obtained by differentiating the two relators"
  (Proposition 4.1 ⟦prop:jacobian⟧, display ⟦eq:jacobian⟧):
  `d1FunR t x = ((liftMarking t x).tameValue.u, (liftMarking t x).wildValueR.u)`.  Additivity
  (`d1FunR_add`) is proved by functoriality from `Marking.map_tameValue`/`map_wildValueR`
  exactly as `d1Fun_add`; the complex identity `d1FunR_comp_d0` forwards the two `Γ_R`
  relations through the inner-automorphism coboundary lift exactly as `d1Fun_comp_d0`.
* the **`R`-word complex** `H0wR/Z1wR/B1wR/H1wR/H2wR` with the chain inclusion `B1wR_le_Z1wR`
  (`H0wR`/`B1wR` are definitionally the shared `H0w`/`B1w` — `d⁰` does not see the relator;
  `H0wR_eq_H0w`, `B1wR_eq_B1w`).
* **`mixedB_R`** — the traced mixed central coordinate at the Heisenberg lift,
  `tameValue.z + wildValueR.z` (mirroring `mixedB`, `GQ2/FoxHeisenberg/Heisenberg.lean:312`),
  with its free-word bridge `bridge_wildR` (the naturality route: `wildValueExpR` carries no
  `ω₂`, so it pushes through `stokesEval` unconditionally — the `Γ_R` twin of `bridge_wild`)
  and the bilinearity `mixedB_R_add_left/right`, `mixedB_R_zero_left/right` ported from
  `GQ2.MixedBilinear`.  The **cocycle closed form** (the note's scalar Gram
  `⟨(a,c,d),(a',c',d')⟩ = ac' + ca' + dd'`, ⟦eq:scalarform⟧) is ticket R25's, not here.

The evaluated closed forms of the wild row (⟦prop:jacobian⟧'s `L_w = Pb + (P + S⁻¹)c`) are in
`GQ2.Roe.WildRow`.
-/

namespace GQ2

namespace FoxH

/-! ## The `R`-word complex (the (30)/(31) clone on the Roe wild relator) -/

section WordComplexR

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **`d¹_R`, function level** (note §4, the differential of display ⟦eq:jacobian⟧): the pair of
`A`-coordinates of the evaluated tame and **Roe** wild relators at the lifted marking — the
`Γ_R` counterpart of `d1Fun`.  The tame component is *identical* to `Γ_A`'s (`d1FunR_fst`). -/
noncomputable def d1FunR (t : Marking C) (x : Fin 4 → A) : A × A :=
  ((liftMarking t x).tameValue.u, (liftMarking t x).wildValueR.u)

/-- **Stress test (shared tame row).**  The tame component of `d1FunR` is definitionally the
`Γ_A` one — the tame relator is shared, so the `Γ_A` tame-row lemmas (`d1Fun_tame`,
`d1Fun_tame_split`) apply verbatim through this equation. -/
theorem d1FunR_fst (t : Marking C) (x : Fin 4 → A) : (d1FunR t x).1 = (d1Fun t x).1 := rfl

/-- The wild component of `d1FunR`, in relator form (the input to `GQ2.Roe.WildRow`'s rows). -/
theorem d1FunR_snd (t : Marking C) (x : Fin 4 → A) :
    (d1FunR t x).2 = (liftMarking t x).wildValueR.u := rfl

/-- **The tame row of `d¹_R`, in closed form** — `Γ_A`'s `d1Fun_tame`, reused (not re-proved):
the note's "The tame row is unchanged from [RT (5.5)]", `L_t = S⁻¹(1+T)a + (S⁻¹+1+T)b`. -/
theorem d1FunR_tame (t : Marking C) (ht : t.TameRel) (x : Fin 4 → A) :
    (d1FunR t x).1
      = t.σ⁻¹ • (t.τ • x 0) - t.σ⁻¹ • x 0 + t.σ⁻¹ • x 1 - (x 1 + t.τ • x 1) :=
  d1Fun_tame t ht x

/-- **`d¹_R` is additive in the lift variables** — the finite Fox rules for the Roe word, proved
by *functoriality* exactly as `d1Fun_add`: evaluate the relators over the coefficient module
`A × A`, then push through the three `C`-equivariant maps `fst, snd, fst + snd : A × A →+ A`
(`Marking.map_tameValue`/`Marking.map_wildValueR` + `WordLift.map`). -/
theorem d1FunR_add [Finite A] [Finite C] (t : Marking C) (x y : Fin 4 → A) :
    d1FunR t (x + y) = d1FunR t x + d1FunR t y := by
  have hfst : ∀ (g : C) (a : A × A),
      (AddMonoidHom.fst A A) (g • a) = g • (AddMonoidHom.fst A A) a := fun _ _ => rfl
  have hsnd : ∀ (g : C) (a : A × A),
      (AddMonoidHom.snd A A) (g • a) = g • (AddMonoidHom.snd A A) a := fun _ _ => rfl
  have hsum : ∀ (g : C) (a : A × A), (AddMonoidHom.fst A A + AddMonoidHom.snd A A) (g • a)
      = g • (AddMonoidHom.fst A A + AddMonoidHom.snd A A) a := by
    intro g a
    show (g • a).1 + (g • a).2 = g • (a.1 + a.2)
    rw [Prod.smul_fst, Prod.smul_snd, smul_add]
  set φ1 := WordLift.map (C := C) (AddMonoidHom.fst A A) hfst with hφ1
  set φ2 := WordLift.map (C := C) (AddMonoidHom.snd A A) hsnd with hφ2
  set φs := WordLift.map (C := C) (AddMonoidHom.fst A A + AddMonoidHom.snd A A) hsum with hφs
  have hL1 : (liftMarking t (fun i => (x i, y i))).map φ1 = liftMarking t x := rfl
  have hL2 : (liftMarking t (fun i => (x i, y i))).map φ2 = liftMarking t y := rfl
  have hLs : (liftMarking t (fun i => (x i, y i))).map φs = liftMarking t (x + y) := rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (x + y)).tameValue.u
        = (liftMarking t x).tameValue.u + (liftMarking t y).tameValue.u
    rw [← hL1, ← hL2, ← hLs, Marking.map_tameValue, Marking.map_tameValue, Marking.map_tameValue,
      hφ1, hφ2, hφs, WordLift.map_u, WordLift.map_u, WordLift.map_u]
    rfl
  · show (liftMarking t (x + y)).wildValueR.u
        = (liftMarking t x).wildValueR.u + (liftMarking t y).wildValueR.u
    rw [← hL1, ← hL2, ← hLs, Marking.map_wildValueR, Marking.map_wildValueR,
      Marking.map_wildValueR, hφ1, hφ2, hφs, WordLift.map_u, WordLift.map_u, WordLift.map_u]
    rfl

/-- **`d¹_R`** bundled on `d1FunR_add` (finite coefficients, per `d1FunR_add`). -/
noncomputable def d1R [Finite A] [Finite C] (t : Marking C) : (Fin 4 → A) →+ A × A :=
  AddMonoidHom.mk' (d1FunR t) (d1FunR_add t)

/-- `d1R` evaluates as `d1FunR`. -/
theorem d1R_apply [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A) :
    d1R t x = d1FunR t x := rfl

/-- **Stress test**: `d1FunR` kills `0` (the additivity bundled in `d1R`). -/
theorem d1FunR_zero [Finite A] [Finite C] (t : Marking C) : d1FunR t (0 : Fin 4 → A) = 0 :=
  (d1R t).map_zero

/-- **The Roe complex is a complex**: `d¹_R ∘ d⁰ = 0` at a marking satisfying the two `Γ_R`
relations.  Proof exactly as `d1Fun_comp_d0`: `liftMarking t (d0 t v)` is `t` pushed through
`g ↦ ⟨g•v − v, g⟩ = ⟨v,1⟩⁻¹⟨0,g⟩⟨v,1⟩`, so its relator values are conjugates of `t`'s — which
are `1` by `TameRel`/`WildRelR` — hence have zero `A`-coordinate. -/
theorem d1FunR_comp_d0 [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (v : A) : d1FunR t (d0 t v) = 0 := by
  let ψ : C →* WordLift A C :=
    (MulAut.conj (⟨v, 1⟩ : WordLift A C)).symm.toMonoidHom.comp WordLift.baseEmbed
  have hψ : ∀ g : C, ψ g = ⟨g • v - v, g⟩ := WordLift.conj_baseEmbed v
  have hkey : liftMarking t (d0 t v) = t.map ψ := by
    simp only [liftMarking, Marking.map, hψ, Marking.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact WordLift.ext (by simp [d0]) rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (d0 t v)).tameValue.u = (0 : A × A).1
    rw [hkey, Marking.map_tameValue, (Marking.tameValue_eq_one_iff t).mpr ht, map_one]
    rfl
  · show (liftMarking t (d0 t v)).wildValueR.u = (0 : A × A).2
    rw [hkey, Marking.map_wildValueR, (Marking.wildValueR_eq_one_iff t).mpr hw, map_one]
    rfl

/-- `H⁰_{R,ρ}(A) = ker d⁰`.  The relator does not enter `d⁰`, so this **is** the shared `H0w`
(`H0wR_eq_H0w`); the `R`-name exists for the Roe complex's uniform API. -/
def H0wR (t : Marking C) : AddSubgroup A := (d0 (A := A) t).ker

/-- `Z¹_{R,ρ}(A) = ker d¹_R` (the Roe degree-one cocycles). -/
noncomputable def Z1wR [Finite A] [Finite C] (t : Marking C) : AddSubgroup (Fin 4 → A) :=
  (d1R (A := A) t).ker

/-- `B¹_{R,ρ}(A) = im d⁰` — again relator-free, `= B1w` (`B1wR_eq_B1w`). -/
def B1wR (t : Marking C) : AddSubgroup (Fin 4 → A) := (d0 (A := A) t).range

/-- **Stress test (shared `d⁰`-layer)**: `H0wR` is definitionally `Γ_A`'s `H0w`. -/
theorem H0wR_eq_H0w (t : Marking C) : H0wR (A := A) t = H0w t := rfl

/-- **Stress test (shared `d⁰`-layer)**: `B1wR` is definitionally `Γ_A`'s `B1w`. -/
theorem B1wR_eq_B1w (t : Marking C) : B1wR (A := A) t = B1w t := rfl

/-- Membership in `Z1wR` is vanishing of `d1FunR`. -/
theorem mem_Z1wR_iff [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A) :
    x ∈ Z1wR (A := A) t ↔ d1FunR t x = 0 :=
  AddMonoidHom.mem_ker

/-- The chain inclusion `B¹ ≤ Z¹_R` under the `Γ_R` relations (mirrors `B1w_le_Z1w`,
`GQ2/Devissage/Naturality.lean`). -/
theorem B1wR_le_Z1wR [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) :
    B1wR (A := A) t ≤ Z1wR (A := A) t := by
  rintro x ⟨v, rfl⟩
  exact AddMonoidHom.mem_ker.mpr (d1FunR_comp_d0 t ht hw v)

/-- `H¹_{R,ρ}(A)` (as for `H1w`: the `addSubgroupOf`-quotient is total — the chain inclusion
`B¹ ≤ Z¹_R` is `B1wR_le_Z1wR`, needed only for lemmas). -/
noncomputable def H1wR [Finite A] [Finite C] (t : Marking C) : Type _ :=
  Z1wR (A := A) t ⧸ (B1wR (A := A) t).addSubgroupOf (Z1wR (A := A) t)

noncomputable instance [Finite A] [Finite C] (t : Marking C) : AddCommGroup (H1wR (A := A) t) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- The class of a degree-one Roe cocycle in `H¹_{R,ρ}`. -/
noncomputable def h1wMkR [Finite A] [Finite C] (t : Marking C) (x : Z1wR (A := A) t) :
    H1wR (A := A) t :=
  QuotientAddGroup.mk x

/-- `H²_{R,ρ}(A) = A² ⧸ im d¹_R`. -/
noncomputable def H2wR [Finite A] [Finite C] (t : Marking C) : Type _ :=
  (A × A) ⧸ (d1R (A := A) t).range

noncomputable instance [Finite A] [Finite C] (t : Marking C) : AddCommGroup (H2wR (A := A) t) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

end WordComplexR

/-! ## The traced mixed coordinate `mixedB_R` -/

section MixedR

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **`B_{R,ρ,A}`**: the *traced* mixed central coordinate of the `Γ_R` word — the sum of the
central coordinates of the two evaluated relators (not the central coordinate of their product),
mirroring `mixedB` (`GQ2/FoxHeisenberg/Heisenberg.lean:312`) with `wildValue → wildValueR`.
Its cocycle closed form — the note's scalar Gram ⟦eq:scalarform⟧, with the honest diagonal `dd'`
in place of `Γ_A`'s opaque `ω₂`-scalar — is ticket R25's `mixedB_cocycle_R`. -/
noncomputable def mixedB_R (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) : ZMod 2 :=
  ((heisMarking t x y).tameValue).z + ((heisMarking t x y).wildValueR).z

/-- **Wild bridge for the Roe word**: the Roe wild relator value at `heisMarking` equals the
free-word evaluation `stokesEval … (wildValueExpR freeMarking e)` at the target-dependent
exponent `e = omega2Exp (exponent H(A)⋊C)` — the `Γ_R` analogue of `bridge_wild`.  Proof:
`wildValueExpR_eq_wildValueR` trades the two `ω₂`-powers for the explicit exponent inside the
finite group `H(A)⋊C`, and `wildValueExpR_map` (no `ω₂`, hence no finiteness) pulls the word
back along the classifying hom `stokesEval (markVec t) x y`.  This is the naturality lemma
feeding the Stokes rows (ticket R23) and the bilinearity below. -/
theorem bridge_wildR [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A)
    (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).wildValueR
      = stokesEval (markVec t) x y
          (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))) := by
  rw [heisMarking_eq_map, wildValueExpR_eq_wildValueR, ← wildValueExpR_map]

/-- **`mixedB_R` is additive in the primal offsets `x`** (ported from `mixedB_add_left`,
`GQ2/MixedBilinear.lean`, with `bridge_wild → bridge_wildR`). -/
theorem mixedB_R_add_left [Finite A] [Finite C] (t : Marking C) (x x' : Fin 4 → A)
    (y : Fin 4 → ElemDual A) :
    mixedB_R t (x + x') y = mixedB_R t x y + mixedB_R t x' y := by
  unfold mixedB_R
  rw [bridge_tame, bridge_wildR, bridge_tame, bridge_wildR, bridge_tame, bridge_wildR,
    stokesEval_z_add_left, stokesEval_z_add_left]
  abel

/-- **`mixedB_R` is additive in the dual offsets `y`** (ported from `mixedB_add_right`). -/
theorem mixedB_R_add_right [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A)
    (y y' : Fin 4 → ElemDual A) :
    mixedB_R t x (y + y') = mixedB_R t x y + mixedB_R t x y' := by
  unfold mixedB_R
  rw [bridge_tame, bridge_wildR, bridge_tame, bridge_wildR, bridge_tame, bridge_wildR,
    stokesEval_z_add_right, stokesEval_z_add_right]
  abel

/-- `mixedB_R t x 0 = 0` (from right-additivity, in the 2-torsion target). -/
theorem mixedB_R_zero_right [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A) :
    mixedB_R t x 0 = 0 := by
  simpa using mixedB_R_add_right t x 0 0

/-- `mixedB_R t 0 y = 0` (from left-additivity, in the 2-torsion target). -/
theorem mixedB_R_zero_left [Finite A] [Finite C] (t : Marking C) (y : Fin 4 → ElemDual A) :
    mixedB_R t 0 y = 0 := by
  simpa using mixedB_R_add_left t 0 0 y

end MixedR

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Proposition 4.1 (Evaluated Jacobian) = ⟦prop:jacobian⟧ — this file supplies the differential
    `d1FunR`/`d1R` and the complex `H0wR/Z1wR/B1wR/H1wR/H2wR`; the evaluated rows are in
    `GQ2.Roe.WildRow` (display ⟦eq:jacobian⟧).
  * Lemma 4.3 (Trivial coefficient) = ⟦lem:trivial⟧ — the scalar Gram ⟦eq:scalarform⟧ on
    `mixedB_R` is ticket R25 (`mixedB_cocycle_R`); this file has only the definition, the
    free-word bridge `bridge_wildR`, and the bilinearity.
  * Lemma 5.1 = ⟦lem:stokes⟧ — the endpoint computation on `bridge_wildR`'s free word is
    `expMod2_wildValueExpR` (`GQ2/Roe/Stokes.lean`, ticket R23); the traced Stokes rows
    (`mixedB_wildRow_R`, `prop_5_8_*_R`) should consume `bridge_wildR` from here.
-/
