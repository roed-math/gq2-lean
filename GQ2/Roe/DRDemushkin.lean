/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Demushkin
public import GQ2.Roe.DRPresentation
public import GQ2.Roe.DRWordCoh

@[expose] public section

/-!
# `D_R` is a rank-3 Demushkin group with `q = 2`  (Roe note Lemma 3.2, ⟦lem:initial⟧)

**Complete** (skeleton ticket R7; the `H¹` side is R12; the `H²` side and the cup Gram matrix are
R13b, through the single-relator obstruction of `GQ2/Roe/DRWordCoh.lean`; the `q`-invariant
consumes ticket R8's abelianization decomposition).

The note's Lemma 3.2: the degree-two initial form of `r₂` is `y² + [x,s]`, so `D_R` is a
rank-three Demushkin group whose cup–Bockstein matrix in the basis dual to `(s, x, y)` is

  `[[0,1,0], [1,0,0], [0,0,1]]`,   ⟦eq:cupmatrix⟧

which is nonsingular.  Per the campaign plan (§3 Route L), *no Zassenhaus filtration is
formalized*: the dimension counts and the Gram matrix are stated in the repo's
cochain/cup vocabulary (`GQ2.ContCoh` + `GQ2.trivialCupPairing`), the route the tree already
knows (`Demushkin.lean`, `WordCoh2.lean`, `CardH2GammaA.lean`), and feed the abstract
`IsDemushkin` predicate — its first load-bearing use.

## Encoding

* Dimensions are `Nat.card` clauses, as in `IsDemushkin`: `dim H¹ = 3` is
  `#H¹(D_R, 𝔽₂) = 8` and `dim H² = 1` is `#H²(D_R, 𝔽₂) = 2`.
* The **dual basis** of `(s, x, y)`: every triple `v : Fin 3 → 𝔽₂` extends to a (continuous)
  character `D_R → 𝔽₂` — the relator dies in any elementary-abelian target since its
  abelianization is `−4x̄ + 2ȳ` (`drWord_comm`) — giving classes `drH1 v ∈ H¹(D_R, 𝔽₂)`;
  `drSStar, drXStar, drYStar` are the coordinate vectors.  That `drH1` is a *bijection*
  `𝔽₂³ ≃ H¹` is the rank-3 statement in basis form (`drH1_bijective` + `card_H1_DR`).
* **The `p = 2` pitfall (R2 spike)**: at `p = 2` the diagonal of ⟦eq:cupmatrix⟧ is the
  Bockstein — `u ∪ u = β(u)` is *additive* in `u` — so the matrix is the **Gram matrix of the
  symmetric bilinear cup form** `GQ2.trivialCupPairing` (with the Bockstein on the diagonal),
  **not** the polar form of a quadratic form (the polar is alternating and would have zero
  diagonal).  The nine entries are stated below as cup values against the dual basis, with
  `#H² = 2` making "`≠ 0`" mean "`= the generator`".  Do not reformulate through
  `QuadraticForm`/Arf: the spike documents how that briefly "refuted" the correct matrix.

## Statement inventory

`card_H1_DR`, `drH1_bijective` (R12); `card_H2_DR`, the nine Gram entries `drCup_*` (R13);
`isDemushkin_DR` (assembly: nondegeneracy from the Gram entries and the basis);
`demushkinRank_DR = 3` (proved from `card_H1_DR`); `demushkinQ_DR = 2` (from R8's
`B_R = C₂t ⊕ ℤ₂s̄ ⊕ ℤ₂x̄`, note eq. (3.6) ⟦eq:BRsplit⟧) — the invariant quadruple consumed by
the B-Lab hypothesis (`GQ2/Roe/MarkedPro2.lean`).
-/

namespace GQ2

open ContCoh

/-! ## The trivial coefficient action

`Aut(ℤ/2) = 1`, so *every* distributive action on `𝔽₂` is trivial; registering the literal
trivial action globally is the house convention (`GQ2/Kummer.lean`, `RStage/GammaA.lean`). -/

instance instDistribMulActionDR : DistribMulAction (DR : Type) (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul (DR : Type) (ZMod 2) := ⟨continuous_snd⟩

/-- The `D_R`-action on `𝔽₂` is trivial (definitional). -/
theorem drSmul_trivial : ∀ (g : (DR : Type)) (m : ZMod 2), g • m = m := fun _ _ => rfl

/-! ## The dual basis of `H¹(D_R, 𝔽₂)` -/

/-- `Multiplicative (ZMod 2)` is pro-2 (a finite 2-group; local clone of
`GQ2.isProP_two_multZMod2`, which lives downstream in `GQ2/SectionThree.lean`). -/
theorem isProP_two_multZMod2_roe : IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-- The multiplicative `𝔽₂`-character of `D_R` with generator values
`s, x, y ↦ v 0, v 1, v 2` (additively): well-defined for **every** triple `v` because the
relator abelianizes to `−4x̄ + 2ȳ = 0` (`drWord_comm`), which is vacuous mod 2 — the Burnside
face of `dim H¹ = 3`. -/
noncomputable def drCharM (v : Fin 3 → ZMod 2) :
    ContinuousMonoidHom (DR : Type) (Multiplicative (ZMod 2)) :=
  drLiftHom isProP_two_multZMod2_roe (fun i => Multiplicative.ofAdd (v i)) (by
    rw [drWord_comm]
    exact (by decide : ∀ a b : Multiplicative (ZMod 2), (a ^ 4)⁻¹ * b ^ 2 = 1) _ _)

@[simp] theorem drCharM_drS (v : Fin 3 → ZMod 2) :
    drCharM v drS = Multiplicative.ofAdd (v 0) := drLiftHom_S _ _ _

@[simp] theorem drCharM_drX (v : Fin 3 → ZMod 2) :
    drCharM v drX = Multiplicative.ofAdd (v 1) := drLiftHom_X _ _ _

@[simp] theorem drCharM_drY (v : Fin 3 → ZMod 2) :
    drCharM v drY = Multiplicative.ofAdd (v 2) := drLiftHom_Y _ _ _

/-- The additive 1-cocycle of the character `drCharM v` (for the trivial action, continuous
1-cocycles *are* continuous additive characters). -/
noncomputable def drZ1 (v : Fin 3 → ZMod 2) : Z1 (DR : Type) (ZMod 2) :=
  ⟨fun g => Multiplicative.toAdd (drCharM v g), by
    refine mem_Z1_iff.mpr ⟨continuous_toAdd.comp (drCharM v).continuous_toFun, ?_⟩
    intro g h
    show Multiplicative.toAdd (drCharM v (g * h))
        = Multiplicative.toAdd (drCharM v g) + g • Multiplicative.toAdd (drCharM v h)
    rw [map_mul, toAdd_mul]
    rfl⟩

/-- The `H¹(D_R, 𝔽₂)`-class with coordinates `v` in the basis dual to `(s, x, y)`. -/
noncomputable def drH1 (v : Fin 3 → ZMod 2) : H1 (DR : Type) (ZMod 2) :=
  H1mk (DR : Type) (ZMod 2) (drZ1 v)

/-- `s* ∈ H¹(D_R, 𝔽₂)`: the class dual to `s`. -/
noncomputable def drSStar : H1 (DR : Type) (ZMod 2) := drH1 ![1, 0, 0]
/-- `x* ∈ H¹(D_R, 𝔽₂)`: the class dual to `x`. -/
noncomputable def drXStar : H1 (DR : Type) (ZMod 2) := drH1 ![0, 1, 0]
/-- `y* ∈ H¹(D_R, 𝔽₂)`: the class dual to `y`. -/
noncomputable def drYStar : H1 (DR : Type) (ZMod 2) := drH1 ![0, 0, 1]

/-! ## Topological generation of `D_R` by `{drS, drX, drY}`

The three named generators topologically generate `D_R` (`GQ2.dr_topGen`, ticket R8), so two
continuous homs out of `D_R` agree once they agree on `drS, drX, drY` — R8's `dr_hom_ext`,
the "characters are determined by generator values" input of `drH1_bijective`-surjectivity. -/

/-! ## `dim H¹ = 3`  (fill: R12) -/

/-- The trivial-action `H¹ ≃+ Z¹` equivalence for `D_R`, abbreviated. -/
private noncomputable def drH1equivZ1 : H1 (DR : Type) (ZMod 2) ≃+ Z1 (DR : Type) (ZMod 2) :=
  H1equivZ1OfTrivial drSmul_trivial

private theorem drH1equivZ1_drH1 (v : Fin 3 → ZMod 2) : drH1equivZ1 (drH1 v) = drZ1 v := rfl

/-- The additive 1-cocycle `drZ1 v`, evaluated at the generator `drS`, returns the coordinate
`v 0` (and similarly `drX ↦ v 1`, `drY ↦ v 2`). -/
private theorem drZ1_apply_drS (v : Fin 3 → ZMod 2) : (drZ1 v).1 drS = v 0 := by
  show Multiplicative.toAdd (drCharM v drS) = v 0
  rw [drCharM_drS]; rfl

private theorem drZ1_apply_drX (v : Fin 3 → ZMod 2) : (drZ1 v).1 drX = v 1 := by
  show Multiplicative.toAdd (drCharM v drX) = v 1
  rw [drCharM_drX]; rfl

private theorem drZ1_apply_drY (v : Fin 3 → ZMod 2) : (drZ1 v).1 drY = v 2 := by
  show Multiplicative.toAdd (drCharM v drY) = v 2
  rw [drCharM_drY]; rfl

/-- **The dual basis is a basis** — `v ↦ drH1 v` is a bijection `𝔽₂³ ≃ H¹(D_R, 𝔽₂)`
⟦lem:initial⟧.  Injectivity evaluates classes on the generators (coboundaries vanish — the action
is trivial); surjectivity is the Burnside/Frattini argument — a continuous 1-cocycle for the
trivial action is a continuous character, determined by its generator values via topological
generation (`dr_hom_ext`), and `drCharM` realizes every triple. -/
theorem drH1_bijective : Function.Bijective drH1 := by
  refine ⟨fun v w h => ?_, fun c => ?_⟩
  · -- injectivity: pass to `Z¹` and evaluate on the generators
    have hz : drZ1 v = drZ1 w := by
      rw [← drH1equivZ1_drH1, ← drH1equivZ1_drH1, h]
    have h0 : v 0 = w 0 := by rw [← drZ1_apply_drS v, ← drZ1_apply_drS w, hz]
    have h1 : v 1 = w 1 := by rw [← drZ1_apply_drX v, ← drZ1_apply_drX w, hz]
    have h2 : v 2 = w 2 := by rw [← drZ1_apply_drY v, ← drZ1_apply_drY w, hz]
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · -- surjectivity: read coordinates off any representing cocycle and rebuild it via `drCharM`
    set z : Z1 (DR : Type) (ZMod 2) := drH1equivZ1 c with hz
    refine ⟨![z.1 drS, z.1 drX, z.1 drY], ?_⟩
    -- the packaged multiplicative character `g ↦ ofAdd (z g)`
    have hcont : Continuous z.1 := (mem_Z1_iff.mp z.2).1
    let φz : (DR : Type) →* Multiplicative (ZMod 2) :=
      { toFun := fun g => Multiplicative.ofAdd (z.1 g)
        map_one' := by rw [Z1_apply_one]; rfl
        map_mul' := fun g h => by
          have hc := (mem_Z1_iff.mp z.2).2 g h
          rw [drSmul_trivial] at hc
          show Multiplicative.ofAdd (z.1 (g * h))
              = Multiplicative.ofAdd (z.1 g) * Multiplicative.ofAdd (z.1 h)
          rw [hc, ofAdd_add] }
    have hφzcont : Continuous ⇑φz := continuous_ofAdd.comp hcont
    -- `drCharM ![…]` and `φz` agree on the generators, hence everywhere
    have hchar : drCharM ![z.1 drS, z.1 drX, z.1 drY]
        = (⟨φz, hφzcont⟩ : ContinuousMonoidHom (DR : Type) (Multiplicative (ZMod 2))) := by
      refine dr_hom_ext _ _ ?_ ?_ ?_
      · show drCharM _ drS = Multiplicative.ofAdd (z.1 drS); rw [drCharM_drS]; rfl
      · show drCharM _ drX = Multiplicative.ofAdd (z.1 drX); rw [drCharM_drX]; rfl
      · show drCharM _ drY = Multiplicative.ofAdd (z.1 drY); rw [drCharM_drY]; rfl
    -- so the rebuilt cocycle equals `z`; transport back to `H¹`
    have hZ : drZ1 ![z.1 drS, z.1 drX, z.1 drY] = z := by
      apply Subtype.ext
      funext g
      show Multiplicative.toAdd (drCharM ![z.1 drS, z.1 drX, z.1 drY] g) = z.1 g
      rw [show drCharM ![z.1 drS, z.1 drX, z.1 drY] g = φz g from DFunLike.congr_fun hchar g]
      rfl
    apply drH1equivZ1.injective
    rw [drH1equivZ1_drH1, hZ, hz]

/-- **`dim_𝔽₂ H¹(D_R, 𝔽₂) = 3`**, in `Nat.card` form ⟦lem:initial⟧ — the rank clause of the
note's Lemma 3.2.  Fill (R12): transport `Nat.card (Fin 3 → ZMod 2) = 8` along
`drH1_bijective`. -/
theorem card_H1_DR : Nat.card (H1 (DR : Type) (ZMod 2)) = 8 := by
  rw [← Nat.card_congr (Equiv.ofBijective drH1 drH1_bijective), Nat.card_eq_fintype_card]
  decide

/-- `H¹(D_R, 𝔽₂)` is finite (clause 1 of `IsDemushkin`; from `card_H1_DR`). -/
theorem finite_H1_DR : Finite (H1 (DR : Type) (ZMod 2)) :=
  Nat.finite_of_card_ne_zero (by rw [card_H1_DR]; norm_num)

/-! ## The elementary-abelian quotient `D_R ↠ 𝔽₂³` and the cup obstruction  (fill: R13b)

The whole `H²` half runs through `GQ2/Roe/DRWordCoh.lean`'s single-relator obstruction
`obsH2_DR : H²(D_R, 𝔽₂) →+ 𝔽₂`, which is **injective** (`obsH2_DR_injective`) because a
2-cocycle with vanishing relator obstruction lifts through `drLiftHom` to a splitting section.
Evaluating `obsH2_DR` on a cup product is then a *finite* computation: the cup cocycle
`(g, h) ↦ z_v(g) · z_w(h)` factors through the elementary-abelian quotient `drE : D_R → 𝔽₂³`
assembled from the dual basis, so `obsH2_DR_eq_of_factor` rewrites the class as the
single-relator obstruction of the explicit `TwoCocycle 𝔽₂³` `drCC v w`, and `decide` evaluates
the relator word `r₂` in the resulting 16-element central extension.

The answer (`drCup_obs`) is the bilinear form `B(v, w) = v₀w₁ + v₁w₀ + v₂w₂`, i.e. exactly the
Gram matrix ⟦eq:cupmatrix⟧ `[[0,1,0],[1,0,0],[0,0,1]]` — the off-diagonal `[x,s]`-pair and the
`y²`-Bockstein.  All nine entries, `#H² = 2` and both nondegeneracy clauses are corollaries of
this single identity. -/

open DRCoh in
/-- The standard basis of `𝔽₂³`: `drBasis 0/1/2` are the coordinate vectors of
`drSStar, drXStar, drYStar`. -/
private def drBasis : Fin 3 → (Fin 3 → ZMod 2) := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

private theorem drSStar_eq : drSStar = drH1 (drBasis 0) := rfl
private theorem drXStar_eq : drXStar = drH1 (drBasis 1) := rfl
private theorem drYStar_eq : drYStar = drH1 (drBasis 2) := rfl

/-- The dual-basis 1-cocycles are additive (the action is trivial, so they are characters). -/
private theorem drZ1_mul (v : Fin 3 → ZMod 2) (g h : (DR : Type)) :
    (drZ1 v).1 (g * h) = (drZ1 v).1 g + (drZ1 v).1 h := by
  show Multiplicative.toAdd (drCharM v (g * h)) = _
  rw [map_mul, toAdd_mul]
  rfl

/-- The **dual-basis quotient** `D_R → 𝔽₂³`, `g ↦ (s*(g), x*(g), y*(g))`.  Assembling the three
dual-basis characters into a single map makes `toAdd (drE g) i = (drZ1 (drBasis i)).1 g` hold by
definition, which is what lets the cup cocycle factor through `𝔽₂³` on the nose. -/
private noncomputable def drE : (DR : Type) →* Multiplicative (Fin 3 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (fun i => (drZ1 (drBasis i)).1 g)
  map_one' := congrArg Multiplicative.ofAdd (funext fun i => Z1_apply_one (drZ1 (drBasis i)))
  map_mul' g h := congrArg Multiplicative.ofAdd (funext fun i => drZ1_mul (drBasis i) g h)

/-- The `𝔽₂`-linear functional on `𝔽₂³` with coordinate vector `v`. -/
private def drEv (v : Fin 3 → ZMod 2) (a : Multiplicative (Fin 3 → ZMod 2)) : ZMod 2 :=
  v 0 * Multiplicative.toAdd a 0 + v 1 * Multiplicative.toAdd a 1 + v 2 * Multiplicative.toAdd a 2

private theorem drEv_mul (v : Fin 3 → ZMod 2) (a b : Multiplicative (Fin 3 → ZMod 2)) :
    drEv v (a * b) = drEv v a + drEv v b := by
  simp only [drEv, show Multiplicative.toAdd (a * b)
      = Multiplicative.toAdd a + Multiplicative.toAdd b from rfl, Pi.add_apply]
  ring

private theorem drEv_one (v : Fin 3 → ZMod 2) : drEv v 1 = 0 := by simp [drEv]

open DRCoh in
/-- The cup cocycle at the `𝔽₂³` level: `κ (a, b) = ⟨v, a⟩ · ⟨w, b⟩`, a 2-cocycle because both
functionals are additive. -/
private def drCC (v w : Fin 3 → ZMod 2) : TwoCocycle (Multiplicative (Fin 3 → ZMod 2)) where
  κ a b := drEv v a * drEv w b
  norm := by rw [drEv_one, zero_mul]
  cocyc a b c := by
    show drEv v a * drEv w b + drEv v (a * b) * drEv w c
      = drEv v a * drEv w (b * c) + drEv v b * drEv w c
    rw [drEv_mul, drEv_mul]; ring

/-- The dual-basis characters read off the coordinates of `drE`, by definition. -/
private theorem drE_coord (i : Fin 3) (g : (DR : Type)) :
    Multiplicative.toAdd (drE g) i = (drZ1 (drBasis i)).1 g := rfl

/-- The marking `drE ∘ (s, x, y)` is the standard basis of `𝔽₂³`. -/
private theorem drE_drGens (k : Fin 3) :
    drE (drGens k) = Multiplicative.ofAdd (fun i => drBasis i k) := by
  refine congrArg Multiplicative.ofAdd (funext fun i => ?_)
  fin_cases k
  · exact drZ1_apply_drS (drBasis i)
  · exact drZ1_apply_drX (drBasis i)
  · exact drZ1_apply_drY (drBasis i)

/-- **Every dual-basis class factors through `drE`**: `z_v = ⟨v, drE ·⟩`.  Both sides are
continuous characters of `D_R`, so R8's `dr_hom_ext` reduces this to the three generator values,
where `drE` is the standard basis. -/
private theorem drZ1_eq_drEv (v : Fin 3 → ZMod 2) (g : (DR : Type)) :
    (drZ1 v).1 g = drEv v (drE g) := by
  have hcont : ∀ i : Fin 3, Continuous (drZ1 (drBasis i)).1 :=
    fun i => (mem_Z1_iff.mp (drZ1 (drBasis i)).2).1
  have hgen : ∀ k : Fin 3, drEv v (drE (drGens k)) = v k := by
    intro k
    rw [drE_drGens]
    fin_cases k
    · show v 0 * 1 + v 1 * 0 + v 2 * 0 = v 0; ring
    · show v 0 * 0 + v 1 * 1 + v 2 * 0 = v 1; ring
    · show v 0 * 0 + v 1 * 0 + v 2 * 1 = v 2; ring
  let ψ : (DR : Type) →* Multiplicative (ZMod 2) :=
    { toFun := fun g => Multiplicative.ofAdd (drEv v (drE g))
      map_one' := by
        show Multiplicative.ofAdd (drEv v (drE 1)) = 1
        rw [map_one, drEv_one]; rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (drEv v (drE (a * b))) = _
        rw [map_mul, drEv_mul, ofAdd_add] }
  have hψcont : Continuous ⇑ψ := by
    show Continuous fun g => Multiplicative.ofAdd (drEv v (drE g))
    refine continuous_ofAdd.comp ?_
    show Continuous fun g => v 0 * (drZ1 (drBasis 0)).1 g + v 1 * (drZ1 (drBasis 1)).1 g
      + v 2 * (drZ1 (drBasis 2)).1 g
    exact ((continuous_const.mul (hcont 0)).add (continuous_const.mul (hcont 1))).add
      (continuous_const.mul (hcont 2))
  have hchar : drCharM v = (⟨ψ, hψcont⟩ :
      ContinuousMonoidHom (DR : Type) (Multiplicative (ZMod 2))) := by
    refine dr_hom_ext _ _ ?_ ?_ ?_
    · show drCharM v drS = Multiplicative.ofAdd (drEv v (drE drS))
      rw [drCharM_drS, show drS = drGens 0 from rfl, hgen 0]
    · show drCharM v drX = Multiplicative.ofAdd (drEv v (drE drX))
      rw [drCharM_drX, show drX = drGens 1 from rfl, hgen 1]
    · show drCharM v drY = Multiplicative.ofAdd (drEv v (drE drY))
      rw [drCharM_drY, show drY = drGens 2 from rfl, hgen 2]
  show Multiplicative.toAdd (drCharM v g) = _
  rw [show drCharM v g = ψ g from DFunLike.congr_fun hchar g]
  rfl

open DRCoh in
/-- **The Gram computation** ⟦eq:cupmatrix⟧: the single-relator obstruction of the `𝔽₂³`-level cup
cocycle is the bilinear form `v₀w₁ + v₁w₀ + v₂w₂`.  Pure finite evaluation of the relator word
`r₂ = (xˢ)⁻¹x⁻³y²[y, yˢ]` in the 16-element central extension, over all 64 pairs `(v, w)`. -/
private theorem drRelZ_drCC (v w : Fin 3 → ZMod 2) :
    drRelZ (fun k => Multiplicative.ofAdd (fun i => drBasis i k)) (drCC v w)
      = v 0 * w 1 + v 1 * w 0 + v 2 * w 2 := by
  revert v w; decide

/-- **The cup obstruction formula.**  `obsH2_DR (v* ⌣ w*) = v₀w₁ + v₁w₀ + v₂w₂` — the Gram
matrix ⟦eq:cupmatrix⟧ in one identity.  Since `obsH2_DR` is injective this determines every cup
product of dual-basis classes. -/
private theorem drCup_obs (v w : Fin 3 → ZMod 2) :
    obsH2_DR drSmul_trivial (drH1 v ⌣[drSmul_trivial] drH1 w)
      = v 0 * w 1 + v 1 * w 0 + v 2 * w 2 := by
  have hμ : ∀ (g : (DR : Type)) (m n : ZMod 2),
      (AddMonoidHom.mul (g • m)) (g • n) = g • (AddMonoidHom.mul m) n :=
    fun g m n => by rw [drSmul_trivial, drSmul_trivial, drSmul_trivial]
  have key := obsH2_DR_eq_of_factor (L := Multiplicative (Fin 3 → ZMod 2)) drSmul_trivial
    ⟨cup11Fun AddMonoidHom.mul (drZ1 v).1 (drZ1 w).1,
      cup11_mem_Z2 AddMonoidHom.mul hμ (drZ1 v) (drZ1 w)⟩
    drE (drCC v w) (fun g h => by
      show (drZ1 v).1 g * (g • (drZ1 w).1 h) = drEv v (drE g) * drEv w (drE h)
      rw [drSmul_trivial, drZ1_eq_drEv, drZ1_eq_drEv])
  rw [show drH1 v ⌣[drSmul_trivial] drH1 w
      = H2mk (DR : Type) (ZMod 2)
          ⟨cup11Fun AddMonoidHom.mul (drZ1 v).1 (drZ1 w).1,
            cup11_mem_Z2 AddMonoidHom.mul hμ (drZ1 v) (drZ1 w)⟩ from rfl, key,
    show (fun k => drE (drGens k))
      = fun k => Multiplicative.ofAdd (fun i => drBasis i k) from funext drE_drGens]
  exact drRelZ_drCC v w

/-- A dual-basis cup product vanishes exactly when its Gram value does (`obsH2_DR` injective). -/
private theorem drCup_eq_zero_of {v w : Fin 3 → ZMod 2}
    (h : v 0 * w 1 + v 1 * w 0 + v 2 * w 2 = 0) : drH1 v ⌣[drSmul_trivial] drH1 w = 0 :=
  obsH2_DR_injective drSmul_trivial (by rw [drCup_obs, h, map_zero])

private theorem drCup_ne_zero_of {v w : Fin 3 → ZMod 2}
    (h : v 0 * w 1 + v 1 * w 0 + v 2 * w 2 ≠ 0) : drH1 v ⌣[drSmul_trivial] drH1 w ≠ 0 :=
  fun hz => h (by rw [← drCup_obs, hz, map_zero])

/-- The zero coordinate vector gives the zero class (its cocycle is `⟨0, drE ·⟩ = 0`). -/
private theorem drH1_zero : drH1 (0 : Fin 3 → ZMod 2) = 0 := by
  have hz : drZ1 (0 : Fin 3 → ZMod 2) = 0 := by
    refine Subtype.ext (funext fun g => ?_)
    rw [drZ1_eq_drEv]
    show (0 : Fin 3 → ZMod 2) 0 * _ + (0 : Fin 3 → ZMod 2) 1 * _
      + (0 : Fin 3 → ZMod 2) 2 * _ = _
    simp
  show H1mk (DR : Type) (ZMod 2) (drZ1 0) = 0
  rw [hz, map_zero]

/-- A non-zero `H¹`-class has a non-zero coordinate (`drH1` kills only the zero vector). -/
private theorem drH1_ne_zero_coords {v : Fin 3 → ZMod 2} (h : drH1 v ≠ 0) :
    v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h0, h1, h2⟩ := hc
  refine h ?_
  rw [show v = 0 from funext fun i => by fin_cases i; exacts [h0, h1, h2], drH1_zero]

/-! ## `dim H² = 1`  (fill: R13) -/

/-- **`dim_𝔽₂ H²(D_R, 𝔽₂) = 1`**, in `Nat.card` form ⟦lem:initial⟧ — "the presentation is
minimal and has one relation".  Fill (R13), one-relator central-extension route (clone of the
`WordCoh2`/`CardH2GammaA` pattern): the upper bound from the single relator through the word
cohomology bridge, the lower bound from a concrete finite central-extension witness detecting a
nonzero class (equivalently, from any nonzero Gram entry below). -/
theorem card_H2_DR : Nat.card (H2 (DR : Type) (ZMod 2)) = 2 := by
  haveI : Finite (H2 (DR : Type) (ZMod 2)) :=
    Finite.of_injective _ (obsH2_DR_injective drSmul_trivial)
  have hle : Nat.card (H2 (DR : Type) (ZMod 2)) ≤ 2 := by
    have h := Nat.card_le_card_of_injective _ (obsH2_DR_injective drSmul_trivial)
    rwa [Nat.card_zmod] at h
  haveI : Nontrivial (H2 (DR : Type) (ZMod 2)) :=
    ⟨drH1 (drBasis 2) ⌣[drSmul_trivial] drH1 (drBasis 2), 0, drCup_ne_zero_of (by decide)⟩
  have hgt : 1 < Nat.card (H2 (DR : Type) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

/-! ## The cup–Bockstein Gram matrix  ⟦eq:cupmatrix⟧  (fill: R13)

The nine entries of the matrix `[[0,1,0],[1,0,0],[0,0,1]]` of the symmetric bilinear cup form
on `H¹(D_R, 𝔽₂)` in the dual basis `(s*, x*, y*)` — rows and columns in that order, diagonal
entries the Bocksteins (`u ∪ u = β(u)` at `p = 2`; see the module docstring for the
quadratic-form trap).  With `card_H2_DR`, "`≠ 0`" says "`= the generator of H² ≅ 𝔽₂`".  Both
triangles are stated since graded-commutativity of `cup11` is not formalized (the
`IsDemushkin.nondegen_left/right` precedent). -/

/-- Gram entry `(s, s) = 0`: the Bockstein `β(s*) = s* ∪ s*` vanishes (no `s²` in the initial
form of `r₂`). -/
theorem drCup_ss : drSStar ⌣[drSmul_trivial] drSStar = 0 := by
  rw [drSStar_eq]; exact drCup_eq_zero_of (by decide)

/-- Gram entry `(s, x) = 1`: `s* ∪ x* ≠ 0` — the `[x, s]`-term of the initial form
`y² + [x,s]` ⟦lem:initial⟧. -/
theorem drCup_sx : drSStar ⌣[drSmul_trivial] drXStar ≠ 0 := by
  rw [drSStar_eq, drXStar_eq]; exact drCup_ne_zero_of (by decide)

/-- Gram entry `(s, y) = 0`. -/
theorem drCup_sy : drSStar ⌣[drSmul_trivial] drYStar = 0 := by
  rw [drSStar_eq, drYStar_eq]; exact drCup_eq_zero_of (by decide)

/-- Gram entry `(x, s) = 1` (the transpose of `drCup_sx`; stated separately since
graded-commutativity is not formalized). -/
theorem drCup_xs : drXStar ⌣[drSmul_trivial] drSStar ≠ 0 := by
  rw [drXStar_eq, drSStar_eq]; exact drCup_ne_zero_of (by decide)

/-- Gram entry `(x, x) = 0`: the Bockstein `β(x*)` vanishes — `x` enters `r₂` with exponent
`−4 ≡ 0 (mod 4)`. -/
theorem drCup_xx : drXStar ⌣[drSmul_trivial] drXStar = 0 := by
  rw [drXStar_eq]; exact drCup_eq_zero_of (by decide)

/-- Gram entry `(x, y) = 0`. -/
theorem drCup_xy : drXStar ⌣[drSmul_trivial] drYStar = 0 := by
  rw [drXStar_eq, drYStar_eq]; exact drCup_eq_zero_of (by decide)

/-- Gram entry `(y, s) = 0`. -/
theorem drCup_ys : drYStar ⌣[drSmul_trivial] drSStar = 0 := by
  rw [drYStar_eq, drSStar_eq]; exact drCup_eq_zero_of (by decide)

/-- Gram entry `(y, x) = 0`. -/
theorem drCup_yx : drYStar ⌣[drSmul_trivial] drXStar = 0 := by
  rw [drYStar_eq, drXStar_eq]; exact drCup_eq_zero_of (by decide)

/-- Gram entry `(y, y) = 1`: the Bockstein `β(y*) = y* ∪ y* ≠ 0` — the `y²`-term of the
initial form `y² + [x,s]` ⟦lem:initial⟧, and the diagonal `1` that makes the matrix
nonsingular over `𝔽₂` (`det = 1`). -/
theorem drCup_yy : drYStar ⌣[drSmul_trivial] drYStar ≠ 0 := by
  rw [drYStar_eq]; exact drCup_ne_zero_of (by decide)

/-! ## The Demushkin package -/

/-- **`D_R` is a Demushkin pro-2 group** ⟦lem:initial⟧ — "this is exactly the defining
cohomological condition".  The first load-bearing use of the abstract `IsDemushkin` predicate.
Nondegeneracy fill (R13, after the Gram entries): a class `a·s* + b·x* + c·y*` cups with `x*`
to `a`, with `s*` to `b`, and with `y*` to `c` — the matrix `[[0,1,0],[1,0,0],[0,0,1]]` is
nonsingular — using `drH1_bijective` to write an arbitrary nonzero class in coordinates. -/
theorem isDemushkin_DR : IsDemushkin 2 (DR : Type) :=
  { smul_trivial := drSmul_trivial
    isProP := isProP_DR
    finiteH1 := finite_H1_DR
    cardH2 := card_H2_DR
    nondegen_left := by
      intro x hx
      obtain ⟨v, rfl⟩ := drH1_bijective.surjective x
      rcases drH1_ne_zero_coords hx with h | h | h
      · refine ⟨drH1 (drBasis 1), drCup_ne_zero_of ?_⟩
        show v 0 * 1 + v 1 * 0 + v 2 * 0 ≠ 0
        simpa using h
      · refine ⟨drH1 (drBasis 0), drCup_ne_zero_of ?_⟩
        show v 0 * 0 + v 1 * 1 + v 2 * 0 ≠ 0
        simpa using h
      · refine ⟨drH1 (drBasis 2), drCup_ne_zero_of ?_⟩
        show v 0 * 0 + v 1 * 0 + v 2 * 1 ≠ 0
        simpa using h
    nondegen_right := by
      intro y hy
      obtain ⟨w, rfl⟩ := drH1_bijective.surjective y
      rcases drH1_ne_zero_coords hy with h | h | h
      · refine ⟨drH1 (drBasis 1), drCup_ne_zero_of ?_⟩
        show (0 : ZMod 2) * w 1 + 1 * w 0 + 0 * w 2 ≠ 0
        simpa using h
      · refine ⟨drH1 (drBasis 0), drCup_ne_zero_of ?_⟩
        show (1 : ZMod 2) * w 1 + 0 * w 0 + 0 * w 2 ≠ 0
        simpa using h
      · refine ⟨drH1 (drBasis 2), drCup_ne_zero_of ?_⟩
        show (0 : ZMod 2) * w 1 + 0 * w 0 + 1 * w 2 ≠ 0
        simpa using h }

/-- **`D_R` has Demushkin rank 3** ⟦lem:initial⟧ (`8 = 2³`; proved from `card_H1_DR`). -/
theorem demushkinRank_DR : demushkinRank 2 (DR : Type) = 3 :=
  demushkinRank_eq_of_card (by rw [card_H1_DR]; norm_num)

/-- **`D_R` has `q`-invariant 2** ⟦eq:BR⟧/⟦eq:BRsplit⟧ (note (3.4)–(3.6)): the topological
abelianization is `B_R = ⟨s̄, x̄, ȳ | −4x̄ + 2ȳ = 0⟩ = C₂·t ⊕ ℤ₂·s̄ ⊕ ℤ₂·x̄` with
`t = ȳ − 2x̄`, whose torsion subgroup has order 2.  Fill: from ticket R8's `BRDecomposition`
(the `BDecomposition` clone; see the R7 design memo §R8). -/
theorem demushkinQ_DR : demushkinQ (DR : Type) = 2 := GQ2.demushkinQ_DR_eq_two

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 3.2 = ⟦lem:initial⟧
  * eq. (3.2) = ⟦eq:cupmatrix⟧
  * eq. (3.4)–(3.6) = ⟦eq:BR⟧/⟦eq:tR⟧/⟦eq:BRsplit⟧ (`demushkinQ_DR`; fill via ticket R8)
-/
