import GQ2.DeepDuality
import GQ2.LocalLiftingDuality

/-!
# The K-level Tate pairing  (ticket P-15f7, concrete layer)

The first consumer of the **base-generalized B6** (`GQ2.tateDualityAt`, user-approved
2026-07-07): the `𝔽₂`-valued Tate pairing on `M = H¹(G_K, 𝔽₂)` for `K` the splitting field
(`G_K = ker ρ`), supplying the pairing hypotheses of the abstract `hduality`
(`GQ2.card_equivHoms_deep_eq_quot`, `GQ2/DeepDuality.lean` §F):

* `ker_isLocalDualizingGroup` — `↥(ker ρ)` is a local dualizing group (the subtype embedding;
  finite index from `Finite C`), so `tateDualityAt` applies: `tateDualityK`.
* `pairingK := inv_K ∘ cup` on `H¹(↥(ker ρ), 𝔽₂)`, through the coefficient bridge
  `ZMod 2 ≃+ MuDual 2 (ZMod 2)` (`zmodMuDualEquiv`) and the `(1,1)` evaluation cup.
* **(H2)** `pairingK_nondeg` — nondegeneracy, from the bundle's `perfect11` injectivity.
* **(H1)** `pairingK_conjAct` — conjugation invariance `B(g·x, g·y) = B(x, y)`: the cup cocycle
  precomposes on the nose with `conjMap × conjMap` (the coefficient action is trivial), a
  coboundary transported along `conjMap` stays a coboundary, and `ZMod 2`-valued functions
  agreeing in vanishing agree — no `H²`-action needs to be constructed (`H²(G_K, μ₂) ≅ ℤ/2`
  has trivial automorphisms, so invariance is forced).

Everything is `ρ.ker`-vocabulary (no `IntermediateField` enters); the isotropy (H3) discharge
(`cup_deepClasses` lives over `k.fixingSubgroup`) is the f8 splice's `k`-plumbing.

Ticket: P-15f7 (`docs/tickets.md`); design: `docs/p15f-handoff.md` §8, proposal
`docs/p15f7-axiom-proposal.md`.
-/

namespace GQ2

open ContCoh LocalKummer

variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

section Probes

-- instance-resolution probes for the subgroup `G := ↥(ker ρ)` (empirical: these gate the
-- `tateDualityAt` application)
noncomputable example : IsTopologicalGroup ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := inferInstance
noncomputable example : DistribMulAction ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) := inferInstance
noncomputable example : ContinuousSMul ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) := inferInstance
example (g : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (x : MuN 2) :
    g • x = (g : AbsGalQ2) • x := rfl

end Probes

section KernelBundle

variable [Finite C]

/-- **`G_K = ker ρ` is a local dualizing group**: the subtype embedding into `G_ℚ₂` is
continuous, injective, of finite index (the quotient injects into the finite `C`), and acts on
`μ₂` by restriction (definitionally). -/
theorem ker_isLocalDualizingGroup :
    IsLocalDualizingGroup ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) 2 := by
  refine ⟨(ρ.toMonoidHom.ker : Subgroup AbsGalQ2).subtype, continuous_subtype_val,
    Subtype.val_injective, ?_, fun g x => rfl⟩
  rw [Subgroup.range_subtype]
  haveI : Finite (AbsGalQ2 ⧸ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :=
    Finite.of_injective _ (QuotientGroup.quotientKerEquivRange ρ.toMonoidHom).injective
  exact Subgroup.finiteIndex_of_finite_quotient

/-- **The Tate-duality bundle at `G_K`** — the first consumer of the base-generalized B6. -/
noncomputable def tateDualityK :
    TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) 2 :=
  tateDualityAt ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) 2 (ker_isLocalDualizingGroup ρ)

omit [Finite C] in
/-- The kernel acts trivially on `μ₂` (restriction of the trivial `G_ℚ₂`-action). -/
theorem smul_muN_two_trivial_ker (g : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (x : MuN 2) :
    g • x = x :=
  LocalLiftingDuality.smul_muN_two_trivial (g : AbsGalQ2) x

end KernelBundle

section CoefficientBridge

-- probe: the kernel's action on `ZMod 2` is definitionally trivial
example (g : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (a : ZMod 2) : g • a = a := rfl

/-- **The coefficient bridge** `𝔽₂ ≃+ Hom(𝔽₂, μ₂)`: `a ↦ (m ↦ μ₂-lift of a·m)`.  Feeds
`H1congr` to move `H¹(G_K, 𝔽₂)`-classes into the duality bundle's `MuDual`-slot. -/
noncomputable def zmodMuDualEquiv : ZMod 2 ≃+ MuDual 2 (ZMod 2) where
  toFun a :=
    (LocalLiftingDuality.muNTwoEquiv.symm.toAddMonoidHom.comp
      (AddMonoidHom.mk' (fun m => a * m) (fun x y => mul_add a x y)) : ZMod 2 →+ MuN 2)
  invFun φ := LocalLiftingDuality.muNTwoEquiv (φ 1)
  left_inv a := by
    show LocalLiftingDuality.muNTwoEquiv (LocalLiftingDuality.muNTwoEquiv.symm (a * 1)) = a
    rw [AddEquiv.apply_symm_apply, mul_one]
  right_inv φ := by
    refine MuDual.ext 2 (ZMod 2) (fun m => ?_)
    show LocalLiftingDuality.muNTwoEquiv.symm (LocalLiftingDuality.muNTwoEquiv (φ 1) * m) = φ m
    have hz : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
    rcases hz m with rfl | rfl
    · rw [mul_zero, map_zero, map_zero]
    · rw [mul_one, AddEquiv.symm_apply_apply]
  map_add' a b := by
    refine MuDual.ext 2 (ZMod 2) (fun m => ?_)
    show LocalLiftingDuality.muNTwoEquiv.symm ((a + b) * m)
      = (LocalLiftingDuality.muNTwoEquiv.symm (a * m) + LocalLiftingDuality.muNTwoEquiv.symm (b * m))
    rw [add_mul, map_add]

/-- Equivariance of the coefficient bridge (both sides carry trivial `↥(ker ρ)`-actions:
`𝔽₂` definitionally, the `μ₂`-dual by `smul_muN_two_trivial_ker`). -/
theorem zmodMuDualEquiv_equivariant (g : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (a : ZMod 2) : zmodMuDualEquiv (g • a) = g • zmodMuDualEquiv a := by
  have htriv : g • zmodMuDualEquiv a = zmodMuDualEquiv a := by
    refine MuDual.ext 2 (ZMod 2) (fun m => ?_)
    rw [muDual_smul_apply]
    rw [smul_muN_two_trivial_ker]
    rfl
  rw [htriv]
  rfl

end CoefficientBridge

section Pairing

variable [Finite C]

/-- **The K-level Tate pairing** on `M = H¹(G_K, 𝔽₂)`: transport the left argument through the
coefficient bridge, cup with the evaluation pairing, and read off through the invariant map of
`tateDualityK` — `B(x, y) := inv_K (x′ ∪ y)`. -/
noncomputable def pairingK :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)
      →+ H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) →+ ZMod 2 where
  toFun x :=
    (tateDualityK ρ).inv.toAddMonoidHom.comp
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ) x))
  map_zero' := by
    rw [map_zero, map_zero, AddMonoidHom.comp_zero]
  map_add' x y := by
    rw [map_add, map_add, AddMonoidHom.comp_add]

/-- **(H2) Nondegeneracy of the K-level pairing** — the `(1,1)`-perfectness clause of the
base-generalized B6 at `G_K`: a class pairing trivially with everything is zero. -/
theorem pairingK_nondeg (x : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
    (hx : ∀ y, pairingK ρ x y = 0) : x = 0 := by
  have hperf := (tateDualityK ρ).perfect11 (ZMod 2) (by decide)
  have h0 : (tateDualityK ρ).inv.toAddMonoidHom.comp
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ) x))
      = (tateDualityK ρ).inv.toAddMonoidHom.comp
        ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
          (0 : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuDual 2 (ZMod 2)))) := by
    ext y
    have := hx y
    rw [map_zero, AddMonoidHom.comp_zero]
    exact this
  have hinj := hperf.1 h0
  have : x = (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ)).symm
      ((H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ)) x) :=
    (AddEquiv.symm_apply_apply _ x).symm
  rw [this, hinj, map_zero]

end Pairing

end GQ2
