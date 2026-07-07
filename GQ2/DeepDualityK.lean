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

section Invariance

/-- `conjMap` is multiplicative in the kernel argument. -/
theorem conjMap_mul_apply (g : AbsGalQ2)
    (n m : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    conjMap ρ g (n * m) = conjMap ρ g n * conjMap ρ g m := by
  apply Subtype.ext
  show g⁻¹ * ((n : AbsGalQ2) * (m : AbsGalQ2)) * g
    = (g⁻¹ * (n : AbsGalQ2) * g) * (g⁻¹ * (m : AbsGalQ2) * g)
  group

/-- `conjMap ρ g⁻¹` inverts `conjMap ρ g`. -/
theorem conjMap_inv_conjMap (g : AbsGalQ2)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    conjMap ρ g⁻¹ (conjMap ρ g n) = n := by
  apply Subtype.ext
  show (g⁻¹)⁻¹ * (g⁻¹ * (n : AbsGalQ2) * g) * g⁻¹ = (n : AbsGalQ2)
  group

/-- `conjMap ρ g` inverts `conjMap ρ g⁻¹`. -/
theorem conjMap_conjMap_inv (g : AbsGalQ2)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    conjMap ρ g (conjMap ρ g⁻¹ n) = n := by
  apply Subtype.ext
  show g⁻¹ * ((g⁻¹)⁻¹ * (n : AbsGalQ2) * g⁻¹) * g = (n : AbsGalQ2)
  group

/-- **Coboundary transport along conjugation**: precomposition with `conjMap × conjMap` carries
`B²(ker ρ, μ₂)` into itself (`δ¹ψ ↦ δ¹(ψ ∘ conjMap)`; the coefficient action is trivial). -/
theorem comp_conjMap_mem_B2 (g : AbsGalQ2)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) × ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      → MuN 2}
    (hf : f ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2)) :
    (fun p => f (conjMap ρ g p.1, conjMap ρ g p.2))
      ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) := by
  obtain ⟨ψ, hψ, rfl⟩ := hf
  refine ⟨ψ ∘ conjMap ρ g, ?_, ?_⟩
  · exact (mem_C1_iff.mp hψ).comp (continuous_conjMap ρ g)
  · funext p
    show p.1 • ψ (conjMap ρ g p.2) - ψ (conjMap ρ g (p.1 * p.2)) + ψ (conjMap ρ g p.1)
      = conjMap ρ g p.1 • ψ (conjMap ρ g p.2)
        - ψ (conjMap ρ g p.1 * conjMap ρ g p.2) + ψ (conjMap ρ g p.1)
    rw [smul_muN_two_trivial_ker, smul_muN_two_trivial_ker, conjMap_mul_apply]

/-- The two-sided form: precomposition with `conjMap × conjMap` preserves `B²` in both
directions. -/
theorem comp_conjMap_mem_B2_iff (g : AbsGalQ2)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) × ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      → MuN 2} :
    ((fun p => f (conjMap ρ g p.1, conjMap ρ g p.2))
        ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2))
      ↔ f ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) := by
  constructor
  · intro h
    have h' := comp_conjMap_mem_B2 ρ g⁻¹ h
    have hfun : (fun p : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          × ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        f (conjMap ρ g (conjMap ρ g⁻¹ p.1), conjMap ρ g (conjMap ρ g⁻¹ p.2))) = f := by
      funext p
      rw [conjMap_conjMap_inv, conjMap_conjMap_inv]
    rwa [hfun] at h'
  · exact comp_conjMap_mem_B2 ρ g

/-- `conjAct` on an `H1mk`-class: the mk-level form of `conjAct_h1ofFun`. -/
theorem conjAct_H1mk (g : AbsGalQ2)
    (a : ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))) :
    conjAct ρ g (H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) a)
      = H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)
          ⟨fun n => a.1 (conjMap ρ g n), comp_conjMap_mem_Z1 ρ a.2 g⟩ := by
  rw [show H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) a
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) a.1 from (H1ofFun_of_mem a.2).symm,
    conjAct_h1ofFun ρ g a.2, H1ofFun_of_mem (comp_conjMap_mem_Z1 ρ a.2 g)]

section ConjInvariance

variable [Finite C]

/-- The invariant map kills conjugation: if the cocycle `Fc` is (pointwise) `F` precomposed
with `conjMap × conjMap`, the two `inv`-values agree.  `ZMod 2`-valued, so it suffices that the
two classes vanish together — and vanishing is `B²`-membership, transported by
`comp_conjMap_mem_B2_iff`.  (Stated with the composition as an *equation hypothesis* so the
call site avoids higher-order unification.) -/
theorem inv_H2mk_eq_of_comp_conjMap (g : AbsGalQ2)
    (Fc F : ↥(Z2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2)))
    (hco : Fc.1 = fun p => F.1 (conjMap ρ g p.1, conjMap ρ g p.2)) :
    (tateDualityK ρ).inv (H2mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) Fc)
      = (tateDualityK ρ).inv (H2mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) F) := by
  have h2 : ∀ u v : ZMod 2, (u = 0 ↔ v = 0) → u = v := by decide
  have hiv : ∀ W : H2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2),
      (tateDualityK ρ).inv W = 0 ↔ W = 0 := fun W =>
    ⟨fun h => (tateDualityK ρ).inv.injective (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  have hz : ∀ W : ↥(Z2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2)),
      (H2mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) W = 0)
        ↔ W.1 ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2) := fun W =>
    (QuotientAddGroup.eq_zero_iff W).trans AddSubgroup.mem_addSubgroupOf
  refine h2 _ _ ?_
  rw [hiv, hiv, hz, hz, hco]
  exact comp_conjMap_mem_B2_iff ρ g

/-- **(H1) Conjugation invariance of the K-level pairing**: `B(g·x, g·y) = B(x, y)` for the
`conjAct`-action of any `g : G_ℚ₂`.  The transported cup cocycle is on the nose the original
precomposed with `conjMap × conjMap` (the coefficient actions are trivial), and the invariant
map kills that precomposition (`inv_H2mk_comp_conjMap`). -/
theorem pairingK_conjAct (g : AbsGalQ2)
    (x y : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    pairingK ρ (conjAct ρ g x) (conjAct ρ g y) = pairingK ρ x y := by
  obtain ⟨a, rfl⟩ := H1mk_surjective x
  obtain ⟨b, rfl⟩ := H1mk_surjective y
  rw [conjAct_H1mk, conjAct_H1mk]
  show (tateDualityK ρ).inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ)
          (H1mk _ _ ⟨fun n => a.1 (conjMap ρ g n), comp_conjMap_mem_Z1 ρ a.2 g⟩))
        (H1mk _ _ ⟨fun n => b.1 (conjMap ρ g n), comp_conjMap_mem_Z1 ρ b.2 g⟩))
    = (tateDualityK ρ).inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ)
          (H1mk _ _ a)) (H1mk _ _ b))
  rw [H1congr_mk, H1congr_mk, cup11_mk_mk, cup11_mk_mk]
  exact inv_H2mk_eq_of_comp_conjMap ρ g _ _ (funext fun p => rfl)

/-- **(H1) in `conjModule` form** — the literal `hBinv` hypothesis of the abstract `hduality`
(`card_equivHoms_deep_eq_quot` with `instA := conjModule ρ hρsurj`). -/
theorem pairingK_conjModule (hρsurj : Function.Surjective ⇑ρ) (c : C)
    (x y : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    letI := conjModule ρ hρsurj
    pairingK ρ (c • x) (c • y) = pairingK ρ x y := by
  letI := conjModule ρ hρsurj
  show pairingK ρ (conjAct ρ (Function.surjInv hρsurj c) x)
      (conjAct ρ (Function.surjInv hρsurj c) y) = pairingK ρ x y
  exact pairingK_conjAct ρ _ x y

end ConjInvariance

end Invariance

end GQ2
