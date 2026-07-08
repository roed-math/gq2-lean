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

/-! ## The (H3) isotropy splice: `pairingK` vanishes on deep × deep

Eq. (94)'s `(U_{e+1}, U_{e+1}) = 1` in class vocabulary.  The Tier-5 fact
(`LocalKummer.cup_deepClasses`, over the finite base `k` with the `𝔽₂`-valued
`trivialCupPairing`) splices to `pairingK` on `H¹(ker ρ, 𝔽₂)` across two boundaries:

* the **group view** `ker ρ = G_k`, taken POINTWISE (`hker : x ∈ ker ρ ↔ x ∈ k.fixingSubgroup`)
  so that no subgroup-equality cast is ever formed — the cup cocycles on the two sides are
  literally the same functions of the underlying group elements, and the `k`-side coboundary
  witness `ψ` transports by precomposition with the identity inclusion `kerToFixing`;
* the **coefficient bridge** `𝔽₂ ≃+ μ₂` (`muNTwoEquiv.symm`), which carries the transported
  witness's coboundary identity over pointwise (`map_sub`/`map_add`; all actions trivial).

Since `inv_K` is injective, vanishing of the `H²(μ₂)`-class (= `B²`-membership of the explicit
cup cocycle) forces `pairingK = 0`.  No new leaf: the axioms are `tateDualityAt` (B6′) plus
`cup_deepClasses`'s Tier-5 chain. -/

section IsotropySplice

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The identity inclusion `↥(ker ρ) → ↥(k.fixingSubgroup)` under a pointwise identification
of the kernel with the fixing subgroup (`G_K = ker ρ`). -/
def kerToFixing (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) : ↥k.fixingSubgroup :=
  ⟨(n : AbsGalQ2), (hker n.1).mp n.2⟩

/-- `kerToFixing` is multiplicative (both sides are the ambient product). -/
theorem kerToFixing_mul (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (n m : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    kerToFixing ρ k hker (n * m) = kerToFixing ρ k hker n * kerToFixing ρ k hker m :=
  Subtype.ext rfl

/-- `kerToFixing` is continuous (it is the identity on underlying elements). -/
theorem continuous_kerToFixing (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    Continuous (kerToFixing ρ k hker) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- Norm bridge for MID units, the `≤`-mirror of `LocalKummer.norm_sub_one_lt_of_isDeepUnit`:
`A = 1 + 2b` with `‖b‖ ≤ 1` gives `‖A − 1‖ ≤ ‖2‖`. -/
theorem norm_sub_one_le_of_isMidUnit {N : Subgroup (Kummer.GaloisGroup ℚ_[2])}
    {A : ℚ̄₂} (h : IsMidUnit N A) : ‖A - 1‖ ≤ ‖(2 : ℚ̄₂)‖ := by
  obtain ⟨-, -, b, -, hAb, hb⟩ := h
  rw [hAb, add_sub_cancel_left, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hb

/-- **Bridge `midClasses → kummerClassK`** — the `≤`-mirror of
`LocalKummer.deepClass_eq_kummerClassK`: over a finite base `k`, a mid Kummer class in
`H¹(G_k, 𝔽₂)` is the Kummer class of a genuine `U_e`-unit `a ∈ kˣ` (`‖a − 1‖ ≤ ‖2‖`). -/
theorem midClass_eq_kummerClassK (k : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k] {ξ : H1 k.fixingSubgroup (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroup k.fixingSubgroup) :
    ∃ a : (↥k)ˣ, ‖((a : ↥k) : ℚ̄₂) - 1‖ ≤ ‖(2 : ℚ̄₂)‖ ∧ kummerClassK k a = ξ := by
  obtain ⟨A, β, hmid, hsq, hβ0, heq⟩ := hξ
  have hAk : A ∈ k := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup k]
    exact (IntermediateField.mem_fixedField_iff _ A).mpr hmid.2.1
  have hA0 : (⟨A, hAk⟩ : ↥k) ≠ 0 := by
    rw [Ne, Subtype.ext_iff]; exact hmid.1
  have hcoe : ((⟨A, hAk⟩ : ↥k) : ℚ̄₂) = A := rfl
  refine ⟨Units.mk0 ⟨A, hAk⟩ hA0, ?_, ?_⟩
  · show ‖((⟨A, hAk⟩ : ↥k) : ℚ̄₂) - 1‖ ≤ ‖(2 : ℚ̄₂)‖
    rw [hcoe]; exact norm_sub_one_le_of_isMidUnit hmid
  · have hccfun : Kummer.kummerCocycleFun (GQ2.sqrtCl A) = Kummer.kummerCocycleFun β := by
      have hsq2 : GQ2.sqrtCl A ^ 2 = A := GQ2.sqrtCl_sq A
      have hfac : (β - GQ2.sqrtCl A) * (β + GQ2.sqrtCl A) = 0 := by
        have hbb : β ^ 2 = GQ2.sqrtCl A ^ 2 := by rw [hsq, hsq2]
        linear_combination hbb
      rcases mul_eq_zero.1 hfac with h | h
      · rw [sub_eq_zero.1 h]
      · rw [eq_neg_of_add_eq_zero_left h, Kummer.kummerCocycleFun_neg]
    have hmemβ : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
        ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      (GQ2.kummerZ1On k.fixingSubgroup hsq hβ0 hmid.2.1).2
    rw [← heq, H1ofFun_of_mem hmemβ]
    unfold GQ2.kummerClassK
    congr 1
    apply Subtype.ext
    funext g
    show Kummer.kummerCocycleFun (GQ2.sqrtCl ((Units.mk0 (⟨A, hAk⟩ : ↥k) hA0 : ↥k)
        : ℚ̄₂)) _ = Kummer.kummerCocycleFun β _
    rw [show ((Units.mk0 (⟨A, hAk⟩ : ↥k) hA0 : ↥k) : ℚ̄₂) = A from rfl, hccfun]

/-- **Eq. (94), mid ⟂ deep in class vocabulary** over the finite base `k`
(`(U_e, U_{e+1}) = 1`) — combines the two `kummerClassK` bridges with the Tier-5
`cup_mid_deep`. -/
theorem cup_midClasses_deepClasses (k : IntermediateField ℚ_[2] ℚ̄₂)
    [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    {ξ η : H1 k.fixingSubgroup (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroup k.fixingSubgroup)
    (hη : η ∈ deepClasses k.fixingSubgroup) :
    trivialCupPairing 2 k.fixingSubgroup htriv ξ η = 0 := by
  obtain ⟨a, ha, rfl⟩ := midClass_eq_kummerClassK k hξ
  obtain ⟨b, hb, rfl⟩ := deepClass_eq_kummerClassK k hη
  exact cup_mid_deep k htriv a b ha hb

variable [Finite C]

/-- **(H3) Isotropy of the deep classes under the K-level pairing**: two deep Kummer classes
pair to zero.  Spliced from the Tier-5 `cup_deepClasses` as described in the section header. -/
theorem pairingK_deep_deep (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)}
    (hξ : ξ ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (hη : η ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    pairingK ρ ξ η = 0 := by
  obtain ⟨A, β, hdA, hsqA, hβ0, rfl⟩ := hξ
  obtain ⟨B, δ, hdB, hsqB, hδ0, rfl⟩ := hη
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hdA
  obtain ⟨hB0, hBfix, c, hcfix, hBeq, hc⟩ := hdB
  -- the same deep-unit data over the `k`-side view of the group
  have hdA' : SectionSix.IsDeepUnit k.fixingSubgroup A :=
    ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩
  have hdB' : SectionSix.IsDeepUnit k.fixingSubgroup B :=
    ⟨hB0, fun g hg => hBfix g ((hker g).mpr hg), c,
      fun g hg => hcfix g ((hker g).mpr hg), hBeq, hc⟩
  -- restricted Kummer cocycles on both sides
  have hZ1β : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqA hβ0 hAfix
  have hZ1δ : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun δ (n : AbsGalQ2))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqB hδ0 hBfix
  have hZ1kβ : (fun n : ↥k.fixingSubgroup =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqA hβ0 hdA'.2.1
  have hZ1kδ : (fun n : ↥k.fixingSubgroup =>
        Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2]))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqB hδ0 hdB'.2.1
  -- the Tier-5 vanishing over `k`, and its coboundary witness
  have hcup0 : trivialCupPairing 2 k.fixingSubgroup htriv
      (H1ofFun ↥k.fixingSubgroup fun n =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      (H1ofFun ↥k.fixingSubgroup fun n =>
        Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2])) = 0 :=
    cup_deepClasses k htriv ⟨A, β, hdA', hsqA, hβ0, rfl⟩ ⟨B, δ, hdB', hsqB, hδ0, rfl⟩
  rw [H1ofFun_of_mem hZ1kβ, H1ofFun_of_mem hZ1kδ] at hcup0
  have hB2k : cup11Fun (AddMonoidHom.mul)
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2]))
      ∈ B2 ↥k.fixingSubgroup (ZMod 2) := by
    have h0 : H2mk ↥k.fixingSubgroup (ZMod 2)
        ⟨cup11Fun (AddMonoidHom.mul)
            (fun n : ↥k.fixingSubgroup =>
              Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
            (fun n : ↥k.fixingSubgroup =>
              Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2])),
          cup11_mem_Z2 (AddMonoidHom.mul) (fun g m n => by rw [htriv, htriv, htriv])
            ⟨_, hZ1kβ⟩ ⟨_, hZ1kδ⟩⟩ = 0 := hcup0
    exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  obtain ⟨ψ, hψc, hψeq⟩ := hB2k
  -- kill `inv_K`; reduce to `B²`-membership of the `μ₂`-valued cup cocycle over `ker ρ`
  have hiv : ∀ W : H2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2),
      (tateDualityK ρ).inv W = 0 ↔ W = 0 := fun W =>
    ⟨fun h => (tateDualityK ρ).inv.injective (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  -- re-view the goal so the `H1ofFun`-terms match `hZ1β`/`hZ1δ` syntactically (the
  -- destructured form carries the definition's `GaloisGroup`-view of `↥(ker ρ)`)
  show pairingK ρ
      (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) fun n =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
      (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) fun n =>
        Kummer.kummerCocycleFun δ (n : AbsGalQ2)) = 0
  rw [H1ofFun_of_mem hZ1β, H1ofFun_of_mem hZ1δ]
  show (tateDualityK ρ).inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ)
          (H1mk _ _ ⟨_, hZ1β⟩)) (H1mk _ _ ⟨_, hZ1δ⟩)) = 0
  rw [H1congr_mk, cup11_mk_mk, hiv]
  refine (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  -- the transported witness: `μ₂-bridge ∘ ψ ∘ inclusion`
  refine AddSubgroup.mem_map.mpr
    ⟨fun n => LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker n)),
      mem_C1_iff.mpr (continuous_of_discreteTopology.comp
        ((mem_C1_iff.mp hψc).comp (continuous_kerToFixing ρ k hker))), ?_⟩
  funext p
  show p.1 • LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker p.2))
      - LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker (p.1 * p.2)))
      + LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker p.1))
    = LocalLiftingDuality.muNTwoEquiv.symm
        (Kummer.kummerCocycleFun β (p.1 : AbsGalQ2) * Kummer.kummerCocycleFun δ (p.2 : AbsGalQ2))
  rw [smul_muN_two_trivial_ker, kerToFixing_mul, ← map_sub, ← map_add]
  congr 1
  calc ψ (kerToFixing ρ k hker p.2)
      - ψ (kerToFixing ρ k hker p.1 * kerToFixing ρ k hker p.2)
      + ψ (kerToFixing ρ k hker p.1)
      = (kerToFixing ρ k hker p.1) • ψ (kerToFixing ρ k hker p.2)
        - ψ (kerToFixing ρ k hker p.1 * kerToFixing ρ k hker p.2)
        + ψ (kerToFixing ρ k hker p.1) := by rw [htriv]
    _ = Kummer.kummerCocycleFun β (p.1 : AbsGalQ2)
          * ((kerToFixing ρ k hker p.1) • Kummer.kummerCocycleFun δ (p.2 : AbsGalQ2)) :=
        congrFun hψeq (kerToFixing ρ k hker p.1, kerToFixing ρ k hker p.2)
    _ = Kummer.kummerCocycleFun β (p.1 : AbsGalQ2)
          * Kummer.kummerCocycleFun δ (p.2 : AbsGalQ2) := by rw [htriv]

/-- **Mid ⟂ deep under the K-level pairing** — `(U_e, U_{e+1}) = 1` spliced to `ker ρ`
(same witness-transport as `pairingK_deep_deep`, with the Tier-5 input
`cup_midClasses_deepClasses`).  The "easy half" of (H4)'s sharpness `Deep^⊥ = E`. -/
theorem pairingK_mid_deep (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (hη : η ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    pairingK ρ ξ η = 0 := by
  obtain ⟨A, β, hdA, hsqA, hβ0, rfl⟩ := hξ
  obtain ⟨B, δ, hdB, hsqB, hδ0, rfl⟩ := hη
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hdA
  obtain ⟨hB0, hBfix, c, hcfix, hBeq, hc⟩ := hdB
  -- the same unit data over the `k`-side view of the group
  have hdA' : IsMidUnit k.fixingSubgroup A :=
    ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩
  have hdB' : SectionSix.IsDeepUnit k.fixingSubgroup B :=
    ⟨hB0, fun g hg => hBfix g ((hker g).mpr hg), c,
      fun g hg => hcfix g ((hker g).mpr hg), hBeq, hc⟩
  -- restricted Kummer cocycles on both sides
  have hZ1β : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqA hβ0 hAfix
  have hZ1δ : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun δ (n : AbsGalQ2))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqB hδ0 hBfix
  have hZ1kβ : (fun n : ↥k.fixingSubgroup =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqA hβ0 hdA'.2.1
  have hZ1kδ : (fun n : ↥k.fixingSubgroup =>
        Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2]))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqB hδ0 hdB'.2.1
  -- the Tier-5 vanishing over `k`, and its coboundary witness
  have hcup0 : trivialCupPairing 2 k.fixingSubgroup htriv
      (H1ofFun ↥k.fixingSubgroup fun n =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      (H1ofFun ↥k.fixingSubgroup fun n =>
        Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2])) = 0 :=
    cup_midClasses_deepClasses k htriv ⟨A, β, hdA', hsqA, hβ0, rfl⟩
      ⟨B, δ, hdB', hsqB, hδ0, rfl⟩
  rw [H1ofFun_of_mem hZ1kβ, H1ofFun_of_mem hZ1kδ] at hcup0
  have hB2k : cup11Fun (AddMonoidHom.mul)
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2]))
      ∈ B2 ↥k.fixingSubgroup (ZMod 2) := by
    have h0 : H2mk ↥k.fixingSubgroup (ZMod 2)
        ⟨cup11Fun (AddMonoidHom.mul)
            (fun n : ↥k.fixingSubgroup =>
              Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
            (fun n : ↥k.fixingSubgroup =>
              Kummer.kummerCocycleFun δ (n : Kummer.GaloisGroup ℚ_[2])),
          cup11_mem_Z2 (AddMonoidHom.mul) (fun g m n => by rw [htriv, htriv, htriv])
            ⟨_, hZ1kβ⟩ ⟨_, hZ1kδ⟩⟩ = 0 := hcup0
    exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  obtain ⟨ψ, hψc, hψeq⟩ := hB2k
  -- kill `inv_K`; reduce to `B²`-membership of the `μ₂`-valued cup cocycle over `ker ρ`
  have hiv : ∀ W : H2 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (MuN 2),
      (tateDualityK ρ).inv W = 0 ↔ W = 0 := fun W =>
    ⟨fun h => (tateDualityK ρ).inv.injective (h.trans (map_zero _).symm),
      fun h => by rw [h, map_zero]⟩
  show pairingK ρ
      (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) fun n =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
      (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) fun n =>
        Kummer.kummerCocycleFun δ (n : AbsGalQ2)) = 0
  rw [H1ofFun_of_mem hZ1β, H1ofFun_of_mem hZ1δ]
  show (tateDualityK ρ).inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv (zmodMuDualEquiv_equivariant ρ)
          (H1mk _ _ ⟨_, hZ1β⟩)) (H1mk _ _ ⟨_, hZ1δ⟩)) = 0
  rw [H1congr_mk, cup11_mk_mk, hiv]
  refine (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  refine AddSubgroup.mem_map.mpr
    ⟨fun n => LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker n)),
      mem_C1_iff.mpr (continuous_of_discreteTopology.comp
        ((mem_C1_iff.mp hψc).comp (continuous_kerToFixing ρ k hker))), ?_⟩
  funext p
  show p.1 • LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker p.2))
      - LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker (p.1 * p.2)))
      + LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixing ρ k hker p.1))
    = LocalLiftingDuality.muNTwoEquiv.symm
        (Kummer.kummerCocycleFun β (p.1 : AbsGalQ2) * Kummer.kummerCocycleFun δ (p.2 : AbsGalQ2))
  rw [smul_muN_two_trivial_ker, kerToFixing_mul, ← map_sub, ← map_add]
  congr 1
  calc ψ (kerToFixing ρ k hker p.2)
      - ψ (kerToFixing ρ k hker p.1 * kerToFixing ρ k hker p.2)
      + ψ (kerToFixing ρ k hker p.1)
      = (kerToFixing ρ k hker p.1) • ψ (kerToFixing ρ k hker p.2)
        - ψ (kerToFixing ρ k hker p.1 * kerToFixing ρ k hker p.2)
        + ψ (kerToFixing ρ k hker p.1) := by rw [htriv]
    _ = Kummer.kummerCocycleFun β (p.1 : AbsGalQ2)
          * ((kerToFixing ρ k hker p.1) • Kummer.kummerCocycleFun δ (p.2 : AbsGalQ2)) :=
        congrFun hψeq (kerToFixing ρ k hker p.1, kerToFixing ρ k hker p.2)
    _ = Kummer.kummerCocycleFun β (p.1 : AbsGalQ2)
          * Kummer.kummerCocycleFun δ (p.2 : AbsGalQ2) := by rw [htriv]

/-- **The "easy half" of (H4) in `pairPerp` form**: `E = midClasses ≤ Deep^⊥` under
`pairingK`.  Sharpness (`Deep^⊥ ≤ E`) follows from this + the cardinality balance
`#Deep^⊥ = #(M ⧸ Deep) = #E` (the counting brick). -/
theorem midClassesSubgroup_le_pairPerp_pairingK
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      ≤ pairPerp (pairingK ρ)
          (deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :=
  fun _ hξ => (mem_pairPerp_iff _ _ _).mpr fun _ hη =>
    pairingK_mid_deep ρ k htriv hker hξ hη

/-- The `hiso` input of the abstract `hduality` in `pairPerp` form:
`Deep ≤ Deep^⊥` under `pairingK`. -/
theorem deepClassesSubgroup_le_pairPerp_pairingK
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      ≤ pairPerp (pairingK ρ)
          (deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :=
  fun _ hξ => (mem_pairPerp_iff _ _ _).mpr fun _ hη =>
    pairingK_deep_deep ρ k htriv hker hξ hη

end IsotropySplice

end GQ2
