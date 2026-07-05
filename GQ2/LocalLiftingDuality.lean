import GQ2.FoxHeisenberg
import GQ2.TateDuality
import GQ2.CupSymmetry
import GQ2.Foundations.Axioms
import GQ2.DualityAssembly

/-!
# P-13g: Prop 5.16 (local lifting duality) from B6 + B7

The paper's local lifting duality `prop_5_16` (§5.16) is the local Tate duality bundle **B6**
(`GQ2.tateDuality`) plus the local Euler characteristic **B7**
(`GQ2.Foundations.absGalQ2_localEulerCharacteristic`), re-expressed against the `𝔽₂`-valued
`ElemDual`/`dualEval` cup framework (T-14) used in §5.

The bridge is the `n = 2` transport `MuN 2 ≅ ZMod 2` (the second roots of unity are `{±1} ⊂ ℚ₂`,
so `G_ℚ₂` acts trivially); it carries `MuDual 2 A ≅ ElemDual A` and `muDualPairing ≅ dualEval`.
The numeric clauses then follow from B6's `card_H*_dual` + B7 Euler-characteristic counting, and the
cup-bijectivity clauses from B6's `perfect*` plus the opposite-currying-by-counting argument.
-/

namespace GQ2.LocalLiftingDuality

open ContCoh GQ2 FoxH

/-! ## The `n = 2` transport `MuN 2 ≅ ZMod 2` (trivial `G`-module). -/

/-- `#μ₂ = 2`. -/
theorem card_muN_two : Nat.card (MuN 2) = 2 :=
  (Nat.card_congr Additive.toMul).trans (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ 2)

/-- An abstract additive isomorphism `MuN 2 ≃+ ZMod 2` (order-2 group). -/
noncomputable def muNTwoEquiv : MuN 2 ≃+ ZMod 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hcyc : IsAddCyclic (MuN 2) := isAddCyclic_of_prime_card card_muN_two
  exact (card_muN_two ▸ zmodAddCyclicAddEquiv hcyc).symm

/-- **`G_ℚ₂` acts trivially on `μ₂`**: the second roots of unity are `{±1} ⊆ ℚ₂`, fixed by every
`ℚ₂`-algebra automorphism. -/
theorem smul_muN_two_trivial (g : AbsGalQ2) (x : MuN 2) : g • x = x := by
  -- `μ₂` has two elements; `g • ·` is a bijection fixing `0`, so it fixes the unique nonzero
  -- element.  Transport to `ZMod 2` (where "nonzero ⟹ = 1" is decidable).
  rcases eq_or_ne x 0 with rfl | hx
  · exact smul_zero g
  · have hgx : g • x ≠ 0 := fun h => hx (by rw [← inv_smul_smul g x, h, smul_zero])
    apply muNTwoEquiv.injective
    have hz : ∀ y : MuN 2, muNTwoEquiv y = 0 → y = 0 := fun y h =>
      muNTwoEquiv.injective (by rw [h, map_zero])
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    rw [key _ (fun h => hgx (hz _ h)), key _ (fun h => hx (hz _ h))]

/-! ## Counting: `#(V →+ 𝔽₂) = #V` for a finite `𝔽₂`-vector space. -/

/-- For a finite `2`-torsion abelian group `V` (a finite `𝔽₂`-vector space), the `𝔽₂`-dual has the
same cardinality: `#(V →+ ZMod 2) = #V`.  (Additive homs to `𝔽₂` are `𝔽₂`-linear, and a
finite-dimensional space is isomorphic to its dual.) -/
theorem card_addHom_zmod2 {V : Type*} [AddCommGroup V] [Finite V] (hV₂ : ∀ v : V, v + v = 0) :
    Nat.card (V →+ ZMod 2) = Nat.card V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV₂ v)
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have e1 : (V →+ ZMod 2) ≃+ Module.Dual (ZMod 2) V := AddMonoidHom.toZModLinearMapEquiv 2
  obtain ⟨e2⟩ :=
    (Basis.linearEquiv_dual_iff_finiteDimensional (K := ZMod 2) (V := V)).mpr inferInstance
  rw [Nat.card_congr e1.toEquiv]
  exact (Nat.card_congr e2.toEquiv).symm

/-- **Separation of points by `𝔽₂`-functionals**: a nonzero vector in a finite `𝔽₂`-vector space
is detected by some additive functional to `𝔽₂`.  (Extend the singleton to a basis; the
corresponding coordinate functional is nonzero on it.) -/
theorem exists_addHom_ne_zero {V : Type*} [AddCommGroup V] [Finite V]
    (hV₂ : ∀ v : V, v + v = 0) {v : V} (hv : v ≠ 0) : ∃ f : V →+ ZMod 2, f v ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV₂ v)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  let b := Module.Free.chooseBasis (ZMod 2) V
  by_contra h
  push_neg at h
  refine hv (b.forall_coord_eq_zero_iff.mp fun i => ?_)
  simpa using h (b.coord i).toAddMonoidHom

/-- **Two-torsion of `H¹`** for a `2`-torsion coefficient module. -/
theorem H1_two_torsion_gen {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]
    (hM₂ : ∀ m : M, m + m = 0) (z : H1 AbsGalQ2 M) : z + z = 0 := by
  obtain ⟨w, rfl⟩ := H1mk_surjective (G := AbsGalQ2) (M := M) z
  rw [← map_add, show (w + w : ↥(Z1 AbsGalQ2 M)) = 0 from Subtype.ext (funext fun g => hM₂ _),
    map_zero]

/-- **Two-torsion of `H²`** for a `2`-torsion coefficient module. -/
theorem H2_two_torsion_gen {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]
    (hM₂ : ∀ m : M, m + m = 0) (z : H2 AbsGalQ2 M) : z + z = 0 := by
  obtain ⟨w, rfl⟩ := H2mk_surjective (G := AbsGalQ2) (M := M) z
  rw [← map_add, show (w + w : ↥(Z2 AbsGalQ2 M)) = 0 from Subtype.ext (funext fun p => hM₂ _),
    map_zero]

/-- **Opposite currying by counting** (B6's flagged deviation, discharged via B7 finiteness): for a
biadditive cup map `Φ : V →+ W →+ H` with `H ≃+ 𝔽₂`, if `#V = #W` (both finite `2`-torsion) and the
`τ`-twisted opposite currying `f ↦ (∃ w, ∀ c, τ(Φ c w) = f c)` is surjective onto `V →+ 𝔽₂`, then
`Φ` is a perfect pairing: `c ↦ Φ c` is bijective onto `W →+ H`. -/
theorem bijective_cup {V W H : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup H]
    [Finite V] [Finite W] [Finite H] (hV₂ : ∀ v : V, v + v = 0) (hW₂ : ∀ w : W, w + w = 0)
    (hcardVW : Nat.card V = Nat.card W) (τ : H ≃+ ZMod 2) (Φ : V →+ W →+ H)
    (hsurj : ∀ f : V →+ ZMod 2, ∃ w : W, ∀ c : V, τ (Φ c w) = f c) :
    Function.Bijective (⇑Φ) := by
  have hinj : Function.Injective (⇑Φ) := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    by_contra hcne
    obtain ⟨f, hf⟩ := exists_addHom_ne_zero hV₂ hcne
    obtain ⟨w, hw⟩ := hsurj f
    apply hf
    have hcw := hw c
    rw [hc] at hcw
    simpa using hcw.symm
  haveI : Finite (W →+ H) := Finite.of_injective _ (DFunLike.coe_injective (F := W →+ H))
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (W →+ H) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card ⇑Φ).mpr ⟨hinj, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
    show Nat.card (W →+ H) = Nat.card (W →+ ZMod 2) from Nat.card_congr
      { toFun := fun h => τ.toAddMonoidHom.comp h
        invFun := fun h => τ.symm.toAddMonoidHom.comp h
        left_inv := fun h => by ext w; simp
        right_inv := fun h => by ext w; simp },
    card_addHom_zmod2 hW₂, hcardVW]

/-! ## Degree-0 transport `#H⁰(MuDual 2 A) = #fixedPts C (ElemDual A)`.

The `μ₂`-dual and the `𝔽₂`-dual agree through `muNTwoEquiv`, and the `G_ℚ₂`-conjugation action on
`MuDual 2 A` matches the `C`-contragredient action on `ElemDual A` through `ρ` (`hcomp` + trivial
action on `μ₂`/`𝔽₂`).  So the invariants correspond. -/

section Bridge

variable {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  {ρ : ContinuousMonoidHom AbsGalQ2 C} (hρ : Function.Surjective ρ)
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A] [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
  (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)

/-- Post-composition with `muNTwoEquiv` sends the `μ₂`-dual to the `𝔽₂`-dual. -/
noncomputable def dualMap (φ : MuDual 2 A) : ElemDual A :=
  muNTwoEquiv.toAddMonoidHom.comp (φ : A →+ MuN 2)

@[simp] theorem dualMap_apply (φ : MuDual 2 A) (a : A) : dualMap φ a = muNTwoEquiv (φ a) := rfl

/-- Inverse direction. -/
noncomputable def dualMapInv (lam : ElemDual A) : MuDual 2 A :=
  muNTwoEquiv.symm.toAddMonoidHom.comp (lam : A →+ ZMod 2)

@[simp] theorem dualMapInv_apply (lam : ElemDual A) (a : A) :
    dualMapInv lam a = muNTwoEquiv.symm (lam a) := rfl

/-- The `μ₂`-dual and the `𝔽₂`-dual are additively isomorphic (post-composition with
`muNTwoEquiv`).  Not `G`-equivariant on its own, but a bijection — enough for cardinalities. -/
noncomputable def dualAddEquiv : MuDual 2 A ≃+ ElemDual A where
  toFun := dualMap
  invFun := dualMapInv
  left_inv φ := DFunLike.ext _ _ fun a => muNTwoEquiv.symm_apply_apply _
  right_inv lam := DFunLike.ext _ _ fun a => muNTwoEquiv.apply_symm_apply _
  map_add' φ ψ := DFunLike.ext _ _ fun a => by
    simp only [dualMap_apply, MuDual.add_apply, ElemDual.add_apply, map_add]

@[simp] theorem dualAddEquiv_apply (φ : MuDual 2 A) (a : A) :
    dualAddEquiv φ a = muNTwoEquiv (φ a) := rfl

include hρ hcomp in
/-- The `G_ℚ₂`-invariance of `φ` (a `μ₂`-dual) rewritten pointwise, then transported to `C`-orbits
via `ρ`: `φ (c • a) = φ a` for every `c : C`. -/
theorem muDual_inv_pointwise {φ : MuDual 2 A} (hφ : ∀ γ : AbsGalQ2, γ • φ = φ) (c : C) (a : A) :
    φ (c • a) = φ a := by
  obtain ⟨γ, hγ⟩ := hρ c
  have h := DFunLike.congr_fun (hφ γ) (c • a)
  rw [muDual_smul_apply, smul_muN_two_trivial] at h
  -- h : φ (γ⁻¹ • (c • a)) = φ (c • a)
  have hid : γ⁻¹ • (c • a) = a := by rw [hcomp, ← hγ, map_inv, inv_smul_smul]
  rw [hid] at h
  exact h.symm

/-- The `C`-invariance of a `𝔽₂`-dual `lam`, rewritten pointwise: `lam (c • a) = lam a`. -/
theorem elemDual_fixed_pointwise {lam : ElemDual A} (hlam : ∀ c : C, c • lam = lam) (c : C)
    (a : A) : lam (c • a) = lam a := by
  have h := DFunLike.congr_fun (hlam c⁻¹) a
  rwa [ElemDual.smul_apply, inv_inv] at h

include hρ hcomp in
/-- **Degree-0 transport**: the `G_ℚ₂`-invariants of the `μ₂`-dual biject with the `C`-invariants
of the `𝔽₂`-dual (via post-composition with `muNTwoEquiv`). -/
theorem card_H0_muDual_eq_fixedPts :
    Nat.card (H0 AbsGalQ2 (MuDual 2 A)) = Nat.card (fixedPts C (ElemDual A)) := by
  refine Nat.card_congr ⟨fun φ => ⟨dualMap φ.1, fun c => ?_⟩,
    fun lam => ⟨dualMapInv lam.1, fun γ => ?_⟩, fun φ => ?_, fun lam => ?_⟩
  · refine DFunLike.ext _ _ fun a => ?_
    rw [ElemDual.smul_apply, dualMap_apply, dualMap_apply,
      muDual_inv_pointwise hρ hcomp φ.2 c⁻¹ a]
  · refine DFunLike.ext _ _ fun a => ?_
    rw [muDual_smul_apply, smul_muN_two_trivial, dualMapInv_apply, dualMapInv_apply]
    congr 1
    rw [hcomp, elemDual_fixed_pointwise lam.2 (ρ γ⁻¹) a]
  · exact Subtype.ext (DFunLike.ext _ _ fun a => muNTwoEquiv.symm_apply_apply _)
  · exact Subtype.ext (DFunLike.ext _ _ fun a => muNTwoEquiv.apply_symm_apply _)

/-- `H²(A)` is `2`-torsion when `A` is (it is a subquotient of `𝔽₂`-valued cochains). -/
theorem H2_two_torsion (hA₂ : ∀ a : A, a + a = 0) (z : H2 AbsGalQ2 A) : z + z = 0 := by
  obtain ⟨w, rfl⟩ := H2mk_surjective (G := AbsGalQ2) (M := A) z
  rw [← map_add, show (w + w : ↥(Z2 AbsGalQ2 A)) = 0 from Subtype.ext (funext fun p => hA₂ _),
    map_zero]

include hρ hcomp in
/-- **Clause (i)**: `#H²(A) = #fixedPts C (ElemDual A)` — B6's `(0,2)` duality (`H⁰(A′) ≅
Hom(H²(A), 𝔽₂)`), the self-dual count `#Hom(H²(A),𝔽₂) = #H²(A)`, and the degree-0 transport. -/
theorem card_H2_eq_fixedPts (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (H2 AbsGalQ2 A) = Nat.card (fixedPts C (ElemDual A)) := by
  haveI : NeZero 2 := ⟨two_ne_zero⟩
  haveI : Finite (H2 AbsGalQ2 A) := (Foundations.absGalQ2_localEulerCharacteristic A).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  calc Nat.card (H2 AbsGalQ2 A)
      = Nat.card (H2 AbsGalQ2 A →+ ZMod 2) := (card_addHom_zmod2 (H2_two_torsion hA₂)).symm
    _ = Nat.card (H0 AbsGalQ2 (MuDual 2 A)) := ((tateDuality 2).card_H0_dual A htor).symm
    _ = Nat.card (fixedPts C (ElemDual A)) := card_H0_muDual_eq_fixedPts hρ hcomp

/-! ### Structural cardinalities for clause (ii). -/

/-- `ker(d⁰) = H⁰`. -/
theorem dZero_ker_eq_H0 : (dZero AbsGalQ2 A).ker = H0 AbsGalQ2 A := by
  ext m
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h g
    have hg : (dZero AbsGalQ2 A) m g = 0 := by rw [h]; rfl
    rwa [show (dZero AbsGalQ2 A) m g = g • m - m from rfl, sub_eq_zero] at hg
  · intro h
    ext g
    rw [show (dZero AbsGalQ2 A) m g = g • m - m from rfl, h g, sub_self]; rfl

/-- `#A = #B¹ · #H⁰` (first isomorphism theorem for `d⁰`: `B¹ = im d⁰ ≅ A/ker d⁰ = A/H⁰`). -/
theorem card_A_eq_B1_mul_H0 :
    Nat.card A = Nat.card (B1 AbsGalQ2 A) * Nat.card (H0 AbsGalQ2 A) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (H0 AbsGalQ2 A)
  rw [show Nat.card (A ⧸ H0 AbsGalQ2 A) = Nat.card (B1 AbsGalQ2 A) from ?_] at h
  · exact h
  · rw [← dZero_ker_eq_H0]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (dZero AbsGalQ2 A)).toEquiv

/-- `#Z¹ = #H¹ · #B¹` (Lagrange on `H¹ = Z¹/B¹`). -/
theorem card_Z1_eq_H1_mul_B1 :
    Nat.card (Z1 AbsGalQ2 A) = Nat.card (H1 AbsGalQ2 A) * Nat.card (B1 AbsGalQ2 A) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((B1 AbsGalQ2 A).addSubgroupOf (Z1 AbsGalQ2 A))
  rwa [Nat.card_congr
    (AddSubgroup.addSubgroupOfEquivOfLe (B1_le_Z1 (G := AbsGalQ2) (M := A))).toEquiv] at h

/-- `2 ^ v₂(#A) = #A` for finite `2`-torsion `A` (a finite `𝔽₂`-vector space). -/
theorem pow_padicValNat_card (hA₂ : ∀ a : A, a + a = 0) :
    2 ^ padicValNat 2 (Nat.card A) = Nat.card A := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun a => by rw [two_nsmul]; exact hA₂ a)
  rw [← FiniteField.pow_finrank_eq_natCard 2 A, padicValNat.prime_pow]

include hρ hcomp in
/-- **Clause (ii)**: `#Z¹(A) = #A² · #fixedPts C (ElemDual A)` — from `#Z¹ = #H¹·#B¹`, the B7 Euler
characteristic `#H¹ = #H⁰·#H²·#A`, `#A = #B¹·#H⁰`, and clause (i). -/
theorem card_Z1_eq (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (Z1 AbsGalQ2 A)
      = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A)) := by
  have hEuler := (Foundations.absGalQ2_localEulerCharacteristic A).2.2.2
  rw [card_Z1_eq_H1_mul_B1, hEuler, pow_padicValNat_card hA₂, card_H2_eq_fixedPts hρ hcomp hA₂,
    pow_two,
    show Nat.card (H0 AbsGalQ2 A) * Nat.card (fixedPts C (ElemDual A)) * Nat.card A
        * Nat.card (B1 AbsGalQ2 A)
      = Nat.card (fixedPts C (ElemDual A)) * Nat.card A
          * (Nat.card (B1 AbsGalQ2 A) * Nat.card (H0 AbsGalQ2 A)) from by ring,
    ← card_A_eq_B1_mul_H0]
  ring

end Bridge

/-! ## Clause (iii): `#H²(𝔽₂) = 2`. -/

/-- **Clause (iii)**: `#H²(G_ℚ₂, 𝔽₂) = 2`.  With `G_ℚ₂` acting trivially the `μ₂`-dual invariants are
everything, so `#H⁰(MuDual 2 𝔽₂) = #(𝔽₂ →+ μ₂) = #(𝔽₂ →+ 𝔽₂) = 2`; B6's `(0,2)` duality then pins
`#H²(𝔽₂)`. -/
theorem card_H2_zmod2_eq_two [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m) :
    Nat.card (H2 AbsGalQ2 (ZMod 2)) = 2 := by
  haveI : NeZero 2 := ⟨two_ne_zero⟩
  haveI : Finite (H2 AbsGalQ2 (ZMod 2)) :=
    (Foundations.absGalQ2_localEulerCharacteristic (ZMod 2)).2.2.1
  have hZtor : ∀ m : ZMod 2, m + m = 0 := fun m => CharTwo.add_self_eq_zero m
  have htor : ∀ x : ZMod 2, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hZtor x
  have hall : H0 AbsGalQ2 (MuDual 2 (ZMod 2)) = ⊤ := by
    ext φ
    simp only [AddSubgroup.mem_top, iff_true]
    intro γ
    refine DFunLike.ext _ _ fun m => ?_
    rw [muDual_smul_apply, smul_muN_two_trivial, htriv]
  calc Nat.card (H2 AbsGalQ2 (ZMod 2))
      = Nat.card (H2 AbsGalQ2 (ZMod 2) →+ ZMod 2) :=
        (card_addHom_zmod2 (H2_two_torsion hZtor)).symm
    _ = Nat.card (H0 AbsGalQ2 (MuDual 2 (ZMod 2))) :=
        ((tateDuality 2).card_H0_dual (ZMod 2) htor).symm
    _ = Nat.card (MuDual 2 (ZMod 2)) := by
        rw [hall]; exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
    _ = Nat.card (ElemDual (ZMod 2)) := Nat.card_congr dualAddEquiv.toEquiv
    _ = Nat.card ((ZMod 2) →+ ZMod 2) := rfl
    _ = Nat.card (ZMod 2) := card_addHom_zmod2 hZtor
    _ = 2 := Nat.card_zmod 2

/-! ## Cup clauses (iv)–(vi): perfectness of the evaluation cup pairings.

B6's `perfect02/11/20` pair with the `μ₂`-dual `MuDual 2 A` in the **left** slot; the paper's
`prop_5_16` puts `A` (resp. `ElemDual A`) in the left slot — the transpose.  The bridge is
graded-commutativity (`GQ2.ContCoh.cup11_comm`, char 2 so the sign is `+1`) plus the
`G`-equivariant coefficient transport `dualAddEquiv : MuDual 2 A ≃+ ElemDual A` (from `hpair`),
carried across `H¹`/`H²`/`H⁰` by `H1congr`/`H2congr`/`H0congr` and across the `μ₂`/`𝔽₂` target by
`muNTwoEquiv`.  Perfectness of the transpose then follows by the opposite-currying count
`bijective_cup` (B7 supplies the finiteness). -/

section CupClauses

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]

/-- `muNTwoEquiv : μ₂ ≃+ 𝔽₂` is `G`-equivariant (both actions are trivial). -/
theorem muNTwoEquiv_equivariant (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m) :
    ∀ (g : AbsGalQ2) (m : MuN 2), muNTwoEquiv (g • m) = g • muNTwoEquiv m :=
  fun g m => by rw [smul_muN_two_trivial]; exact (htriv g (muNTwoEquiv m)).symm

/-- `dualAddEquiv : MuDual 2 A ≃+ ElemDual A` is `G`-equivariant: the conjugation action on the
`μ₂`-dual matches the contragredient action on the `𝔽₂`-dual, which `hpair` pins down. -/
theorem edEquivariant
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam)
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m) :
    ∀ (g : AbsGalQ2) (φ : MuDual 2 A), dualAddEquiv (g • φ) = g • dualAddEquiv φ := by
  intro g φ
  refine DFunLike.ext _ _ fun a => ?_
  have hEDsmul : (g • dualAddEquiv φ) a = (dualAddEquiv φ) (g⁻¹ • a) := by
    have h := hpair g (g⁻¹ • a) (dualAddEquiv φ)
    rw [smul_inv_smul, dualEval_apply, dualEval_apply, htriv] at h
    exact h
  rw [hEDsmul]
  simp only [dualAddEquiv_apply, muDual_smul_apply, smul_muN_two_trivial]

/-- `ElemDual A` is `2`-torsion (its values lie in `𝔽₂`). -/
theorem elemDual_two_torsion (lam : ElemDual A) : lam + lam = 0 :=
  DFunLike.ext _ _ fun a => by
    rw [ElemDual.add_apply, ElemDual.zero_apply]
    exact CharTwo.add_self_eq_zero (lam a)

/-- **Clause (iv)**: the `(1,1)` evaluation cup `c ↦ (d ↦ c ∪ d) : H¹(A) → Hom(H¹(A′), H²(𝔽₂))` is
bijective — the transpose of B6's `perfect11`, discharged by graded-commutativity + counting. -/
theorem bijective_cup11_dualEval
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Function.Bijective (fun c : H1 AbsGalQ2 A => cup11 (dualEval A) hpair c) := by
  haveI : NeZero 2 := ⟨two_ne_zero⟩
  haveI : Finite (H1 AbsGalQ2 A) := (Foundations.absGalQ2_localEulerCharacteristic A).2.1
  haveI : Finite (H1 AbsGalQ2 (ElemDual A)) :=
    (Foundations.absGalQ2_localEulerCharacteristic (ElemDual A)).2.1
  haveI : Finite (H2 AbsGalQ2 (ZMod 2)) :=
    (Foundations.absGalQ2_localEulerCharacteristic (ZMod 2)).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  have hμNe := muNTwoEquiv_equivariant htriv
  have heD := edEquivariant hpair htriv
  let τ : H2 AbsGalQ2 (ZMod 2) ≃+ ZMod 2 :=
    (H2congr muNTwoEquiv hμNe).symm.trans (tateDuality 2).inv
  have hτapp : ∀ X, τ (H2congr muNTwoEquiv hμNe X) = (tateDuality 2).inv X := fun X => by
    show ((H2congr muNTwoEquiv hμNe).symm.trans (tateDuality 2).inv)
      (H2congr muNTwoEquiv hμNe X) = _
    rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  have key : ∀ (c : H1 AbsGalQ2 A) (d'' : H1 AbsGalQ2 (MuDual 2 A)),
      τ (cup11 (dualEval A) hpair c (H1congr dualAddEquiv heD d''))
        = (tateDuality 2).inv
            (cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' c) := by
    intro c d''
    have hgc : cup11 (dualEval A) hpair c (H1congr dualAddEquiv heD d'')
        = H2congr muNTwoEquiv hμNe
            (cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' c) := by
      rw [cup11_comm (dualEval A) hpair (fun p => CharTwo.add_self_eq_zero p) c
        (H1congr dualAddEquiv heD d'')]
      obtain ⟨a', rfl⟩ := H1mk_surjective (G := AbsGalQ2) (M := MuDual 2 A) d''
      obtain ⟨b, rfl⟩ := H1mk_surjective (G := AbsGalQ2) (M := A) c
      rw [H1congr_mk, cup11_mk_mk, cup11_mk_mk, H2congr_mk]
      congr 1
    rw [hgc, hτapp]
  have hsurj : ∀ f : H1 AbsGalQ2 A →+ ZMod 2, ∃ w : H1 AbsGalQ2 (ElemDual A),
      ∀ c, τ (cup11 (dualEval A) hpair c w) = f c := by
    intro f
    obtain ⟨d'', hd''⟩ := ((tateDuality 2).perfect11 A htor).2 f
    refine ⟨H1congr dualAddEquiv heD d'', fun c => ?_⟩
    rw [key c d'']
    exact DFunLike.congr_fun hd'' c
  exact bijective_cup (H1_two_torsion_gen hA₂) (H1_two_torsion_gen elemDual_two_torsion)
    (by rw [← Nat.card_congr (H1congr dualAddEquiv heD).toEquiv,
      (tateDuality 2).card_H1_dual A htor, card_addHom_zmod2 (H1_two_torsion_gen hA₂)])
    τ (cup11 (dualEval A) hpair) hsurj

/-- **Clause (v)**: the `(0,2)` evaluation cup `c ↦ (d ↦ c ∪ d) : H⁰(A) → Hom(H²(A′), H²(𝔽₂))` is
bijective — the transpose of B6's `perfect20` (`cup02 = cup20ᵀ` swaps the degree pair). -/
theorem bijective_cup02_dualEval
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Function.Bijective (fun c : ↥(H0 AbsGalQ2 A) => cup02 (dualEval A) hpair c) := by
  haveI : NeZero 2 := ⟨two_ne_zero⟩
  haveI : Finite (H2 AbsGalQ2 (ElemDual A)) :=
    (Foundations.absGalQ2_localEulerCharacteristic (ElemDual A)).2.2.1
  haveI : Finite (H2 AbsGalQ2 (ZMod 2)) :=
    (Foundations.absGalQ2_localEulerCharacteristic (ZMod 2)).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  have h0₂ : ∀ v : ↥(H0 AbsGalQ2 A), v + v = 0 := fun v => Subtype.ext (by simpa using hA₂ v.1)
  have hμNe := muNTwoEquiv_equivariant htriv
  have heD := edEquivariant hpair htriv
  let τ : H2 AbsGalQ2 (ZMod 2) ≃+ ZMod 2 :=
    (H2congr muNTwoEquiv hμNe).symm.trans (tateDuality 2).inv
  have hτapp : ∀ X, τ (H2congr muNTwoEquiv hμNe X) = (tateDuality 2).inv X := fun X => by
    show ((H2congr muNTwoEquiv hμNe).symm.trans (tateDuality 2).inv)
      (H2congr muNTwoEquiv hμNe X) = _
    rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  have key : ∀ (c : ↥(H0 AbsGalQ2 A)) (d'' : H2 AbsGalQ2 (MuDual 2 A)),
      τ (cup02 (dualEval A) hpair c (H2congr dualAddEquiv heD d''))
        = (tateDuality 2).inv
            (cup20 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' c) := by
    intro c d''
    have hgc : cup02 (dualEval A) hpair c (H2congr dualAddEquiv heD d'')
        = H2congr muNTwoEquiv hμNe
            (cup20 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' c) := by
      rw [cup02_eq_cup20_flip (dualEval A) hpair c (H2congr dualAddEquiv heD d'')]
      obtain ⟨a', rfl⟩ := H2mk_surjective (G := AbsGalQ2) (M := MuDual 2 A) d''
      rw [H2congr_mk, cup20_mk_mk, cup20_mk_mk, H2congr_mk]
      congr 1
    rw [hgc, hτapp]
  have hsurj : ∀ f : ↥(H0 AbsGalQ2 A) →+ ZMod 2, ∃ w : H2 AbsGalQ2 (ElemDual A),
      ∀ c, τ (cup02 (dualEval A) hpair c w) = f c := by
    intro f
    obtain ⟨d'', hd''⟩ := ((tateDuality 2).perfect20 A htor).2 f
    refine ⟨H2congr dualAddEquiv heD d'', fun c => ?_⟩
    rw [key c d'']
    exact DFunLike.congr_fun hd'' c
  exact bijective_cup h0₂ (H2_two_torsion_gen elemDual_two_torsion)
    (by rw [← Nat.card_congr (H2congr dualAddEquiv heD).toEquiv,
      (tateDuality 2).card_H2_dual A htor, card_addHom_zmod2 h0₂])
    τ (cup02 (dualEval A) hpair) hsurj

/-- **Clause (vi)**: the `(2,0)` evaluation cup `c ↦ (d ↦ c ∪ d) : H²(A) → Hom(H⁰(A′), H²(𝔽₂))` is
bijective — the transpose of B6's `perfect02` (`cup20 = cup02ᵀ` swaps the degree pair). -/
theorem bijective_cup20_dualEval
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Function.Bijective (fun c : H2 AbsGalQ2 A => cup20 (dualEval A) hpair c) := by
  haveI : NeZero 2 := ⟨two_ne_zero⟩
  haveI : Finite (H2 AbsGalQ2 A) := (Foundations.absGalQ2_localEulerCharacteristic A).2.2.1
  haveI : Finite (H2 AbsGalQ2 (ZMod 2)) :=
    (Foundations.absGalQ2_localEulerCharacteristic (ZMod 2)).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  have hED0₂ : ∀ w : ↥(H0 AbsGalQ2 (ElemDual A)), w + w = 0 :=
    fun w => Subtype.ext (by simpa using elemDual_two_torsion w.1)
  have hμNe := muNTwoEquiv_equivariant htriv
  have heD := edEquivariant hpair htriv
  let τ : H2 AbsGalQ2 (ZMod 2) ≃+ ZMod 2 :=
    (H2congr muNTwoEquiv hμNe).symm.trans (tateDuality 2).inv
  have hτapp : ∀ X, τ (H2congr muNTwoEquiv hμNe X) = (tateDuality 2).inv X := fun X => by
    show ((H2congr muNTwoEquiv hμNe).symm.trans (tateDuality 2).inv)
      (H2congr muNTwoEquiv hμNe X) = _
    rw [AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  have key : ∀ (c : H2 AbsGalQ2 A) (d'' : ↥(H0 AbsGalQ2 (MuDual 2 A))),
      τ (cup20 (dualEval A) hpair c (H0congr dualAddEquiv heD d''))
        = (tateDuality 2).inv
            (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' c) := by
    intro c d''
    have hgc : cup20 (dualEval A) hpair c (H0congr dualAddEquiv heD d'')
        = H2congr muNTwoEquiv hμNe
            (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A) d'' c) := by
      rw [cup20_eq_cup02_flip (dualEval A) hpair c (H0congr dualAddEquiv heD d'')]
      obtain ⟨b, rfl⟩ := H2mk_surjective (G := AbsGalQ2) (M := A) c
      rw [cup02_mk_mk, cup02_mk_mk, H2congr_mk]
      congr 1
    rw [hgc, hτapp]
  have hsurj : ∀ f : H2 AbsGalQ2 A →+ ZMod 2, ∃ w : ↥(H0 AbsGalQ2 (ElemDual A)),
      ∀ c, τ (cup20 (dualEval A) hpair c w) = f c := by
    intro f
    obtain ⟨d'', hd''⟩ := ((tateDuality 2).perfect02 A htor).2 f
    refine ⟨H0congr dualAddEquiv heD d'', fun c => ?_⟩
    rw [key c d'']
    exact DFunLike.congr_fun hd'' c
  exact bijective_cup (H2_two_torsion_gen hA₂) hED0₂
    (by rw [← Nat.card_congr (H0congr dualAddEquiv heD).toEquiv,
      (tateDuality 2).card_H0_dual A htor, card_addHom_zmod2 (H2_two_torsion_gen hA₂)])
    τ (cup20 (dualEval A) hpair) hsurj

end CupClauses

/-! ## Assembly: the full `prop_5_16` conclusion. -/

/-- **`prop_5_16` (local lifting duality), fully assembled** — all six clauses, stated with the
paper's exact signature (`GQ2.FoxH.prop_5_16`).  This is the complete P-13g deliverable: clauses
(i)–(iii) are the numeric/Euler-characteristic content, (iv)–(vi) the cup-perfectness content.

`GQ2.FoxH.prop_5_16` itself cannot be spliced to `exact` this in place, because `FoxHeisenberg`
(where it is declared) would then have to import this file, which already imports `FoxHeisenberg`
(for `ElemDual`/`dualEval`) — an import cycle.  Discharging the sorry there needs the statement
relocated out of the co-owned `FoxHeisenberg.lean` (a coordinated move, not a one-line splice). -/
theorem prop_5_16_bundle {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 AbsGalQ2 A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 AbsGalQ2 A) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 AbsGalQ2 (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 AbsGalQ2 A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H0 AbsGalQ2 A => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 AbsGalQ2 A => cup20 (dualEval A) hpair c) :=
  ⟨card_H2_eq_fixedPts hρ hcomp hA₂, card_Z1_eq hρ hcomp hA₂, card_H2_zmod2_eq_two htriv,
    bijective_cup11_dualEval hA₂ htriv hpair, bijective_cup02_dualEval hA₂ htriv hpair,
    bijective_cup20_dualEval hA₂ htriv hpair⟩

end GQ2.LocalLiftingDuality

/-! ## §5.16–§5.17, relocated from `GQ2/FoxHeisenberg.lean`.

`prop_5_16` and `cor_5_17_card` are declared here (in their original `GQ2.FoxH` namespace, so
qualified names are unchanged) rather than in `FoxHeisenberg.lean`, because their proofs need B6
(`GQ2.tateDuality`) and the `𝔽₂`-cup transport — infrastructure in files that import
`FoxHeisenberg`, so proving them there would be an import cycle. -/

namespace GQ2.FoxH

open GQ2.ContCoh GQ2.LocalLiftingDuality

/-- **Prop 5.16 (local lifting duality)**: for a finite elementary module with `G_ℚ₂`-action
factoring through `ρ : G_ℚ₂ ↠ C`, the display-(57) numerics hold and the T-04 evaluation-cup
pairings are perfect in all three degree pairs (T-14 phrasing; the clause `#H²(𝔽₂) = 2`
certifies the target line).  The two-actions setup follows T-02's compatible-pair pattern:
separate `C`- and `G_ℚ₂`-actions related pointwise through `ρ` — no double instance on one
type.

*Status*: **PROVED** (P-13g), via `GQ2.LocalLiftingDuality.prop_5_16_bundle`; this is where
axioms B6 and B7 enter (App. D row).  Relocated out of `GQ2/FoxHeisenberg.lean` to break an
import cycle (the `𝔽₂`-cup/B6 infrastructure imports that file). -/
theorem prop_5_16 {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 AbsGalQ2 A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 AbsGalQ2 A) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 AbsGalQ2 (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 AbsGalQ2 A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H0 AbsGalQ2 A => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 AbsGalQ2 A => cup20 (dualEval A) hpair c) :=
  prop_5_16_bundle ρ hρ hcomp hA₂ hcompD htriv hpair

/-- **Corollary 5.17, numerics half** (proved wiring): the obstruction-space and
unobstructed-lift-multiplicity cardinalities agree for the two sources.  (The
adjoint-boundary identity (58) is deferred: it needs connecting-map infrastructure in both
theories — see the module docstring.) -/
theorem cor_5_17_card {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hcore : t.Pro2Core)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Nat.card (Z1w (A := A) t) = Nat.card (ContCoh.Z1 AbsGalQ2 A) ∧
    Nat.card (H2w (A := A) t) = Nat.card (ContCoh.H2 AbsGalQ2 A) := by
  obtain ⟨hc2, hc1, -⟩ := prop_5_15 t ht hw hgen (A := A) hA₂ hcore
  obtain ⟨hl2, hl1, -⟩ := prop_5_16 ρ hρ (A := A) hcomp hA₂ hcompD htriv hpair
  exact ⟨hc1.trans hl1.symm, hc2.trans hl2.symm⟩

end GQ2.FoxH
