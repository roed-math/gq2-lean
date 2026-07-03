import Mathlib
import GQ2.CupProduct
import GQ2.MuN

/-!
# B6: local Tate duality for `ℚ₂` — the dual module and the duality bundle  (ticket T-14)

This file provides the *statement infrastructure* for the paper's **local Tate duality** leaf
(**B6**): the `μₙ`-dual of a finite discrete `G_ℚ₂`-module, the evaluation cup pairing, and the
bundle `TateDuality n` packaging the invariant map `inv : H²(G_ℚ₂, μₙ) ≃+ ℤ/n` together with
perfectness of the cup pairing in the three degree pairs.  The axiom itself
(`GQ2.tateDuality : ∀ n [NeZero n], TateDuality n`) lives in `GQ2/Foundations/Axioms.lean`
(T-19 rule); everything here is definitions plus axiom-free, bundle-parametrized stress tests.

## Design decisions (the ticket's 🔴 items, resolved)

* **Per-`n` form, not the colimit.**  The literature states duality with `μ = ⋃ₙ μₙ` and
  `H²(G_k, μ) ≅ ℚ/ℤ`.  We state it per `n` (for `n`-torsion modules), which suffices for the
  paper (only `n = 2` and `𝔽₂`-modules are used, §§5–8) and avoids colimits of modules.
  **Deviation flagged**: cross-`n` compatibility of the `inv`'s (restriction along
  `μₙ ⊆ μₙₘ`) is *not* asserted.
* **Pontryagin-dual encoding.**  For an `n`-torsion finite abelian `A`,
  `Hom(A, ℚ/ℤ) = Hom(A, ⅟n·ℤ/ℤ) ≅ Hom(A, ℤ/n)`; so "the dual of `H`" is encoded as the plain
  hom-group `H →+ ZMod n`, and no `AddCircle`/`ℚ⧸ℤ` is needed.
* **The dual module** `M′ = Hom(M, μₙ)` is `MuDual n M`, a **`def`** (not `abbrev`) type
  synonym of `M →+ MuN n`: Mathlib has a *codomain-only* action instance on `A →+ B`
  (`DistribMulAction M (A →+ B)`, `Mathlib/Algebra/GroupWithZero/Action/Hom.lean`), so the
  Galois **conjugation** action `(g • φ)(m) = g • φ(g⁻¹ • m)` must live on a synonym to avoid
  an instance diamond.  Continuity of the conjugation action is via open stabilizers
  (`continuousSMul_iff_stabilizer_isOpen` + T-01's `isOpen_iInf_stabilizer`: the joint action
  kernel on `M` and `μₙ` is open and stabilizes every `φ`).
* **Perfectness, single currying.**  For each degree pair — `(0,2)`, `(1,1)`, `(2,0)`, i.e.
  exactly T-04's three cup shapes with `M′` in the left slot and the evaluation pairing
  `muDualPairing : M′ →+ M →+ μₙ` — the clause asserts that
  `x ↦ inv ∘ (x ∪ ·) : Hⁱ(M′) → (H^{2−i}(M) →+ ZMod n)` is **bijective**.
  **Deviation flagged**: the opposite currying (`H^{2−i}(M) → Hom(Hⁱ(M′), ℤ/n)`) is not
  asserted; for finite cohomology groups (B7) it follows by counting, and the paper consumes
  only the stated direction.
* **No normalization of `inv`.**  The literature pins `inv` down (via the valuation map and
  Frobenius); the bundle only asserts *existence* of an `inv` making the pairings perfect,
  which is what the paper's dimension counts use.  The explicit `n = 2` cup values enter
  through B7′ (the Hilbert symbol), not through `inv`.  **Deviation flagged** for review.

## Citations

**NSW, Ch. VII §7.2, Theorem (7.2.6)** (local Tate duality: the cup pairing
`Hⁱ(G_k, M′) × H^{2−i}(G_k, M) → H²(G_k, μ) = ℚ/ℤ` is non-degenerate for finite `M`);
Serre, *Galois Cohomology* II §5.2, Theorem 2; Milne, *Arithmetic Duality Theorems*, I.2.3.
Paper: §§5–8 (dimension counts over `𝔽₂`), `docs/literature-axioms.md` B6.
-/

namespace GQ2

open ContCoh

/-! ## The `μₙ`-dual of a discrete module -/

section MuDual

variable (n : ℕ) [NeZero n] (M : Type*) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]

/-- **The `μₙ`-dual module** `M′ = Hom(M, μₙ)` of a discrete `G_ℚ₂`-module `M`, with the Galois
conjugation action `(g • φ)(m) = g • φ(g⁻¹ • m)`.  A `def` (not `abbrev`): Mathlib's
codomain-only action on `M →+ MuN n` must not be found here (see module docstring). -/
def MuDual : Type _ := M →+ MuN n

noncomputable instance : AddCommGroup (MuDual n M) :=
  inferInstanceAs (AddCommGroup (M →+ MuN n))

noncomputable instance : FunLike (MuDual n M) M (MuN n) :=
  inferInstanceAs (FunLike (M →+ MuN n) M (MuN n))

instance : AddMonoidHomClass (MuDual n M) M (MuN n) :=
  inferInstanceAs (AddMonoidHomClass (M →+ MuN n) M (MuN n))

omit [NeZero n] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction AbsGalQ2 M]
  [ContinuousSMul AbsGalQ2 M] in
/-- Extensionality for the dual module, keyed to the synonym's own head. -/
@[ext] lemma MuDual.ext {φ ψ : MuDual n M} (h : ∀ m : M, φ m = ψ m) : φ = ψ :=
  DFunLike.ext φ ψ h

omit [NeZero n] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction AbsGalQ2 M]
  [ContinuousSMul AbsGalQ2 M] in
/-- Evaluation of the zero dual (the synonym's `FunLike` head keeps Mathlib's
`AddMonoidHom` simp set from firing; these `rfl`-lemmas replace it). -/
@[simp] lemma MuDual.zero_apply (m : M) : (0 : MuDual n M) m = 0 := rfl

omit [NeZero n] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction AbsGalQ2 M]
  [ContinuousSMul AbsGalQ2 M] in
@[simp] lemma MuDual.add_apply (φ ψ : MuDual n M) (m : M) : (φ + ψ) m = φ m + ψ m := rfl

instance : TopologicalSpace (MuDual n M) := ⊥

instance : DiscreteTopology (MuDual n M) := ⟨rfl⟩

instance [Finite M] : Finite (MuDual n M) :=
  Finite.of_injective (fun φ : MuDual n M => (φ : M → MuN n)) DFunLike.coe_injective

/-- The conjugation action of `G_ℚ₂` on `Hom(M, μₙ)`. -/
noncomputable instance : DistribMulAction AbsGalQ2 (MuDual n M) where
  smul g φ :=
    { toFun := fun m => g • φ (g⁻¹ • m)
      map_zero' := by rw [smul_zero, map_zero, smul_zero]
      map_add' := fun a b => by rw [smul_add, map_add, smul_add] }
  one_smul φ := by
    refine DFunLike.ext _ _ fun m => ?_
    show (1 : AbsGalQ2) • φ ((1 : AbsGalQ2)⁻¹ • m) = φ m
    rw [inv_one, one_smul, one_smul]
  mul_smul g h φ := by
    refine DFunLike.ext _ _ fun m => ?_
    show (g * h) • φ ((g * h)⁻¹ • m) = g • (h • φ (h⁻¹ • g⁻¹ • m))
    rw [mul_inv_rev, mul_smul, mul_smul]
  smul_zero g := by
    refine DFunLike.ext _ _ fun m => ?_
    show g • (0 : MuDual n M) (g⁻¹ • m) = 0
    rw [MuDual.zero_apply, smul_zero]
  smul_add g φ ψ := by
    refine DFunLike.ext _ _ fun m => ?_
    show g • (φ + ψ) (g⁻¹ • m) = g • φ (g⁻¹ • m) + g • ψ (g⁻¹ • m)
    rw [MuDual.add_apply, smul_add]

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul AbsGalQ2 M] in
@[simp] lemma muDual_smul_apply (g : AbsGalQ2) (φ : MuDual n M) (m : M) :
    (g • φ) m = g • φ (g⁻¹ • m) := rfl

/-- **Continuity of the conjugation action** (for finite `M`): the joint action kernel on `M`
and `μₙ` is an open subgroup fixing every `φ`, so all stabilizers are open. -/
instance [Finite M] : ContinuousSMul AbsGalQ2 (MuDual n M) := by
  rw [continuousSMul_iff_stabilizer_isOpen]
  intro φ
  set N : Subgroup AbsGalQ2 :=
    (⨅ m : M, MulAction.stabilizer AbsGalQ2 m) ⊓
      (⨅ x : MuN n, MulAction.stabilizer AbsGalQ2 x) with hN
  have hNopen : IsOpen (N : Set AbsGalQ2) := by
    rw [hN, Subgroup.coe_inf]
    exact (isOpen_iInf_stabilizer (G := AbsGalQ2) (M := M)).inter
      (isOpen_iInf_stabilizer (G := AbsGalQ2) (M := MuN n))
  refine Subgroup.isOpen_mono (fun u hu => ?_) hNopen
  -- `u` fixes all of `M` and all of `μₙ`, hence fixes `φ`
  rw [hN, Subgroup.mem_inf] at hu
  have huM : ∀ m : M, u • m = m := fun m => by
    have := Subgroup.mem_iInf.mp hu.1 m
    rwa [MulAction.mem_stabilizer_iff] at this
  have huμ : ∀ x : MuN n, u • x = x := fun x => by
    have := Subgroup.mem_iInf.mp hu.2 x
    rwa [MulAction.mem_stabilizer_iff] at this
  rw [MulAction.mem_stabilizer_iff]
  refine DFunLike.ext _ _ fun m => ?_
  rw [muDual_smul_apply, huμ]
  congr 1
  rw [inv_smul_eq_iff, huM m]

/-- **The evaluation pairing** `Hom(M, μₙ) →+ M →+ μₙ` — under the type synonym, literally the
identity.  This is the `μ` fed to the T-04 cup products in the duality clauses. -/
noncomputable def muDualPairing : MuDual n M →+ M →+ MuN n := AddMonoidHom.id (M →+ MuN n)

omit [NeZero n] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction AbsGalQ2 M]
  [ContinuousSMul AbsGalQ2 M] in
@[simp] lemma muDualPairing_apply (φ : MuDual n M) (m : M) :
    muDualPairing n M φ m = φ m := rfl

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul AbsGalQ2 M] in
/-- Equivariance of the evaluation pairing — the `hμ` hypothesis of the cup products. -/
lemma muDualPairing_equivariant (g : AbsGalQ2) (φ : MuDual n M) (m : M) :
    muDualPairing n M (g • φ) (g • m) = g • muDualPairing n M φ m := by
  rw [muDualPairing_apply, muDualPairing_apply, muDual_smul_apply, inv_smul_smul]

end MuDual

/-! ## `μₙ` is `n`-torsion (needed to feed `μₙ` itself to the duality) -/

/-- `μₙ` is `n`-torsion: `n • x = 0` additively, i.e. `ζⁿ = 1`. -/
theorem nsmul_muN_eq_zero (n : ℕ) [NeZero n] (x : MuN n) : n • x = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul]
  show x.toMul ^ n = 1
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow]
  exact (mem_rootsOfUnity n _).mp x.toMul.2

/-! ## The duality bundle -/

/-- **B6 (local Tate duality for `ℚ₂`), the bundle** — per-`n` form (see the module docstring
for the encoding decisions and flagged deviations).  `inv` identifies `H²(G_ℚ₂, μₙ)` with
`ℤ/n`, and for every finite discrete `n`-torsion module `M` the evaluation cup pairing is
perfect in the three degree pairs, in the sense that `x ↦ inv ∘ (x ∪ ·)` is a bijection onto
the Pontryagin dual `H^{2−i}(G_ℚ₂, M) →+ ZMod n`.

Modules are quantified over `Type` (`Type 0`): every finite module is isomorphic to one there,
and all of the paper's coefficients (`𝔽₂`-modules, `μₙ`, duals) live there. -/
structure TateDuality (n : ℕ) [NeZero n] where
  /-- The invariant map: `H²(G_ℚ₂, μₙ) ≅ ℤ/n` (unnormalized; see deviations). -/
  inv : H2 AbsGalQ2 (MuN n) ≃+ ZMod n
  /-- Perfectness in degrees `(0, 2)`: `H⁰(M′) ≅ Hom(H²(M), ℤ/n)`. -/
  perfect02 : ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M],
      (∀ x : M, n • x = 0) →
      Function.Bijective fun c : (H0 AbsGalQ2 (MuDual n M)) =>
        inv.toAddMonoidHom.comp
          (cup02 (muDualPairing n M) (muDualPairing_equivariant n M) c)
  /-- Perfectness in degrees `(1, 1)`: `H¹(M′) ≅ Hom(H¹(M), ℤ/n)`. -/
  perfect11 : ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M],
      (∀ x : M, n • x = 0) →
      Function.Bijective fun c : H1 AbsGalQ2 (MuDual n M) =>
        inv.toAddMonoidHom.comp
          (cup11 (muDualPairing n M) (muDualPairing_equivariant n M) c)
  /-- Perfectness in degrees `(2, 0)`: `H²(M′) ≅ Hom(H⁰(M), ℤ/n)`. -/
  perfect20 : ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
      [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M],
      (∀ x : M, n • x = 0) →
      Function.Bijective fun c : H2 AbsGalQ2 (MuDual n M) =>
        inv.toAddMonoidHom.comp
          (cup20 (muDualPairing n M) (muDualPairing_equivariant n M) c)

/-! ## Stress tests (axiom-free: parametrized over an arbitrary bundle)

Each consequence below takes `D : TateDuality n`, so it exercises the bundle's clauses without
consuming the axiom; `#print axioms` stays at the standard three. -/

section StressTests

variable {n : ℕ} [NeZero n]

/-- **`#H²(G_ℚ₂, μₙ) = n`** — the invariant map pins down the size of the dualizing `H²`
(the local analogue of `inv : Br(k) ≅ ℚ/ℤ` restricted to `n`-torsion). -/
theorem TateDuality.card_H2_muN (D : TateDuality n) :
    Nat.card (H2 AbsGalQ2 (MuN n)) = n := by
  rw [Nat.card_congr D.inv.toEquiv, Nat.card_zmod]

section Consequences

variable (D : TateDuality n)
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M]
  (htor : ∀ x : M, n • x = 0)

include D htor

/-- Duality, `(0,2)` cardinality form: `#H⁰(M′) = #Hom(H²(M), ℤ/n)`. -/
theorem TateDuality.card_H0_dual :
    Nat.card (H0 AbsGalQ2 (MuDual n M))
      = Nat.card (H2 AbsGalQ2 M →+ ZMod n) :=
  Nat.card_congr (Equiv.ofBijective _ (D.perfect02 M htor))

/-- Duality, `(1,1)` cardinality form: `#H¹(M′) = #Hom(H¹(M), ℤ/n)`. -/
theorem TateDuality.card_H1_dual :
    Nat.card (H1 AbsGalQ2 (MuDual n M))
      = Nat.card (H1 AbsGalQ2 M →+ ZMod n) :=
  Nat.card_congr (Equiv.ofBijective _ (D.perfect11 M htor))

/-- Duality, `(2,0)` cardinality form: `#H²(M′) = #Hom(H⁰(M), ℤ/n)`. -/
theorem TateDuality.card_H2_dual :
    Nat.card (H2 AbsGalQ2 (MuDual n M))
      = Nat.card ((H0 AbsGalQ2 M) →+ ZMod n) :=
  Nat.card_congr (Equiv.ofBijective _ (D.perfect20 M htor))

/-- Injectivity extraction (the form used for dimension counts): a nonzero `H¹(M′)`-class cups
non-trivially against some `H¹(M)`-class. -/
theorem TateDuality.exists_cup_ne_zero_of_ne_zero {c : H1 AbsGalQ2 (MuDual n M)}
    (hc : c ≠ 0) :
    ∃ d : H1 AbsGalQ2 M,
      cup11 (muDualPairing n M) (muDualPairing_equivariant n M) c d ≠ 0 := by
  by_contra hall
  have hall' : ∀ d : H1 AbsGalQ2 M,
      cup11 (muDualPairing n M) (muDualPairing_equivariant n M) c d = 0 :=
    fun d => not_not.mp fun h => hall ⟨d, h⟩
  apply hc
  apply (D.perfect11 M htor).1
  show D.inv.toAddMonoidHom.comp (cup11 (muDualPairing n M) (muDualPairing_equivariant n M) c)
      = D.inv.toAddMonoidHom.comp (cup11 (muDualPairing n M) (muDualPairing_equivariant n M) 0)
  ext d
  simp only [AddMonoidHom.coe_comp, Function.comp_apply]
  rw [hall' d, cup11_zero_left]

end Consequences

/-- **Self-instantiation sanity check**: `μₙ` itself is a legal argument of the duality (it is
finite, discrete, and `n`-torsion by `nsmul_muN_eq_zero`), giving
`#H¹(Hom(μₙ,μₙ)) = #Hom(H¹(μₙ), ℤ/n)`. -/
example (D : TateDuality n) :
    Nat.card (H1 AbsGalQ2 (MuDual n (MuN n)))
      = Nat.card (H1 AbsGalQ2 (MuN n) →+ ZMod n) :=
  D.card_H1_dual (MuN n) (nsmul_muN_eq_zero n)

end StressTests

end GQ2
