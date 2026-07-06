/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.DeepPart
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Local Kummer theory for the deep half  (ticket P-15f1)

Infrastructure for `SectionSix.lemma_6_17_dim` — the deep-half dimension count
`#X₊² = #H¹(ℚ₂, V)` for ramified `V` — via the paper's filtration route (Route B of
`docs/p15f1-scoping.md`): under the Kummer identification
`H¹(ℚ₂, V) ≅ Hom_{H_V}(V^∨, M_K)` (`M_K = K^×/K^{×2}`, `K` the tame splitting field),
the multiplicity `d j` of `V^∨` at filtration depth `j` satisfies `d j = d (2e − j)`
(graded duality, self-duality of `V` through the invariant form `q`) and `d e = 0`
(Lemma 6.10, middle layer unramified), so the deep tail `Σ_{j>e} d j` is exactly half the
total — no `H¹`-pairing is involved.

## Layers

* **Layer 1 (this file, bottom)**: the counting core — pure `Finset` arithmetic turning the
  four count facts (`htotal`, `hdeep`, `hpair`, `hmid`) into the `lemma_6_17_dim` goal.
  Std-3, no axioms, no design risk.
* **Layer 2 (to come)**: the `DeepKummerData` bundle (B6/`TateDuality` pattern) with fields
  the literature-leaf candidates L1 (Kummer bijectivity of `kummerClassK`), L2 (the (93)
  square-class filtration), L3 ((94) Hilbert orthogonality — consumed by P-15f2, not here),
  plus the flagged Lemma-6.11 consequence (`Hom`-exactness; paper-proved content, must be
  discharged before any axiom is declared).  The construction `DeepKummerData → Layer-1
  counts` is the P3 (inflation–restriction) + P4 (`deepPart` bridge) + P5 work of the
  scoping doc.

## Ticket protocol

Own file of **P-15f1**; the eventual `SectionSix` splice follows the P-15d/6.18ram pattern
(statement moves out at closure).  Axiom census unchanged (13) — Layer 2's leaf bundle is
PENDING USER APPROVAL and nothing here declares an axiom.
-/

namespace GQ2.LocalKummer

open Finset ContCoh SectionSix DeepPart RepIndependence

/-! ## Layer 1: the halving arithmetic -/

/-- **Duality-paired sums halve.**  If the multiplicities `d` on depths `0, …, 2e` satisfy
the duality symmetry `d j = d (2e − j)` and the middle multiplicity vanishes, then the total
is twice the deep tail `Σ_{e < j ≤ 2e} d j`.  (The tail is indexed as `Ico (e+1) (2e+1)`.) -/
theorem sum_eq_two_mul_tail (e : ℕ) (d : ℕ → ℕ)
    (hpair : ∀ j ≤ 2 * e, d j = d (2 * e - j)) (hmid : d e = 0) :
    (Finset.range (2 * e + 1)).sum d = 2 * (Finset.Ico (e + 1) (2 * e + 1)).sum d := by
  have hsplit : (Finset.Ico 0 (e + 1)).sum d + (Finset.Ico (e + 1) (2 * e + 1)).sum d
      = (Finset.Ico 0 (2 * e + 1)).sum d :=
    Finset.sum_Ico_consecutive d (Nat.zero_le _) (by omega)
  have htop : (Finset.Ico 0 (e + 1)).sum d = (Finset.Ico 0 e).sum d + d e :=
    Finset.sum_Ico_succ_top (Nat.zero_le e) d
  have hbij : (Finset.Ico 0 e).sum d = (Finset.Ico (e + 1) (2 * e + 1)).sum d := by
    refine Finset.sum_nbij' (fun j ↦ 2 * e - j) (fun j ↦ 2 * e - j) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      rw [Finset.mem_Ico] at ha ⊢
      omega
    · intro a ha
      rw [Finset.mem_Ico] at ha ⊢
      omega
    · intro a ha
      rw [Finset.mem_Ico] at ha
      omega
    · intro a ha
      rw [Finset.mem_Ico] at ha
      omega
    · intro a ha
      rw [Finset.mem_Ico] at ha
      exact hpair a (by omega)
  rw [Finset.range_eq_Ico]
  omega

/-- **Isotropic subgroups are at most half-dimensional** (the `≤` half of `card_sq_of_selfperp`):
for a biadditive nondegenerate `𝔽₂`-pairing on a finite 2-torsion group `A`, a totally isotropic
subgroup `X` (`P` vanishes on `X × X`) has `#X² ≤ #A`.  The descended pairing embeds
`X ↪ Hom(A/X, 𝔽₂)` (injective by nondegeneracy), so `#X ≤ #(A/X) = #A / #X`.  Supplies the
upper bound `#X₊ ≤ 2^m` for the deep half once its isotropy under the Tate pairing (the (94)
Hilbert orthogonality of deep Kummer classes) is established. -/
theorem card_sq_le_of_isotropic {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) (P : A → A → ZMod 2)
    (hPl : ∀ a b c : A, P (a + b) c = P a c + P b c)
    (hPr : ∀ a b c : A, P a (b + c) = P a b + P a c)
    (hnd : ∀ a : A, a ≠ 0 → ∃ b : A, P a b ≠ 0)
    (X : AddSubgroup A) (hXX : ∀ x ∈ X, ∀ y ∈ X, P x y = 0) :
    Nat.card ↥X ^ 2 ≤ Nat.card A := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype ↥X := Fintype.ofFinite _
  have h2X : ∀ x : ↥X, x + x = 0 := fun x => Subtype.ext (h2 _)
  have h2Q : ∀ y : A ⧸ X, y + y = 0 := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add, h2]; rfl
  haveI : Finite (A ⧸ X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A ⧸ X → ZMod 2)) DFunLike.coe_injective
  have hX_le : Nat.card ↥X ≤ Nat.card (A ⧸ X) := by
    have hinj : Function.Injective (fun x : ↥X =>
        QuotientAddGroup.lift X
          (AddMonoidHom.mk' (fun a => P ↑x a) (fun a b => hPr ↑x a b))
          (fun y hy => by
            rw [AddMonoidHom.mem_ker]
            exact hXX ↑x x.2 y hy)) := by
      intro x x' heq
      have hpe : ∀ a : A, P ↑x a = P ↑x' a := by
        intro a
        have h := DFunLike.congr_fun heq (QuotientAddGroup.mk a)
        simpa [QuotientAddGroup.lift_mk] using h
      have hsum0 : ((x + x' : ↥X) : A) = 0 := by
        by_contra hne
        obtain ⟨b, hb⟩ := hnd _ hne
        apply hb
        rw [AddSubgroup.coe_add, hPl, hpe b]
        exact CharTwo.add_self_eq_zero _
      have hxx' : x + x' = 0 := Subtype.ext hsum0
      have := congrArg (· + x') hxx'
      rwa [add_assoc, h2X, add_zero, zero_add] at this
    calc Nat.card ↥X ≤ Nat.card (A ⧸ X →+ ZMod 2) :=
          Nat.card_le_card_of_injective _ hinj
      _ = Nat.card (A ⧸ X) := GQ2.QuadraticFp2.card_addHom_zmod2 (A ⧸ X) h2Q
  have hquot : Nat.card (A ⧸ X) * Nat.card ↥X = Nat.card A :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X).symm
  rw [sq]
  calc Nat.card ↥X * Nat.card ↥X ≤ Nat.card (A ⧸ X) * Nat.card ↥X :=
        Nat.mul_le_mul_right _ hX_le
    _ = Nat.card A := hquot

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V]
  [DistribMulAction C V] in
/-- **Layer-1 counting core for `lemma_6_17_dim`** — the dimension clause from the four
count facts.  Once Layer 2 produces, for the tame splitting-field filtration depth data
`(e, d)`,
* `htotal` — `#H¹ = 2^{Σ_{j≤2e} d j}` (Kummer identification + `Hom`-exactness),
* `hdeep`  — `#X₊ = 2^{Σ_{j>e} d j}` (the `deepPart` bridge),
* `hpair`  — `d j = d (2e−j)` (graded duality + self-duality of `V` via `q`), and
* `hmid`   — `d e = 0` (Lemma 6.10 + ramifiedness),

the `#X₊² = #H¹` goal is this pure arithmetic. -/
theorem card_deepPart_sq_of_counts (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (e : ℕ) (d : ℕ → ℕ)
    (htotal : Nat.card (H1 AbsGalQ2 V) = 2 ^ (Finset.range (2 * e + 1)).sum d)
    (hdeep : Nat.card (deepPart (V := V) ρ)
      = 2 ^ (Finset.Ico (e + 1) (2 * e + 1)).sum d)
    (hpair : ∀ j ≤ 2 * e, d j = d (2 * e - j)) (hmid : d e = 0) :
    Nat.card (deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  rw [hdeep, htotal, sum_eq_two_mul_tail e d hpair hmid, ← pow_mul, two_mul, Nat.mul_comm]

/-! ## Layer 2a: the scalar restriction map and the deep classes

The identification `H¹(ℚ₂, V) ≅ Hom_{H_V}(V^∨, M_K)` is built from the **scalar restriction
map** `phiRes ρ x φ = [n ↦ φ((Quotient.out x) n)] ∈ H¹(N, 𝔽₂)`, `N = ker ρ`.  Everything is
stated *ambiently over* `G_ℚ₂`: no `G/N`-quotient types and no `K^×/K^{×2}`-carrier appear.
`H¹(N, 𝔽₂)` itself plays the role of `M_K` (the L1 Kummer leaf will identify them), the
`H_V`-equivariance conditions are phrased through conjugation inside `G_ℚ₂`, and the two
cohomological inputs produced later from Lemma 6.11 projectivity (`InflationVanishes`,
extension of equivariant homs) are plain ambient statements about cocycles.

Since the `N`-action on both `V` (as `N = ker ρ`) and `𝔽₂` is trivial, `B¹` vanishes on both
sides of the restriction: `H¹(N, 𝔽₂)`-classes are just continuous homs (`h1ofFun_eq_zero_iff`)
and restriction is representative-independent at the raw-cocycle level (`phiRes_of_rep`). -/

section ScalarRestriction

/-- `𝔽₂`-functionals separate points on an elementary finite 2-group.  (Local copy of
`GQ2.FoxH.elemDual_separates` from `GQ2/Devissage.lean`, duplicated to keep this file's build
decoupled from the `FoxHeisenberg` import chain — a P-13f hot file.) -/
theorem exists_functional_ne_zero {A : Type*} [AddCommGroup A]
    (hA2 : ∀ a : A, a + a = 0) {a : A} (ha : a ≠ 0) : ∃ φ : A →+ ZMod 2, φ a ≠ 0 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact hA2 v)
  by_contra h
  refine ha ?_
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2) a]
  intro φ
  by_contra hφ
  exact h ⟨φ.toAddMonoidHom, hφ⟩

/-- Over a subgroup `N ≤ G_ℚ₂` the coefficient action on `𝔽₂` is trivial, so `B¹(N, 𝔽₂) = 0`:
a raw cocycle's class vanishes iff the cocycle is the zero function.  (`N` is bound as
`Subgroup AbsGalQ2` — the `phiRes`-side instance flavor — so that `rw` matches at use
sites; the defeq `Kummer.GaloisGroup ℚ_[2]`-flavor of `deepClasses` casts at use sites.) -/
theorem h1ofFun_eq_zero_iff {N : Subgroup AbsGalQ2} {f : ↥N → ZMod 2}
    (hf : f ∈ Z1 ↥N (ZMod 2)) : H1ofFun ↥N f = 0 ↔ f = 0 := by
  constructor
  · intro h0
    rw [H1ofFun_of_mem hf] at h0
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp h0
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨w₀, hw₀⟩ := hmem
    funext n
    show (⟨f, hf⟩ : ↥(Z1 ↥N (ZMod 2))).1 n = 0
    rw [← congrFun hw₀ n]
    show n • w₀ - w₀ = 0
    rw [show n • w₀ = w₀ from rfl, sub_self]
  · rintro rfl
    rw [H1ofFun_of_mem hf]
    have : (⟨0, hf⟩ : ↥(Z1 ↥N (ZMod 2))) = 0 := Subtype.ext rfl
    rw [this, map_zero]

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

/-- The **scalar restriction map** `Θ`: the `φ`-coordinate of the restriction of a class
`x ∈ H¹(ℚ₂, V)` to `N = ker ρ` — the class of `n ↦ φ((Quotient.out x) n)` in `H¹(N, 𝔽₂)`.
`deepPart ρ` is definitionally `{x | ∀ φ, phiRes ρ x φ ∈ deepClasses}` (`mem_deepPart_iff`). -/
noncomputable def phiRes (x : H1 AbsGalQ2 V) (φ : V →+ ZMod 2) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
    (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) => φ ((Quotient.out x).1 (n : AbsGalQ2)))

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V]
  [DistribMulAction C V] in
/-- Unfolding rule for `phiRes` (a `rw`-safe alternative to `unfold`, which delta-exposes the
`H1`-quotient in type arguments). -/
theorem phiRes_def (x : H1 AbsGalQ2 V) (φ : V →+ ZMod 2) :
    phiRes ρ x φ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
        => φ ((Quotient.out x).1 (n : AbsGalQ2))) := rfl

variable {ρ}

/-- **Representative independence** of the scalar restriction: any `Z¹`-representative of `x`
computes `phiRes ρ x φ` (representatives differ by a coboundary, and coboundaries vanish
pointwise on `ker ρ`). -/
theorem phiRes_of_rep (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    {b : ↥(Z1 AbsGalQ2 V)} {x : H1 AbsGalQ2 V} (hb : H1mk AbsGalQ2 V b = x)
    (φ : V →+ ZMod 2) :
    H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) => φ (b.1 (n : AbsGalQ2)))
      = phiRes ρ x φ := by
  have hd : H1mk AbsGalQ2 V (b - Quotient.out x) = 0 := by
    rw [map_sub, hb, H1mk_out, sub_self]
  unfold phiRes
  congr 1
  funext n
  have h0 := vanish_on_ker_of_H1mk_eq_zero ρ hρ hd n
  have hsub : b.1 (n : AbsGalQ2) - (Quotient.out x).1 (n : AbsGalQ2) = 0 := h0
  rw [sub_eq_zero.mp hsub]

/-- `phiRes` is additive in the class. -/
theorem phiRes_add (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (x y : H1 AbsGalQ2 V) (φ : V →+ ZMod 2) :
    phiRes ρ (x + y) φ = phiRes ρ x φ + phiRes ρ y φ := by
  have hb : H1mk AbsGalQ2 V (Quotient.out x + Quotient.out y) = x + y := by
    rw [map_add, H1mk_out, H1mk_out]
  rw [← phiRes_of_rep hρ hb φ]
  have hfun : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        φ ((Quotient.out x + Quotient.out y).1 (n : AbsGalQ2)))
      = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          φ ((Quotient.out x).1 (n : AbsGalQ2)))
        + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
            φ ((Quotient.out y).1 (n : AbsGalQ2)) := by
    funext n
    show φ ((Quotient.out x).1 (n : AbsGalQ2) + (Quotient.out y).1 (n : AbsGalQ2)) = _
    rw [map_add]
    rfl
  rw [hfun, H1ofFun_add (phiRestrict_mem_Z1 ρ hρ _ φ) (phiRestrict_mem_Z1 ρ hρ _ φ)]
  rfl

/-- `phiRes` is additive in the functional. -/
theorem phiRes_add_phi (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (x : H1 AbsGalQ2 V) (φ ψ : V →+ ZMod 2) :
    phiRes ρ x (φ + ψ) = phiRes ρ x φ + phiRes ρ x ψ := by
  unfold phiRes
  have hfun : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        (φ + ψ) ((Quotient.out x).1 (n : AbsGalQ2)))
      = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          φ ((Quotient.out x).1 (n : AbsGalQ2)))
        + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
            ψ ((Quotient.out x).1 (n : AbsGalQ2)) := by
    funext n
    exact AddMonoidHom.add_apply φ ψ _
  rw [hfun, H1ofFun_add (phiRestrict_mem_Z1 ρ hρ _ φ) (phiRestrict_mem_Z1 ρ hρ _ ψ)]

end ScalarRestriction

/-! ### The deep classes in `H¹(N, 𝔽₂)` and the `deepPart` bridge -/

section DeepClasses

/-- **The deep Kummer classes** in `H¹(N, 𝔽₂)`: classes of restricted Kummer cocycles of deep
units (the image of `U_{e+1}(K) ⊂ K^×/K^{×2}` under the Kummer identification, stated without
the identification).  `deepPart ρ` is exactly the set of classes all of whose scalar
restrictions land here (`mem_deepPart_iff`). -/
def deepClasses (N : Subgroup (Kummer.GaloisGroup ℚ_[2])) : Set (H1 ↥N (ZMod 2)) :=
  {ξ | ∃ A β : AlgebraicClosure ℚ_[2], IsDeepUnit N A ∧ β ^ 2 = A ∧ β ≠ 0 ∧
    H1ofFun ↥N (fun n : ↥N => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2])) = ξ}

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V]
  [DistribMulAction C V] in
/-- **The `deepPart` bridge (P4, definitional half)**: membership in the deep half is exactly
"every scalar restriction is a deep Kummer class". -/
theorem mem_deepPart_iff (x : H1 AbsGalQ2 V) :
    x ∈ deepPart (V := V) ρ ↔ ∀ φ : V →+ ZMod 2,
      phiRes ρ x φ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  constructor
  · intro hx φ
    obtain ⟨A, β, hdeep, hsq, hβ0, heq⟩ := hx φ
    exact ⟨A, β, hdeep, hsq, hβ0, heq⟩
  · intro hx φ
    obtain ⟨A, β, hdeep, hsq, hβ0, heq⟩ := hx φ
    exact ⟨A, β, hdeep, hsq, hβ0, heq⟩

end DeepClasses

/-! ### Injectivity of the scalar restriction from the inflation input -/

section Injectivity

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

/-- **The ambient inflation-vanishing input** (to be produced from Lemma 6.11 projectivity
via `H¹(H_V, V) = 0`, stated with no `G/N`-quotient types): every continuous cocycle that
vanishes pointwise on `N = ker ρ` is a coboundary.  A cocycle vanishing on `N` factors
through `G/N ≅ H_V`, so this is precisely inflation-`H¹`-vanishing. -/
def InflationVanishes : Prop :=
  ∀ b : ↥(Z1 AbsGalQ2 V), (∀ n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2),
      b.1 (n : AbsGalQ2) = 0) →
    ∃ w₀ : V, ∀ g : AbsGalQ2, b.1 g = g • w₀ - w₀

variable {ρ}

/-- All scalar restrictions of `x` vanish iff the canonical representative vanishes pointwise
on `N = ker ρ` (functionals separate points; `B¹(N, 𝔽₂) = 0`). -/
theorem phiRes_eq_zero_iff (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) (x : H1 AbsGalQ2 V) :
    (∀ φ : V →+ ZMod 2, phiRes ρ x φ = 0)
      ↔ ∀ n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2),
          (Quotient.out x).1 (n : AbsGalQ2) = 0 := by
  constructor
  · intro h n
    by_contra hne
    obtain ⟨φ, hφ⟩ := exists_functional_ne_zero hV2 hne
    have h0 := h φ
    rw [phiRes_def,
      h1ofFun_eq_zero_iff (phiRestrict_mem_Z1 ρ hρ (Quotient.out x) φ)] at h0
    exact hφ (congrFun h0 n)
  · intro h φ
    rw [phiRes_def,
      h1ofFun_eq_zero_iff (phiRestrict_mem_Z1 ρ hρ (Quotient.out x) φ)]
    funext n
    rw [h n, map_zero]
    rfl

/-- **Injectivity of the scalar restriction package** from the inflation input: two classes
with equal scalar restrictions are equal.  (With `InflationVanishes` discharged by Lemma 6.11
projectivity, this is the injectivity half of `H¹(ℚ₂,V) ≅ Hom_{H_V}(V^∨, M_K)`.) -/
theorem phiRes_injective (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) (hinf : InflationVanishes (V := V) ρ)
    {x y : H1 AbsGalQ2 V} (h : ∀ φ : V →+ ZMod 2, phiRes ρ x φ = phiRes ρ y φ) :
    x = y := by
  have hz : ∀ φ : V →+ ZMod 2, phiRes ρ (x - y) φ = 0 := by
    intro φ
    have hxy : x - y + y = x := sub_add_cancel x y
    have hsplit := phiRes_add hρ (x - y) y φ
    rw [hxy, h φ] at hsplit
    exact add_right_cancel (hsplit.symm.trans (zero_add (phiRes ρ y φ)).symm)
  have hout := (phiRes_eq_zero_iff hρ hV2 (x - y)).mp hz
  obtain ⟨w₀, hw₀⟩ := hinf (Quotient.out (x - y)) hout
  have hzero : x - y = 0 := by
    rw [← H1mk_out (x - y)]
    refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    exact ⟨w₀, funext fun g => (hw₀ g).symm⟩
  rw [← sub_add_cancel x y, hzero, zero_add]

end Injectivity

/-! ### Discharging `InflationVanishes` — the coprime-averaging proof

`InflationVanishes` (= `H¹(H_V, V) = 0` content) is **not** a projectivity fact: the paper
proves it (proof of (78), p. 25) by coprime-order averaging over the odd tame inertia
`I ◁ H_V` plus `V^I = 0`.  The argument here is Hochschild–Serre-free: a cocycle `b` vanishing
on `N = ker ρ` (whose kernel acts trivially on `V`, `hρ`) descends to a cocycle
`b̄ : C → V` on the finite image `C`; averaging over `I` (odd order ⟹ `|I|·x = x` in the
2-torsion `V`) makes `b̄` cohomologous to a cocycle killed on `I`; and the two-way evaluation
`b̄(ic) = b̄(c·(c⁻¹ic))` forces the residue into `V^I = 0`.

Stated **parametrically** over `(I, |I| odd, V^I = 0)` — the tame-arithmetic verification of
those (odd inertia, ramified-simple fixed-point-freeness) is supplied at the `DeepKummerData`
instantiation. -/

section InflationProof

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

/-- In a 2-torsion additive group, an odd multiple is the identity. -/
theorem odd_nsmul_eq_self {A : Type*} [AddCommGroup A] (htor : ∀ a : A, a + a = 0)
    {n : ℕ} (hn : Odd n) (x : A) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul', two_nsmul, htor, zero_add]

/-- **The image of tame inertia has odd order.**  For any hom `c : T_tame →* C` into a finite
group, `orderOf (c τ)` is odd: applying `c` to the tame relation `τ^σ = τ²` shows `c τ` is
conjugate to `(c τ)²`, so `orderOf (c τ) = orderOf ((c τ)²) = orderOf (c τ) / gcd(·, 2)`, which
forces the order odd.  Supplies `Odd (Nat.card ↥⟨c τ⟩)` for the inertia subgroup at the
`inflationVanishes_of_oddNormal` instantiation. -/
theorem odd_orderOf_tameInertia {D : Type*} [Group D] [TopologicalSpace D] [Finite D]
    (c : ContinuousMonoidHom Ttame D) : Odd (orderOf (c tameTau)) := by
  set t := c tameTau with ht
  set s := c tameSigma with hs
  have hrel : s⁻¹ * t * s = t ^ 2 := by
    have h := congrArg (⇑c) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using h
  have hsc : SemiconjBy s⁻¹ t (t ^ 2) := by
    show s⁻¹ * t = t ^ 2 * s⁻¹
    rw [← hrel]; group
  have hconj : orderOf t = orderOf (t ^ 2) := hsc.orderOf_eq
  have hpos : 0 < orderOf t := orderOf_pos t
  have hpow : orderOf (t ^ 2) = orderOf t / Nat.gcd (orderOf t) 2 := orderOf_pow t
  rw [hpow] at hconj
  rcases Nat.even_or_odd (orderOf t) with heven | hodd
  · exfalso
    have hdvd : 2 ∣ orderOf t := heven.two_dvd
    rw [Nat.gcd_eq_right hdvd] at hconj
    omega
  · exact hodd

/-- **The image of tame inertia is normal.**  If `c : T_tame →* C` (into a finite group) has
`c σ, c τ` generating `C`, then `⟨c τ⟩ = zpowers(c τ)` is normal: conjugation by `c σ` sends
`c τ` to `(c τ)²` (the tame relation), and `zpowers((c τ)²) = zpowers(c τ)` since `c τ` has odd
order — so `c σ` and `c τ` both normalize `zpowers(c τ)`, hence so does all of `C`.  Supplies
the `I.Normal` hypothesis of `inflationVanishes_of_oddNormal`.  (The generation hypothesis
`hgen` is the profinite fact `im c = closure{c σ, c τ}`, discharged at instantiation from the
surjectivity of the classifying map.) -/
theorem tameInertia_normal {D : Type*} [Group D] [TopologicalSpace D] [Finite D]
    (c : ContinuousMonoidHom Ttame D)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤) :
    (Subgroup.zpowers (c tameTau)).Normal := by
  set t := c tameTau with ht
  set s := c tameSigma with hs
  have hrel : s⁻¹ * t * s = t ^ 2 := by
    have h := congrArg (⇑c) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using h
  have hcop : Nat.Coprime 2 (orderOf t) :=
    Nat.coprime_two_left.mpr (odd_orderOf_tameInertia c)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hzeq : Subgroup.zpowers (t ^ 2) = Subgroup.zpowers t := by
    apply le_antisymm
    · rw [Subgroup.zpowers_le]
      exact pow_mem (Subgroup.mem_zpowers t) 2
    · rw [Subgroup.zpowers_le]
      exact ⟨(m : ℤ), by show (t ^ 2) ^ (m : ℤ) = t; rw [zpow_natCast]; exact hm⟩
  have hHmap : (Subgroup.zpowers t).map (MulAut.conj s⁻¹).toMonoidHom = Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    have hconjt : (MulAut.conj s⁻¹).toMonoidHom t = t ^ 2 := by
      show s⁻¹ * t * (s⁻¹)⁻¹ = t ^ 2
      rw [inv_inv, hrel]
    rw [hconjt, hzeq]
  refine Subgroup.normalizer_eq_top_iff.mp ?_
  rw [eq_top_iff, ← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe]
  rcases hx with rfl | rfl
  · -- `s` normalizes `⟨t⟩`: conjugation by `s⁻¹` maps `⟨t⟩` onto itself.
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    have heq : s⁻¹ * h * s = (MulAut.conj s⁻¹).toMonoidHom h := by
      show s⁻¹ * h * s = s⁻¹ * h * (s⁻¹)⁻¹
      rw [inv_inv]
    rw [heq]
    conv_rhs => rw [← hHmap]
    exact (Subgroup.mem_map_iff_mem (MulAut.conj s⁻¹).injective).symm
  · -- `t` normalizes `⟨t⟩` (it lies inside it).
    exact Subgroup.le_normalizer (Subgroup.mem_zpowers t)

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C] [TopologicalSpace V]
  [DiscreteTopology V] [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] in
/-- **The `I`-fixed submodule vanishes** (`V^I = 0`) for a normal subgroup `I ◁ C` acting
nontrivially on the simple module `V`: `V^I` is a `C`-submodule (by normality), and it is not
all of `V` (some `i ∈ I` moves some vector), so simplicity forces `V^I = ⊥`.  This produces
the `hVI` hypothesis of `inflationVanishes_of_oddNormal` for a ramified simple module. -/
theorem fixedByNormal_eq_bot (I : Subgroup C) (hInorm : I.Normal)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hmoves : ∃ i ∈ I, ∃ v : V, i • v ≠ v) :
    ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0 := by
  set W : AddSubgroup V :=
    { carrier := {v | ∀ i ∈ I, i • v = v}
      zero_mem' := fun i _ => smul_zero i
      add_mem' := fun {a b} ha hb i hi => by rw [smul_add, ha i hi, hb i hi]
      neg_mem' := fun {a} ha i hi => by rw [smul_neg, ha i hi] } with hW
  have hWmem : ∀ v : V, v ∈ W ↔ ∀ i ∈ I, i • v = v := fun v => Iff.rfl
  have hWstable : ∀ (h : C), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    rw [hWmem] at hw ⊢
    intro i hi
    have hconj : h⁻¹ * i * h ∈ I := by
      have := hInorm.conj_mem i hi h⁻¹
      rwa [inv_inv] at this
    calc i • (h • w) = (i * h) • w := by rw [mul_smul]
      _ = (h * (h⁻¹ * i * h)) • w := by group
      _ = h • ((h⁻¹ * i * h) • w) := by rw [mul_smul]
      _ = h • w := by rw [hw _ hconj]
  rcases hsimple W hWstable with hbot | htop
  · intro v hv
    have hvW : v ∈ W := (hWmem v).mpr hv
    rw [hbot, AddSubgroup.mem_bot] at hvW
    exact hvW
  · exfalso
    obtain ⟨i, hi, v, hv⟩ := hmoves
    have hvW : v ∈ W := by rw [htop]; exact AddSubgroup.mem_top v
    exact hv ((hWmem v).mp hvW i hi)

omit [DiscreteTopology C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **`InflationVanishes` from an odd normal subgroup with no fixed vectors** (the
coprime-averaging discharge, parametric): if `ρ : G_ℚ₂ ↠ C` with `C` acting on the 2-torsion
`V` through `ρ`, and `C` has a normal subgroup `I` of odd order with `V^I = 0`, then every
cocycle vanishing on `ker ρ` is a coboundary. -/
theorem inflationVanishes_of_oddNormal
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (hsurj : Function.Surjective ⇑ρ)
    (I : Subgroup C) (hInorm : I.Normal) (hIodd : Odd (Nat.card ↥I))
    (hVI : ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0) :
    InflationVanishes (V := V) ρ := by
  classical
  haveI : Fintype ↥I := Fintype.ofFinite _
  intro b hbN
  obtain ⟨-, hcoc⟩ := mem_Z1_iff.mp b.2
  -- `b.1` is constant on `ρ`-fibres (its kernel acts trivially, `hρ`).
  have hdesc : ∀ g₁ g₂ : AbsGalQ2, ρ g₁ = ρ g₂ → b.1 g₁ = b.1 g₂ := by
    intro g₁ g₂ hg
    have hmem : g₁⁻¹ * g₂ ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
      rw [MonoidHom.mem_ker]
      show ρ (g₁⁻¹ * g₂) = 1
      rw [map_mul, map_inv, hg, inv_mul_cancel]
    have h0 : b.1 (g₁⁻¹ * g₂) = 0 := hbN ⟨g₁⁻¹ * g₂, hmem⟩
    have := hcoc g₁ (g₁⁻¹ * g₂)
    rw [h0, smul_zero, add_zero, mul_inv_cancel_left] at this
    exact this.symm
  -- descend `b` to `b̄ : C → V`.
  set σ := Function.surjInv hsurj with hσdef
  have hσ : ∀ c : C, ρ (σ c) = c := Function.surjInv_eq hsurj
  set bbar : C → V := fun c => b.1 (σ c) with hbbar
  have hbbar_spec : ∀ g : AbsGalQ2, bbar (ρ g) = b.1 g := fun g =>
    hdesc (σ (ρ g)) g (hσ (ρ g))
  have hbbar_coc : ∀ c d : C, bbar (c * d) = bbar c + c • bbar d := by
    intro c d
    have h1 : b.1 (σ (c * d)) = b.1 (σ c * σ d) :=
      hdesc _ _ (by rw [hσ, map_mul, hσ, hσ])
    show b.1 (σ (c * d)) = b.1 (σ c) + c • b.1 (σ d)
    rw [h1, hcoc, hρ, hσ]
  -- the averaging witness `w₀ = ∑_{i ∈ I} b̄ i`.
  set w₀ : V := ∑ i : ↥I, bbar (i : C) with hw₀def
  -- averaging identity: on `I`, `b̄` is the coboundary of `w₀`.
  have havg : ∀ g₀ : ↥I, bbar (g₀ : C) = (g₀ : C) • w₀ - w₀ := by
    intro g₀
    have hreindex : ∑ i : ↥I, bbar ((g₀ : C) * (i : C)) = w₀ := by
      rw [hw₀def, ← Equiv.sum_comp (Equiv.mulLeft g₀) (fun j : ↥I => bbar (j : C))]
      rfl
    have hexpand : ∑ i : ↥I, bbar ((g₀ : C) * (i : C))
        = (Nat.card ↥I) • bbar (g₀ : C) + (g₀ : C) • w₀ := by
      simp_rw [hbbar_coc]
      rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.smul_sum, ← hw₀def,
        Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [hreindex] at hexpand
    rw [odd_nsmul_eq_self hV2 hIodd] at hexpand
    -- `w₀ = b̄ g₀ + g₀ • w₀`  ⟹  `b̄ g₀ = g₀ • w₀ − w₀`  (char 2).
    have : bbar (g₀ : C) = w₀ - (g₀ : C) • w₀ := by
      rw [eq_sub_iff_add_eq]; exact hexpand.symm
    rw [this]
    have hna : -w₀ = w₀ := neg_eq_of_add_eq_zero_left (hV2 w₀)
    have hnb : -((g₀ : C) • w₀) = (g₀ : C) • w₀ := neg_eq_of_add_eq_zero_left (hV2 _)
    rw [sub_eq_add_neg, sub_eq_add_neg, hna, hnb, add_comm]
  -- the error cocycle `r c = b̄ c − (c • w₀ − w₀)` is a cocycle killed on `I`.
  set r : C → V := fun c => bbar c - ((c : C) • w₀ - w₀) with hrdef
  have hr_coc : ∀ c d : C, r (c * d) = r c + c • r d := by
    intro c d
    show bbar (c * d) - ((c * d) • w₀ - w₀)
      = (bbar c - (c • w₀ - w₀)) + c • (bbar d - (d • w₀ - w₀))
    rw [hbbar_coc, smul_sub, smul_sub, mul_smul]
    abel
  have hr_I : ∀ i : C, i ∈ I → r i = 0 := by
    intro i hi
    show bbar i - ((i : C) • w₀ - w₀) = 0
    rw [havg ⟨i, hi⟩, sub_self]
  -- two-way evaluation forces `r c ∈ V^I = 0`.
  have hr_zero : ∀ c : C, r c = 0 := by
    intro c
    refine hVI (r c) fun i hi => ?_
    have e1 : r (i * c) = i • r c := by rw [hr_coc, hr_I i hi, zero_add]
    have hconj : c⁻¹ * i * c ∈ I := by
      have := hInorm.conj_mem i hi c⁻¹
      rwa [inv_inv] at this
    have e2 : r (i * c) = r c := by
      have hic : i * c = c * (c⁻¹ * i * c) := by group
      rw [hic, hr_coc, hr_I _ hconj, smul_zero, add_zero]
    rw [← e1, e2]
  -- assemble the coboundary.
  refine ⟨w₀, fun g => ?_⟩
  have hz := hr_zero (ρ g)
  rw [hrdef] at hz
  simp only [hbbar_spec, sub_eq_zero] at hz
  rw [hz, hρ]

omit [DiscreteTopology C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **`InflationVanishes` for a ramified simple tame module** — the four-brick assembly.
Takes the classifying data `ρ` (surjective) with lower map `c : T_tame →* C`, the ramified
simple hypotheses, and the tame-generation fact `hgen`; discharges `InflationVanishes` by
instantiating `inflationVanishes_of_oddNormal` at the inertia subgroup `I = ⟨c τ⟩`, whose three
hypotheses are supplied by `tameInertia_normal` (normal), `odd_orderOf_tameInertia` (odd order),
and `fixedByNormal_eq_bot` (`V^I = 0`, from `hram`).  The only inputs beyond `lemma_6_17_dim`'s
own are the two profinite facts `hsurj` (`im ρ = C`) and `hgen` (`C = ⟨c σ, c τ⟩`). -/
theorem inflationVanishes_ramifiedTame (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (c : ContinuousMonoidHom Ttame C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (hsurj : Function.Surjective ⇑ρ)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v) :
    InflationVanishes (V := V) ρ := by
  have hInorm : (Subgroup.zpowers (c tameTau)).Normal := tameInertia_normal c hgen
  have hIodd : Odd (Nat.card ↥(Subgroup.zpowers (c tameTau))) := by
    rw [Nat.card_zpowers]; exact odd_orderOf_tameInertia c
  have hVI : ∀ v : V, (∀ i ∈ Subgroup.zpowers (c tameTau), i • v = v) → v = 0 :=
    fixedByNormal_eq_bot (Subgroup.zpowers (c tameTau)) hInorm hsimple
      (by obtain ⟨v, hv⟩ := hram; exact ⟨c tameTau, Subgroup.mem_zpowers _, v, hv⟩)
  exact inflationVanishes_of_oddNormal ρ hρ hV2 hsurj (Subgroup.zpowers (c tameTau))
    hInorm hIodd hVI

end InflationProof

/-! ### Conjugation equivariance and the admissible-family identification

The `H_V`-module structure on `H¹(N, 𝔽₂)` is the conjugation action, defined ambiently for
every `g : G_ℚ₂` (it factors through `G/N` since inner-`N` conjugation composed with the
trivial coefficient action is homotopic to the identity — not needed here).  A scalar
restriction family `φ ↦ phiRes ρ x φ` is additive and conjugation-equivariant
(`phiRes_conj`, from the cocycle identity `b(g⁻¹ng) = g⁻¹ • b(n)` on `N = ker ρ`); the
**extension input** (to be produced from Lemma 6.11 projectivity via `H²(H_V, V) = 0`)
asserts every such family arises.  Together with `phiRes_injective` this identifies
`H¹(ℚ₂, V)` with the admissible families, carrying `deepPart` onto the families valued in
`deepClasses` — the counting interface consumed by the Layer-2b filtration bundle. -/

section ConjAction

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

omit [DiscreteTopology C] [Finite C] in
/-- Conjugation carries `N = ker ρ` into itself. -/
theorem conj_mem_ker (g : AbsGalQ2)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    g⁻¹ * (n : AbsGalQ2) * g ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  simpa using (MonoidHom.normal_ker ρ.toMonoidHom).conj_mem (n : AbsGalQ2) n.2 g⁻¹

/-- The conjugation self-map of `N = ker ρ`, `n ↦ g⁻¹ n g`, as a continuous map. -/
noncomputable def conjMap (g : AbsGalQ2) (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
  ⟨g⁻¹ * (n : AbsGalQ2) * g, conj_mem_ker ρ g n⟩

omit [DiscreteTopology C] [Finite C] in
theorem continuous_conjMap (g : AbsGalQ2) : Continuous (conjMap ρ g) :=
  Continuous.subtype_mk
    (((continuous_const.mul continuous_subtype_val).mul continuous_const)) _

omit [DiscreteTopology C] [Finite C] in
/-- Conjugation-precomposition preserves `Z¹(N, 𝔽₂)` (the coefficient action is trivial, so
cocycles are continuous homs and conjugation is a continuous endomorphism). -/
theorem comp_conjMap_mem_Z1 {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) (g : AbsGalQ2) :
    (fun n => f (conjMap ρ g n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_conjMap ρ g), fun n m => ?_⟩
  show f (conjMap ρ g (n * m)) = f (conjMap ρ g n) + n • f (conjMap ρ g m)
  have hmul : conjMap ρ g (n * m) = conjMap ρ g n * conjMap ρ g m := by
    apply Subtype.ext
    show g⁻¹ * ((n : AbsGalQ2) * m) * g = (g⁻¹ * n * g) * (g⁻¹ * m * g)
    group
  have htriv : ∀ (a : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (z : ZMod 2),
      a • z = z := fun _ _ => rfl
  rw [hmul, hcoc, htriv, htriv]

/-- **The conjugation action** of `g ∈ G_ℚ₂` on `H¹(N, 𝔽₂)`, `[f] ↦ [n ↦ f(g⁻¹ n g)]`. -/
noncomputable def conjAct (g : AbsGalQ2)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
    (fun n => (Quotient.out ξ).1 (conjMap ρ g n))

omit [DiscreteTopology C] [Finite C] in
/-- Computation rule for `conjAct` on the class of an explicit cocycle. -/
theorem conjAct_h1ofFun (g : AbsGalQ2)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) f)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (fun n => f (conjMap ρ g n)) := by
  set ξ := H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) f with hξ
  have hout : (Quotient.out ξ : ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))).1
      = f := by
    have h1 : H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) (Quotient.out ξ)
        = H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⟨f, hf⟩ := by
      have hoe : H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) (Quotient.out ξ)
          = ξ := Quotient.out_eq ξ
      rw [hoe, hξ, H1ofFun_of_mem hf]
    have hz0 : H1mk ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)
        (Quotient.out ξ - ⟨f, hf⟩) = 0 := by
      rw [map_sub, h1, sub_self]
    have hdiff := (QuotientAddGroup.eq_zero_iff _).mp hz0
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff
    obtain ⟨w₀, hw₀⟩ := hdiff
    funext n
    have hn := congrFun hw₀ n
    have hz : (Quotient.out ξ - ⟨f, hf⟩ :
        ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))).1 n = 0 := by
      rw [← hn]
      show n • w₀ - w₀ = 0
      rw [show n • w₀ = w₀ from rfl, sub_self]
    have : (Quotient.out ξ).1 n - f n = 0 := hz
    exact sub_eq_zero.mp this
  unfold conjAct
  rw [hout]

end ConjAction

section Equivariance

variable {ρ : ContinuousMonoidHom AbsGalQ2 C}

omit [DiscreteTopology C] [Finite C] [Finite V] [ContinuousSMul AbsGalQ2 V] in
/-- **The conjugation identity for cocycles on the kernel**: for a cocycle `b` and
`n ∈ N = ker ρ` (so that conjugates of `n` act trivially on `V`),
`b(g⁻¹ n g) = g⁻¹ • b(n)`. -/
theorem cocycle_conj (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (b : ↥(Z1 AbsGalQ2 V)) (g : AbsGalQ2)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    b.1 (g⁻¹ * (n : AbsGalQ2) * g) = g⁻¹ • b.1 (n : AbsGalQ2) := by
  obtain ⟨-, hcoc⟩ := mem_Z1_iff.mp b.2
  have hker : ∀ m : AbsGalQ2, m ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) →
      ∀ v : V, m • v = v := fun m hm v => by
    rw [hρ, show ρ m = 1 from hm, one_smul]
  -- b(g⁻¹ · n) = b(g⁻¹) + g⁻¹ • b(n)
  have h1 : b.1 (g⁻¹ * (n : AbsGalQ2)) = b.1 g⁻¹ + g⁻¹ • b.1 (n : AbsGalQ2) := hcoc g⁻¹ n
  -- b((g⁻¹ n g) · g⁻¹) = b(g⁻¹ n g) + (g⁻¹ n g) • b(g⁻¹) = b(g⁻¹ n g) + b(g⁻¹)
  have h2 : b.1 (g⁻¹ * (n : AbsGalQ2)) = b.1 (g⁻¹ * (n : AbsGalQ2) * g) + b.1 g⁻¹ := by
    have := hcoc (g⁻¹ * (n : AbsGalQ2) * g) g⁻¹
    rw [show g⁻¹ * (n : AbsGalQ2) * g * g⁻¹ = g⁻¹ * (n : AbsGalQ2) by group] at this
    rw [this, hker _ (conj_mem_ker ρ g n)]
  -- cancel b(g⁻¹)
  have := h1.symm.trans h2
  -- b(g⁻¹) + g⁻¹•b(n) = b(g⁻¹ng) + b(g⁻¹)
  have hcomm : b.1 g⁻¹ + g⁻¹ • b.1 (n : AbsGalQ2)
      = g⁻¹ • b.1 (n : AbsGalQ2) + b.1 g⁻¹ := add_comm _ _
  exact (add_right_cancel (hcomm.symm.trans this)).symm

/-- **Equivariance of the scalar restriction family**:
`g · (phiRes x φ) = phiRes x (φ ∘ (g⁻¹ • ·))`. -/
theorem phiRes_conj (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (x : H1 AbsGalQ2 V) (φ : V →+ ZMod 2) (g : AbsGalQ2) :
    conjAct ρ g (phiRes ρ x φ)
      = phiRes ρ x (φ.comp (DistribSMul.toAddMonoidHom V g⁻¹)) := by
  rw [phiRes_def, conjAct_h1ofFun ρ g (phiRestrict_mem_Z1 ρ hρ (Quotient.out x) φ),
    phiRes_def]
  congr 1
  funext n
  show φ ((Quotient.out x).1 ((conjMap ρ g n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      : AbsGalQ2)) = φ (g⁻¹ • (Quotient.out x).1 (n : AbsGalQ2))
  congr 1
  exact cocycle_conj hρ (Quotient.out x) g n

end Equivariance

/-! ### The admissible families and the counting identification -/

section AdmissibleFamilies

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

/-- **An admissible family**: an additive, conjugation-equivariant assignment of
`H¹(N, 𝔽₂)`-classes to `𝔽₂`-functionals on `V` — the ambient encoding of
`Hom_{H_V}(V^∨, M_K)` (under the L1 Kummer leaf, `H¹(N, 𝔽₂) ≅ M_K`). -/
structure AdmissibleFam : Type where
  /-- The underlying assignment `V^∨ → H¹(N, 𝔽₂)`. -/
  fam : (V →+ ZMod 2) → H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)
  /-- Additivity in the functional. -/
  add' : ∀ φ ψ : V →+ ZMod 2, fam (φ + ψ) = fam φ + fam ψ
  /-- Conjugation equivariance. -/
  equiv' : ∀ (g : AbsGalQ2) (φ : V →+ ZMod 2),
    conjAct ρ g (fam φ) = fam (φ.comp (DistribSMul.toAddMonoidHom V g⁻¹))

/-- The scalar restriction family of a class, as an `AdmissibleFam`. -/
noncomputable def toFam (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (x : H1 AbsGalQ2 V) : AdmissibleFam (V := V) ρ where
  fam := phiRes ρ x
  add' := phiRes_add_phi hρ x
  equiv' g φ := phiRes_conj hρ x φ g

/-- **The extension input** (to be produced from Lemma 6.11 projectivity via
`H²(H_V, V) = 0`; ambient statement, no `G/N`-quotients): every admissible family is the
scalar restriction family of some class. -/
def FamiliesExtend : Prop :=
  ∀ ξ : AdmissibleFam (V := V) ρ, ∃ x : H1 AbsGalQ2 V, ∀ φ : V →+ ZMod 2,
    phiRes ρ x φ = ξ.fam φ

/-- **`FamiliesExtend` from a cardinality bound** — the cheap discharge of the
`H²(H_V, V) = 0` input.  `toFam` is already injective (from `hinf`, `phiRes_injective`); so
once the admissible families form a finite type no larger than `H¹(ℚ₂, V)`, `toFam` is
surjective and every family arises.  At the `DeepKummerData` instantiation this converts
`hext` into the very count `#AdmissibleFam` the filtration already supplies, so the degree-2
cochain-extension construction is never needed.  (`#H¹ = #V` is banked via B7;
`#AdmissibleFam` is the filtration/`Hom`-count.) -/
theorem familiesExtend_of_card_le (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) (hinf : InflationVanishes (V := V) ρ)
    [Finite (AdmissibleFam (V := V) ρ)]
    (hcard : Nat.card (AdmissibleFam (V := V) ρ) ≤ Nat.card (H1 AbsGalQ2 V)) :
    FamiliesExtend (V := V) ρ := by
  haveI : Finite (H1 AbsGalQ2 V) := GQ2.Foundations.finite_H1 V
  haveI : Fintype (H1 AbsGalQ2 V) := Fintype.ofFinite _
  haveI : Fintype (AdmissibleFam (V := V) ρ) := Fintype.ofFinite _
  have hinj : Function.Injective (toFam ρ hρ) := fun x y hxy =>
    phiRes_injective hρ hV2 hinf (fun φ => congrFun (congrArg AdmissibleFam.fam hxy) φ)
  have hcard' : Fintype.card (H1 AbsGalQ2 V) = Fintype.card (AdmissibleFam (V := V) ρ) := by
    have h1 : Fintype.card (H1 AbsGalQ2 V) ≤ Fintype.card (AdmissibleFam (V := V) ρ) :=
      Fintype.card_le_of_injective _ hinj
    have h2 : Fintype.card (AdmissibleFam (V := V) ρ) ≤ Fintype.card (H1 AbsGalQ2 V) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]; exact hcard
    omega
  have hbij : Function.Bijective (toFam ρ hρ) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard'⟩
  intro ξ
  obtain ⟨x, hx⟩ := hbij.2 ξ
  exact ⟨x, fun φ => congrFun (congrArg AdmissibleFam.fam hx) φ⟩

variable {ρ}

/-- **The identification**: given the two deferred cohomological inputs, `toFam` is an
equivalence `H¹(ℚ₂, V) ≃ AdmissibleFam`. -/
noncomputable def h1EquivFam (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) (hinf : InflationVanishes (V := V) ρ)
    (hext : FamiliesExtend (V := V) ρ) :
    H1 AbsGalQ2 V ≃ AdmissibleFam (V := V) ρ :=
  Equiv.ofBijective (toFam ρ hρ)
    ⟨fun x y hxy => phiRes_injective hρ hV2 hinf
        (fun φ => congrFun (congrArg AdmissibleFam.fam hxy) φ),
      fun ξ => by
        obtain ⟨x, hx⟩ := hext ξ
        refine ⟨x, ?_⟩
        have hfam : (toFam ρ hρ x).fam = ξ.fam := funext hx
        cases ξ
        cases hfam
        rfl⟩

/-- **Count `H¹` by families** (modulo the deferred inputs). -/
theorem card_H1_eq_card_fam (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) (hinf : InflationVanishes (V := V) ρ)
    (hext : FamiliesExtend (V := V) ρ) :
    Nat.card (H1 AbsGalQ2 V) = Nat.card (AdmissibleFam (V := V) ρ) :=
  Nat.card_congr (h1EquivFam hρ hV2 hinf hext)

/-- **Count the deep half by deep-valued families** (modulo the deferred inputs): the
identification carries `X₊` onto the admissible families valued in the deep classes. -/
theorem card_deepPart_eq_card_deepFam (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) (hinf : InflationVanishes (V := V) ρ)
    (hext : FamiliesExtend (V := V) ρ) :
    Nat.card (deepPart (V := V) ρ)
      = Nat.card {ξ : AdmissibleFam (V := V) ρ // ∀ φ : V →+ ZMod 2,
          ξ.fam φ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)} :=
  Nat.card_congr <| (Equiv.subtypeEquiv (h1EquivFam hρ hV2 hinf hext)
    (fun x => mem_deepPart_iff ρ x))

end AdmissibleFamilies

/-! ## Layer 2b: the `DeepKummerData` bundle and the parametric dimension theorem

Following the B6/`TateDuality` pattern, `DeepKummerData` bundles exactly the paper-content and
literature-leaf outputs that the filtration count produces, so that `lemma_6_17_dim` is proved
*parametrically* over it (std-3) and only the instantiation remains.  Its fields:

* the filtration depth bound `e` (`= v_K(2)`) and the `V^∨`-isotypic multiplicities `d j`;
* the two deferred cohomological inputs `hinf`/`hext` (the `H¹`/`H²`(H_V, V) vanishing that
  Lemma 6.11 projectivity supplies);
* the self-duality symmetry `hpair` (`d j = d (2e−j)`, from `V ≅ V^∨` through the invariant
  form `q` + graded Hilbert duality) and the middle vanishing `hmid` (`d e = 0`, Lemma 6.10 +
  ramifiedness); and
* the two family counts (`#{admissible families} = 2^{Σ_{j≤2e} d j}` and
  `#{deep families} = 2^{Σ_{j>e} d j}`, the exact-`Hom_{H_V}(V^∨, −)` computation over the unit
  filtration of `M_K`).

NONE of these is an axiom; the census is unchanged.  Producing an instance is the remaining f1
work (the L1/L2 leaves — pending approval — plus the Lemma-6.11 discharge). -/

section DeepKummerData

/-- The bundled local-Kummer count data for a ramified simple module, from which the deep-half
dimension clause follows parametrically (Route B of `docs/p15f1-scoping.md`). -/
structure DeepKummerData (ρ : ContinuousMonoidHom AbsGalQ2 C) : Type where
  /-- The filtration depth bound `e = v_K(2)`. -/
  e : ℕ
  /-- The `V^∨`-isotypic multiplicity of `M_K` at depth `j`. -/
  d : ℕ → ℕ
  /-- **Inflation vanishing** (`H¹(H_V, V) = 0` from Lemma 6.11 projectivity). -/
  hinf : InflationVanishes (V := V) ρ
  /-- **Extension surjectivity** (`H²(H_V, V) = 0` from Lemma 6.11 projectivity). -/
  hext : FamiliesExtend (V := V) ρ
  /-- **Graded self-duality**: `V ≅ V^∨` (via the invariant form `q`) plus Hilbert duality of
  the depth-`j` and depth-`(2e−j)` graded pieces give equal multiplicities. -/
  hpair : ∀ j ≤ 2 * e, d j = d (2 * e - j)
  /-- **Middle vanishing** (Lemma 6.10): the unpaired middle depth `j = e` carries no ramified
  copy of `V`. -/
  hmid : d e = 0
  /-- **Total count**: `#{admissible families} = 2^{Σ_{j ≤ 2e} d j}` (exact
  `Hom_{H_V}(V^∨, −)` over the full unit filtration of `M_K`). -/
  card_fam : Nat.card (AdmissibleFam (V := V) ρ) = 2 ^ (Finset.range (2 * e + 1)).sum d
  /-- **Deep count**: `#{deep families} = 2^{Σ_{e < j ≤ 2e} d j}` (the same computation over
  the deep tail `U_{e+1}`). -/
  card_deepFam :
    Nat.card {ξ : AdmissibleFam (V := V) ρ // ∀ φ : V →+ ZMod 2,
        ξ.fam φ ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)}
      = 2 ^ (Finset.Ico (e + 1) (2 * e + 1)).sum d

/-- **The deep-half dimension clause, parametric over `DeepKummerData`** (std-3): the count data
plus the two module-setup hypotheses give `#X₊² = #H¹` — the mathematical content of
`SectionSix.lemma_6_17_dim`, minus the (still-open) construction of a `DeepKummerData`
instance for the ramified simple setup. -/
theorem dim_deepPart_of_data (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (DK : DeepKummerData (V := V) ρ) :
    Nat.card (deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  refine card_deepPart_sq_of_counts ρ DK.e DK.d ?_ ?_ DK.hpair DK.hmid
  · rw [card_H1_eq_card_fam hρ hV2 DK.hinf DK.hext, DK.card_fam]
  · rw [card_deepPart_eq_card_deepFam hρ hV2 DK.hinf DK.hext, DK.card_deepFam]

/-- **The deep-half dimension clause from the balance condition** (std-3 + B7): the whole graded
`DeepKummerData` scaffold is not needed — `#X₊² = #H¹` is equivalent (by Lagrange on the finite
`H¹`) to the single **balance** `#X₊ = #(H¹ / X₊)`, i.e. "the deep half is exactly half".  This
is the honest remaining content of `lemma_6_17_dim`: the balance packages the (94)/cup self-duality
(deep ⟂ its complement) and the `Hom`-exactness lower bound (Lemma 6.11) into one group-theoretic
equality.  `#H¹ = #V` is banked (B7) at the consumer. -/
theorem dim_deepPart_of_balance (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (hbal : Nat.card ↥(deepPartSubgroup ρ hρ hV2)
      = Nat.card (H1 AbsGalQ2 V ⧸ deepPartSubgroup ρ hρ hV2)) :
    Nat.card (deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V) := by
  haveI : Finite (H1 AbsGalQ2 V) := GQ2.Foundations.finite_H1 V
  have hcard_eq : Nat.card (deepPart (V := V) ρ) = Nat.card ↥(deepPartSubgroup ρ hρ hV2) := rfl
  have hlag : Nat.card (H1 AbsGalQ2 V)
      = Nat.card (H1 AbsGalQ2 V ⧸ deepPartSubgroup ρ hρ hV2)
        * Nat.card ↥(deepPartSubgroup ρ hρ hV2) :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [hcard_eq, sq, hlag, ← hbal]

/-- **The deep-half upper bound from isotropy** (std-3 + B6 + B7): if the deep half `X₊` is
totally isotropic under the polar of `Q⁰_loc` (the (94)/cup-orthogonality of deep Kummer
classes — a hypothesis here, the genuine shared gap with P-15f2), then `#X₊² ≤ #H¹`, i.e.
`#X₊ ≤ 2^m`.  The isotropy-only half of `card_deepPart_sq_of_selfperp`; combined with the
lower bound (Lemma 6.11 / exactness) it pins `#X₊ = 2^m`. -/
theorem card_deepPart_sq_le_of_isotropic (D : TateDuality 2)
    (q : V → ZMod 2) (hq : GQ2.QuadraticFp2.IsQuadraticFp2 q)
    (hns : GQ2.QuadraticFp2.Nonsingular q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (hV2 : ∀ v : V, v + v = 0)
    (hiso : ∀ x ∈ deepPartSubgroup ρ hρ hV2, ∀ y ∈ deepPartSubgroup ρ hρ hV2,
      GQ2.QuadraticFp2.polar (Q0loc D dat ρ) x y = 0) :
    Nat.card (deepPart (V := V) ρ) ^ 2 ≤ Nat.card (H1 AbsGalQ2 V) := by
  haveI : Finite (H1 AbsGalQ2 V) := GQ2.Foundations.finite_H1 V
  have hq' := isQuadraticFp2_Q0loc D q hq dat hdat ρ hρ hqG
  have hns' := nonsingular_Q0loc D q hq hns hV2 dat hdat ρ hρ hqG
  exact card_sq_le_of_isotropic (GQ2.DeepPart.h1_add_self hV2)
    (fun a b => GQ2.QuadraticFp2.polar (Q0loc D dat ρ) a b)
    hq'.polar_add_left hq'.polar_add_right hns' (deepPartSubgroup ρ hρ hV2) hiso

end DeepKummerData

end GQ2.LocalKummer
