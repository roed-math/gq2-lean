/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.PairingK
import GQ2.Dyadic.Projectivity
import GQ2.Dyadic.TameQuotientK
import GQ2.AdmissibleCount
import GQ2.DeepDualityK
import GQ2.Shapiro.Extend

/-!
# The deep-unit package over a general local source — the vanishing lane (LG4a)

Packet Def. 6.11 (`def:deep-package`) and the parts of Prop. 6.12 (`prop:deep-lagrangian`) that
feed the **vanishing** clause of Lemma 6.17, retyped from the `ℚ₂` models
(`GQ2/SectionSix.lean`, `GQ2/DeepPart/Q0locLayer.lean`, `GQ2/LocalKummer.lean`,
`GQ2/DeepDualityK.lean`) to an arbitrary topological group `Γ` in place of `G_ℚ₂`.  In the
dyadic campaign `Γ = G_K = ↥U` for `U ≤ G_ℚ₂` open of finite index.  The `ℚ₂` originals are
untouched (design memo `docs/dyadic/lg-design.md` §2: clone, zero in-place edits).

**Scope split (orchestrator, binding).**  This file (LG4a) owns the deep-unit package and the
vanishing lane.  `LocalGauss/Ramified.lean` (LG4b) owns the dimension lane, the join
`card_Q0loc_zero_eq_of_dim_of_vanish_K` and the endpoint `prop_6_18_ramified_K`; it imports this
file.  §8 below stages the vanishing-side exports LG4b consumes.

## THE ANCHORING CONVENTION (binding for LG4b and LG5)

Deep units are `AbsGalQ2`-side objects (`GQ2.SectionSix.IsDeepUnit` quantifies over a
`Subgroup (Kummer.GaloisGroup ℚ_[2])`), while the pairing, the deep classes and `Q⁰` live over the
`Γ`-side splitting group `N_K = ker ρ ≤ Γ`.  The memo (§7.2) flagged this as the top technical
risk ("nested-subtype friction") and provisioned LG2's `H1anchor`/`anchorEquiv`/`H1congrGroup`
transport for it.  **The convention fixed here does not transport cohomology at all:**

> **Anchoring is by the ELEMENT map, through the RANGE of an anchor homomorphism.**
> A *local source with an anchor* is a pair `(Γ, anc)` with `anc : ContinuousMonoidHom Γ AbsGalQ2`
> (`anc = U.subtype` in the campaign, `anc = id` at `Γ = G_ℚ₂`).  For the splitting group the
> anchor is `kerAnc anc ρ : ContinuousMonoidHom ↥(ker ρ) AbsGalQ2`, the composite with the
> subtype map, and **the anchored subgroup is its range**
> `ancSubgroup (kerAnc anc ρ) = (ker ρ).map anc.toMonoidHom ≤ G_ℚ₂`.
> Deep/mid *units* are `IsDeepUnit`/`IsMidUnit` **at that anchored subgroup** (so all `ℚ₂`-side
> deep-unit lemmas apply verbatim); deep/mid *classes* live in `H¹(↥(ker ρ), 𝔽₂)` — the group the
> pairing lives on — as `H1ofFun _ (fun n ↦ κ_β (anc n))`.
>
> No `Subgroup ↥U`-vs-`Subgroup AbsGalQ2` cast, no cohomology transport, and no
> `H1anchor`/`anchorEquiv` use appears anywhere in the lane.  The `ℚ₂` splice's own device — the
> *pointwise* hypothesis `hker` relating the splitting group to `k.fixingSubgroup`, so that "no
> subgroup-equality cast is ever formed" (`GQ2/DeepDualityK.lean` §(H3) header) — generalizes
> verbatim once the two sides are compared through `anc` rather than through a subtype coercion.

Consequences LG4b/LG5 must follow: (i) every deep-side hypothesis is stated at
`ancSubgroup (kerAnc anc ρ)`; (ii) `hker` hypotheses read
`∀ x : AbsGalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup`; (iii) at `Γ = G_ℚ₂`,
`anc = ContinuousMonoidHom.id`, every declaration here reduces to its `ℚ₂` model — §9 records the
regression identities.

## Contents

* §1 the anchor, the anchored subgroup, and the anchored Kummer cocycle bricks.
* §2 **deep/mid classes** at an anchor: `deepClassesAt`, `deepClassesSubgroupAt`,
  `midClassesSubgroupAt` — the `Γ`-side twins of `GQ2.LocalKummer.deepClasses`,
  `GQ2.deepClassesSubgroup`, `GQ2.midClassesSubgroup`.
* §3 **the deep half `X₊`**: `phiResK`, `deepPartK` (packet Def. 6.11(c)), `mem_deepPartK_iff`,
  and `deepPartSubgroupK` (Prop. 6.12: `X₊` is a subgroup).
* §4 **the (H3) isotropy splice** retyped (memo §2 row 3, deferred from LG2 by design):
  `pairingK_kummer_eq_zero_K`, `pairingK_deep_deep_K`, `pairingK_mid_deep_K`,
  `deepClassesSubgroup_le_pairPerp_pairingK_K`, `midClassesSubgroup_le_pairPerp_pairingK_K`.
* §5 **projective inflation–restriction** (packet Def. 6.11(a)): `InflationVanishesK`,
  `FamiliesExtendK`, `AdmissibleFamK`, `h1EquivFamK`, and the discharges —
  `inflationVanishes_of_oddNormalK` (**coprime averaging**, not projectivity: packet §12
  over-attribution correction adopted at AX5) and `inflationVanishes_ramifiedTameQ` at every
  `q = 2^f` through PJ1's `tame_zpowers_normal_pow`/`tame_odd_order_pow` and F3's
  `gen_tq_quotient`; `familiesExtend_of_packageK` from PJ1's `lemma_6_11_of_tame_pair_pow`.
* §6 **deep-class cup vanishing** at the splitting group (the `hvanish` core of packet Rem. 6.13's
  square and free layers).
* §7 conjugation stability of the deep classes (the free-orbit input).
* §8 **staged exports for LG4b**: the vanishing-side hypothesis bundle
  `Q0locVanishesOnDeep` in the exact shape the `ℚ₂` join consumes.
* §9 the `n = 1` regression identities.

## Middle-layer argument (packet Rem. 6.13)

The case split feeding §6/§7 is **odd tame-inertia characters vs trivial-inertia exceptional
pieces** — there is **no "even inertia order" case**.  Odd tame inertia at every `q = 2^f` is
packet Lem. 3.1, available here as `GQ2.Dyadic.TameQ.odd_order` (F3) and
`GQ2.Dyadic.tame_odd_order_pow` (PJ1); it is what §5's averaging discharge consumes, and it is
what makes the exceptional (trivial-inertia) pieces the only other branch.  The `ℚ₂` file's
`GQ2.LocalKummer.odd_orderOf_tameInertia`/`tameInertia_normal` (`GQ2/LocalKummer.lean` :382,
:409) hard-code `q = 2` through `Ttame`; they are **not** used here.

## Axiom hygiene

Everything is parametrized over the duality bundle `D`, so §1–§3 and §5–§8 print the standard
three.  §4 consumes the `ℚ₂` Tier-5 leaves (`GQ2.LocalKummer.cup_deepClasses`,
`GQ2.cup_midClasses_deepClasses`) exactly as its model does, hence the model's B11a-side set —
a subset of `GQ2.pairingK_deep_deep`'s.  Nothing new; census unchanged.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The `AlgEquiv`-flavoured spelling of `G_ℚ₂`.  Definitionally `GQ2.AbsGalQ2`, but reducible, so
that instance search finds the `AlgEquiv`-action on `ℚ̄₂` (`GQ2/Kummer.lean`, `GaloisGroup`
docstring).  Anchors are typed with this spelling throughout; call sites may pass `AbsGalQ2`-typed
data (e.g. `U.subtype`) unchanged. -/
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

/-! ## §1 The anchor and the anchored Kummer cocycle

`Γ`-side groups reach the deep-unit vocabulary through a continuous homomorphism into `G_ℚ₂`.
For the campaign's tower `N_K = ker ρ ≤ G_K = ↥U ≤ G_ℚ₂` the anchor of the splitting group is
`kerAnc U.subtype ρ`, whose range is the memo's anchored `N = N_K.map U.subtype`. -/

section Anchor

variable {Θ : Type} [Group Θ] [TopologicalSpace Θ]

/-- **The anchored subgroup** of an anchor homomorphism: the image `anc(Θ) ≤ G_ℚ₂`.  This is the
subgroup at which all deep/mid *unit* predicates are evaluated (see the anchoring convention in
the module docstring).

The result type is spelled `GalQ2 = Kummer.GaloisGroup ℚ_[2]` rather than `AbsGalQ2`:
the two are definitionally equal and elaborate interchangeably (as throughout
`GQ2/DeepDualityK.lean`), but only the `Kummer.GaloisGroup` spelling lets instance search find
the `AlgEquiv`-action on `ℚ̄₂` that the deep-unit predicates use (`GQ2/Kummer.lean` §`GaloisGroup`
docstring). -/
noncomputable def ancSubgroup (anc : ContinuousMonoidHom Θ GalQ2) : Subgroup GalQ2 :=
  anc.toMonoidHom.range

theorem mem_ancSubgroup (anc : ContinuousMonoidHom Θ GalQ2) (n : Θ) :
    anc n ∈ ancSubgroup anc :=
  ⟨n, rfl⟩

theorem ancSubgroup_le_iff {anc : ContinuousMonoidHom Θ GalQ2}
    {W : Subgroup GalQ2} :
    ancSubgroup anc ≤ W ↔ ∀ n : Θ, anc n ∈ W := by
  constructor
  · exact fun h n => h (mem_ancSubgroup anc n)
  · rintro h _ ⟨n, rfl⟩; exact h n

variable {C : Type} [Group C] [TopologicalSpace C]

/-- **The anchor of the splitting group** `N_K = ker ρ ≤ Γ`: the anchor of `Γ` restricted along
the subtype inclusion.  Its range is the memo's anchored `N = N_K.map U.subtype`. -/
noncomputable def kerAnc (anc : ContinuousMonoidHom Θ GalQ2) (ρ : ContinuousMonoidHom Θ C) :
    ContinuousMonoidHom ↥(ρ.toMonoidHom.ker : Subgroup Θ) GalQ2 :=
  anc.comp ⟨(ρ.toMonoidHom.ker : Subgroup Θ).subtype, continuous_subtype_val⟩

@[simp] theorem kerAnc_apply (anc : ContinuousMonoidHom Θ GalQ2)
    (ρ : ContinuousMonoidHom Θ C) (n : ↥(ρ.toMonoidHom.ker : Subgroup Θ)) :
    kerAnc anc ρ n = anc (n : Θ) := rfl

/-- The anchored splitting subgroup is the `anc`-image of `ker ρ` — the memo's
`N = N_K.map U.subtype`. -/
theorem ancSubgroup_kerAnc (anc : ContinuousMonoidHom Θ GalQ2)
    (ρ : ContinuousMonoidHom Θ C) :
    ancSubgroup (kerAnc anc ρ)
      = (ρ.toMonoidHom.ker : Subgroup Θ).map anc.toMonoidHom := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩; exact ⟨(n : Θ), n.2, rfl⟩
  · rintro ⟨g, hg, rfl⟩; exact ⟨⟨g, hg⟩, rfl⟩

end Anchor

section KummerBricks

/-- **The Kummer cocycle is additive at any two elements fixing the square** — the element-level
form of `GQ2.kummerCocycleFun_hom_on` / `GQ2.DeepPart.kummerRestrict_hom`, with the subgroup
binder removed so that it applies at anchored elements `anc n` of any source group. -/
theorem kcf_hom_of_fixed {A β : ℚ̄₂} (hsq : β ^ 2 = A) (hβ0 : β ≠ 0)
    {g h : GalQ2} (hg : g • A = A) (hh : h • A = A) :
    Kummer.kummerCocycleFun β (g * h)
      = Kummer.kummerCocycleFun β g + Kummer.kummerCocycleFun β h := by
  have eq1 : ∀ {x : GalQ2}, x • β = -β → Kummer.kummerCocycleFun β x = 1 :=
    fun hx => if_neg (fun e => ne_neg_of_ne_zero hβ0 (e.symm.trans hx))
  rcases two_values_of_fixed hsq hg with hg' | hg' <;>
    rcases two_values_of_fixed hsq hh with hh' | hh'
  · rw [Kummer.kummerCocycleFun_eq0 hg', Kummer.kummerCocycleFun_eq0 hh',
      Kummer.kummerCocycleFun_eq0 (by rw [mul_smul, hh', hg'])]
    decide
  · rw [Kummer.kummerCocycleFun_eq0 hg', eq1 hh', eq1 (by rw [mul_smul, hh', smul_neg, hg'])]
    decide
  · rw [eq1 hg', Kummer.kummerCocycleFun_eq0 hh', eq1 (by rw [mul_smul, hh', hg'])]
    decide
  · rw [eq1 hg', eq1 hh',
      Kummer.kummerCocycleFun_eq0 (by rw [mul_smul, hh', smul_neg, hg', neg_neg])]
    decide

/-- **Multiplicativity of the Kummer cocycle in the radicand**, at elements fixing both squares —
the element-level form of `GQ2.kcf_mul_of_fixed`. -/
theorem kcf_mul_of_fixedAt {A₁ A₂ β₁ β₂ : ℚ̄₂} (hsq₁ : β₁ ^ 2 = A₁) (hsq₂ : β₂ ^ 2 = A₂)
    (hβ₁ : β₁ ≠ 0) (hβ₂ : β₂ ≠ 0) {g : GalQ2}
    (h₁ : g • A₁ = A₁) (h₂ : g • A₂ = A₂) :
    Kummer.kummerCocycleFun (β₁ * β₂) g
      = Kummer.kummerCocycleFun β₁ g + Kummer.kummerCocycleFun β₂ g := by
  have eq1 : ∀ {γ : ℚ̄₂}, γ ≠ 0 → γ ≠ -γ := fun h => ne_neg_of_ne_zero h
  have hne1 : ∀ {γ : ℚ̄₂} {x : GalQ2}, γ ≠ 0 → x • γ = -γ →
      Kummer.kummerCocycleFun γ x = 1 :=
    fun hγ hx => if_neg (fun e => eq1 hγ (e.symm.trans hx))
  have hsmul : ∀ (x : GalQ2) (a b : ℚ̄₂),
      x • (a * b) = (x • a) * (x • b) := fun x a b => by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_mul]
  rcases two_values_of_fixed hsq₁ h₁ with h1' | h1' <;>
    rcases two_values_of_fixed hsq₂ h₂ with h2' | h2'
  · rw [Kummer.kummerCocycleFun_eq0 h1', Kummer.kummerCocycleFun_eq0 h2',
      Kummer.kummerCocycleFun_eq0 (by rw [hsmul, h1', h2'])]
    decide
  · rw [Kummer.kummerCocycleFun_eq0 h1', hne1 hβ₂ h2',
      hne1 (mul_ne_zero hβ₁ hβ₂) (by rw [hsmul, h1', h2']; ring)]
    decide
  · rw [hne1 hβ₁ h1', Kummer.kummerCocycleFun_eq0 h2',
      hne1 (mul_ne_zero hβ₁ hβ₂) (by rw [hsmul, h1', h2']; ring)]
    decide
  · rw [hne1 hβ₁ h1', hne1 hβ₂ h2',
      Kummer.kummerCocycleFun_eq0 (by rw [hsmul, h1', h2']; ring)]
    decide

variable {Θ : Type} [Group Θ] [TopologicalSpace Θ] [IsTopologicalGroup Θ]
  [DistribMulAction Θ (ZMod 2)] [ContinuousSMul Θ (ZMod 2)]

omit [IsTopologicalGroup Θ] [ContinuousSMul Θ (ZMod 2)] in
/-- **The anchored Kummer cocycle lies in `Z¹(Θ, 𝔽₂)`** — the anchored form of
`GQ2.DeepPart.kummerRestrict_mem_Z1`. -/
theorem kummerAnc_mem_Z1 (anc : ContinuousMonoidHom Θ GalQ2) {A β : ℚ̄₂}
    (hsq : β ^ 2 = A) (hβ0 : β ≠ 0) (hAfix : ∀ g ∈ ancSubgroup anc, g • A = A) :
    (fun n : Θ => Kummer.kummerCocycleFun β (anc n)) ∈ Z1 Θ (ZMod 2) := by
  refine mem_Z1_iff.mpr ⟨?_, fun n m => ?_⟩
  · exact (Kummer.kummerCocycleFun_continuous β).comp anc.continuous_toFun
  · show Kummer.kummerCocycleFun β (anc (n * m))
      = Kummer.kummerCocycleFun β (anc n) + n • Kummer.kummerCocycleFun β (anc m)
    rw [smul_zmodTwo, map_mul,
      kcf_hom_of_fixed hsq hβ0 (hAfix _ (mem_ancSubgroup anc n)) (hAfix _ (mem_ancSubgroup anc m))]

end KummerBricks

end GQ2.Dyadic
