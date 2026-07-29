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

/-! ## §2 Deep and mid Kummer classes at an anchor

The `Γ`-side twins of `GQ2.LocalKummer.deepClasses` (`GQ2/LocalKummer.lean`),
`GQ2.deepClassesSubgroup` (`GQ2/AdmissibleCount.lean`) and `GQ2.midClassesSubgroup`
(`GQ2/DeepDuality.lean`): the *units* are the `ℚ₂` predicates at the anchored subgroup, only the
*classes* move to `H¹(Θ, 𝔽₂)`. -/

section DeepClasses

variable {Θ : Type} [Group Θ] [TopologicalSpace Θ] [IsTopologicalGroup Θ]
  [DistribMulAction Θ (ZMod 2)] [ContinuousSMul Θ (ZMod 2)]

/-- **The deep Kummer classes at an anchor** — `GQ2.LocalKummer.deepClasses` retyped: classes of
anchored Kummer cocycles of units that are deep for the anchored subgroup. -/
def deepClassesAt (anc : ContinuousMonoidHom Θ GalQ2) : Set (H1 Θ (ZMod 2)) :=
  {ξ | ∃ A β : ℚ̄₂, SectionSix.IsDeepUnit (ancSubgroup anc) A ∧ β ^ 2 = A ∧ β ≠ 0 ∧
    H1ofFun Θ (fun n : Θ => Kummer.kummerCocycleFun β (anc n)) = ξ}

/-- **The mid Kummer classes at an anchor** — the `≤`-relaxation, mirroring
`GQ2.midClassesSubgroup`'s carrier. -/
def midClassesAt (anc : ContinuousMonoidHom Θ GalQ2) : Set (H1 Θ (ZMod 2)) :=
  {ξ | ∃ A β : ℚ̄₂, IsMidUnit (ancSubgroup anc) A ∧ β ^ 2 = A ∧ β ≠ 0 ∧
    H1ofFun Θ (fun n : Θ => Kummer.kummerCocycleFun β (anc n)) = ξ}

variable (anc : ContinuousMonoidHom Θ GalQ2)

/-- The trivial unit `A = 1` gives the zero class (used for `0 ∈ deepClasses/midClasses`). -/
theorem kummerAnc_one_eq_zero :
    H1ofFun Θ (fun n : Θ => Kummer.kummerCocycleFun (1 : ℚ̄₂) (anc n)) = 0 := by
  have hk1 : (fun n : Θ => Kummer.kummerCocycleFun (1 : ℚ̄₂) (anc n)) = 0 := by
    funext n
    exact Kummer.kummerCocycleFun_eq0 (by rw [AlgEquiv.smul_def, map_one])
  rw [hk1, H1ofFun_of_mem (zero_mem _)]
  exact map_zero (H1mk Θ (ZMod 2))

omit [IsTopologicalGroup Θ] [ContinuousSMul Θ (ZMod 2)] in
/-- `H¹(Θ, 𝔽₂)` is 2-torsion, so negation is the identity on it. -/
theorem h1_zmodTwo_add_self (x : H1 Θ (ZMod 2)) : x + x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      funext g
      show z.1 g + z.1 g = 0
      have : ∀ a : ZMod 2, a + a = 0 := by decide
      exact this _
    show H1mk Θ (ZMod 2) z + H1mk Θ (ZMod 2) z = 0
    rw [← map_add, hz, map_zero]

/-- Deep units are closed under products (the `ℚ₂` computation of `GQ2.deepClassesSubgroup`,
restated at an arbitrary subgroup so both `Θ`-side subgroup proofs can share it). -/
theorem isDeepUnit_mul {N : Subgroup GalQ2} {A₁ A₂ : ℚ̄₂}
    (h₁ : SectionSix.IsDeepUnit N A₁) (h₂ : SectionSix.IsDeepUnit N A₂) :
    SectionSix.IsDeepUnit N (A₁ * A₂) := by
  obtain ⟨hA₁0, hA₁fix, b₁, hb₁fix, hA₁eq, hb₁⟩ := h₁
  obtain ⟨hA₂0, hA₂fix, b₂, hb₂fix, hA₂eq, hb₂⟩ := h₂
  have h2le : ‖(2 : ℚ̄₂)‖ ≤ 1 := by simpa using IsUltrametricDist.norm_natCast_le_one ℚ̄₂ 2
  refine ⟨mul_ne_zero hA₁0 hA₂0, fun g hg => ?_, b₁ + b₂ + 2 * b₁ * b₂, fun g hg => ?_,
    by rw [hA₁eq, hA₂eq]; ring, ?_⟩
  · rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      hA₁fix g hg, hA₂fix g hg]
  · rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
      ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hb₁fix g hg, hb₂fix g hg]
  · have hprod : ‖(2 : ℚ̄₂) * b₁ * b₂‖ < 1 := by
      rw [norm_mul, norm_mul]
      calc ‖(2 : ℚ̄₂)‖ * ‖b₁‖ * ‖b₂‖
          ≤ 1 * ‖b₁‖ * ‖b₂‖ := by gcongr
        _ = ‖b₁‖ * ‖b₂‖ := by ring
        _ ≤ ‖b₁‖ * 1 := mul_le_mul_of_nonneg_left hb₂.le (norm_nonneg b₁)
        _ = ‖b₁‖ := mul_one _
        _ < 1 := hb₁
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [max_lt_iff]
    refine ⟨lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_, hprod⟩
    rw [max_lt_iff]
    exact ⟨hb₁, hb₂⟩

/-- Mid units are closed under products (the `≤`-mirror of `isDeepUnit_mul`). -/
theorem isMidUnit_mul {N : Subgroup GalQ2} {A₁ A₂ : ℚ̄₂}
    (h₁ : IsMidUnit N A₁) (h₂ : IsMidUnit N A₂) : IsMidUnit N (A₁ * A₂) := by
  obtain ⟨hA₁0, hA₁fix, b₁, hb₁fix, hA₁eq, hb₁⟩ := h₁
  obtain ⟨hA₂0, hA₂fix, b₂, hb₂fix, hA₂eq, hb₂⟩ := h₂
  have h2le : ‖(2 : ℚ̄₂)‖ ≤ 1 := by simpa using IsUltrametricDist.norm_natCast_le_one ℚ̄₂ 2
  refine ⟨mul_ne_zero hA₁0 hA₂0, fun g hg => ?_, b₁ + b₂ + 2 * b₁ * b₂, fun g hg => ?_,
    by rw [hA₁eq, hA₂eq]; ring, ?_⟩
  · rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
      hA₁fix g hg, hA₂fix g hg]
  · rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
      ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hb₁fix g hg, hb₂fix g hg]
  · have hprod : ‖(2 : ℚ̄₂) * b₁ * b₂‖ ≤ 1 := by
      rw [norm_mul, norm_mul]
      calc ‖(2 : ℚ̄₂)‖ * ‖b₁‖ * ‖b₂‖
          ≤ 1 * ‖b₁‖ * ‖b₂‖ := by gcongr
        _ = ‖b₁‖ * ‖b₂‖ := by ring
        _ ≤ ‖b₁‖ * 1 := mul_le_mul_of_nonneg_left hb₂ (norm_nonneg b₁)
        _ = ‖b₁‖ := mul_one _
        _ ≤ 1 := hb₁
    refine le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_
    rw [max_le_iff]
    refine ⟨le_trans (IsUltrametricDist.norm_add_le_max _ _) ?_, hprod⟩
    rw [max_le_iff]
    exact ⟨hb₁, hb₂⟩

/-- The anchored Kummer class of a product of two anchored-fixed units is the sum of the
classes. -/
theorem kummerAnc_class_mul {A₁ A₂ β₁ β₂ : ℚ̄₂} (hsq₁ : β₁ ^ 2 = A₁) (hsq₂ : β₂ ^ 2 = A₂)
    (hβ₁ : β₁ ≠ 0) (hβ₂ : β₂ ≠ 0)
    (hA₁fix : ∀ g ∈ ancSubgroup anc, g • A₁ = A₁) (hA₂fix : ∀ g ∈ ancSubgroup anc, g • A₂ = A₂) :
    H1ofFun Θ (fun n : Θ => Kummer.kummerCocycleFun (β₁ * β₂) (anc n))
      = H1ofFun Θ (fun n : Θ => Kummer.kummerCocycleFun β₁ (anc n))
        + H1ofFun Θ (fun n : Θ => Kummer.kummerCocycleFun β₂ (anc n)) := by
  have hsplit : (fun n : Θ => Kummer.kummerCocycleFun (β₁ * β₂) (anc n))
      = (fun n : Θ => Kummer.kummerCocycleFun β₁ (anc n))
        + fun n : Θ => Kummer.kummerCocycleFun β₂ (anc n) := by
    funext n
    exact kcf_mul_of_fixedAt hsq₁ hsq₂ hβ₁ hβ₂ (hA₁fix _ (mem_ancSubgroup anc n))
      (hA₂fix _ (mem_ancSubgroup anc n))
  rw [hsplit]
  exact DeepPart.H1ofFun_add (kummerAnc_mem_Z1 anc hsq₁ hβ₁ hA₁fix)
    (kummerAnc_mem_Z1 anc hsq₂ hβ₂ hA₂fix)

/-- **The deep classes form an additive subgroup** — `GQ2.deepClassesSubgroup` retyped. -/
def deepClassesSubgroupAt : AddSubgroup (H1 Θ (ZMod 2)) where
  carrier := deepClassesAt anc
  zero_mem' :=
    ⟨1, 1, ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one], 0,
      fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_lt_one⟩,
      one_pow 2, one_ne_zero, kummerAnc_one_eq_zero anc⟩
  add_mem' := by
    rintro ξ η ⟨A₁, β₁, hd₁, hsq₁, hne₁, rfl⟩ ⟨A₂, β₂, hd₂, hsq₂, hne₂, rfl⟩
    exact ⟨A₁ * A₂, β₁ * β₂, isDeepUnit_mul hd₁ hd₂, by rw [mul_pow, hsq₁, hsq₂],
      mul_ne_zero hne₁ hne₂,
      kummerAnc_class_mul anc hsq₁ hsq₂ hne₁ hne₂ hd₁.2.1 hd₂.2.1⟩
  neg_mem' := by
    intro x hx
    rwa [neg_eq_of_add_eq_zero_left (h1_zmodTwo_add_self x)]

/-- **The mid classes form an additive subgroup** — `GQ2.midClassesSubgroup` retyped. -/
def midClassesSubgroupAt : AddSubgroup (H1 Θ (ZMod 2)) where
  carrier := midClassesAt anc
  zero_mem' :=
    ⟨1, 1, ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one], 0,
      fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_le_one⟩,
      one_pow 2, one_ne_zero, kummerAnc_one_eq_zero anc⟩
  add_mem' := by
    rintro ξ η ⟨A₁, β₁, hd₁, hsq₁, hne₁, rfl⟩ ⟨A₂, β₂, hd₂, hsq₂, hne₂, rfl⟩
    exact ⟨A₁ * A₂, β₁ * β₂, isMidUnit_mul hd₁ hd₂, by rw [mul_pow, hsq₁, hsq₂],
      mul_ne_zero hne₁ hne₂,
      kummerAnc_class_mul anc hsq₁ hsq₂ hne₁ hne₂ hd₁.2.1 hd₂.2.1⟩
  neg_mem' := by
    intro x hx
    rwa [neg_eq_of_add_eq_zero_left (h1_zmodTwo_add_self x)]

@[simp] theorem mem_deepClassesSubgroupAt {ξ : H1 Θ (ZMod 2)} :
    ξ ∈ deepClassesSubgroupAt anc ↔ ξ ∈ deepClassesAt anc := Iff.rfl

@[simp] theorem mem_midClassesSubgroupAt {ξ : H1 Θ (ZMod 2)} :
    ξ ∈ midClassesSubgroupAt anc ↔ ξ ∈ midClassesAt anc := Iff.rfl

/-- Deep classes are mid classes (`U_{e+1} ⊆ U_e`). -/
theorem deepClassesAt_subset_midClassesAt : deepClassesAt anc ⊆ midClassesAt anc := by
  rintro ξ ⟨A, β, ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩, hsq, hβ0, rfl⟩
  exact ⟨A, β, ⟨hA0, hAfix, b, hbfix, hAeq, hb.le⟩, hsq, hβ0, rfl⟩

end DeepClasses

/-! ## §3 The deep half `X₊` (packet Def. 6.11(c), Prop. 6.12)

`GQ2.SectionSix.deepPart` (`GQ2/SectionSix.lean`) and `GQ2.DeepPart.deepPartSubgroup`
(`GQ2/DeepPart/Q0locLayer.lean`) retyped: the classes of `H¹(Γ, V)` all of whose scalar Kummer
coordinates over the splitting group `N_K = ker ρ` are deep. -/

section DeepPart

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction Γ V] [DistribMulAction C V]

/-- **The scalar restriction map** at a general ambient — `GQ2.LocalKummer.phiRes` retyped. -/
noncomputable def phiResK (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V) (φ : V →+ ZMod 2) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
    (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => φ ((Quotient.out x).1 (n : Γ)))

omit [DistribMulAction C V] in
theorem phiResK_def (ρ : ContinuousMonoidHom Γ C) (x : H1 Γ V) (φ : V →+ ZMod 2) :
    phiResK ρ x φ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
      (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => φ ((Quotient.out x).1 (n : Γ))) := rfl

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- `H1mk` of the canonical representative is the identity (the `Γ`-side `H1mk_out`). -/
theorem h1mk_outK (y : H1 Γ V) : H1mk Γ V (Quotient.out y) = y := Quotient.out_eq y

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- A `Z¹`-cocycle whose class vanishes dies pointwise on `ker ρ` — `GQ2.DeepPart`'s
`vanish_on_ker_of_H1mk_eq_zero` retyped. -/
theorem vanish_on_ker_of_H1mk_eq_zeroK (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    {d : ↥(Z1 Γ V)} (hd : H1mk Γ V d = 0) (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    d.1 (n : Γ) = 0 := by
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hd
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨w₀, hw₀⟩ := hmem
  have hn := congrFun hw₀ (n : Γ)
  rw [← hn]
  show (n : Γ) • w₀ - w₀ = 0
  rw [hρ, show ρ (n : Γ) = 1 from n.2, one_smul, sub_self]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The `φ`-coordinate of a cocycle restricted to `ker ρ` lies in `Z¹(ker ρ, 𝔽₂)` —
`GQ2.DeepPart.phiRestrict_mem_Z1` retyped. -/
theorem phiRestrict_mem_Z1K (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (b : ↥(Z1 Γ V)) (φ : V →+ ZMod 2) :
    (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => φ (b.1 (n : Γ)))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine mem_Z1_iff.mpr ⟨?_, fun n m => ?_⟩
  · exact (continuous_of_discreteTopology (f := fun v : V => φ v)).comp
      (hbc.comp continuous_subtype_val)
  · show φ (b.1 ((n * m : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) : Γ))
      = φ (b.1 (n : Γ)) + n • φ (b.1 (m : Γ))
    rw [smul_zmodTwo, show ((n * m : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) : Γ) = (n : Γ) * (m : Γ)
      from rfl, hb (n : Γ) (m : Γ), hρ, show ρ (n : Γ) = 1 from n.2, one_smul, map_add]

/-- **The deep half `X₊`** (packet Def. 6.11(c), `GQ2.SectionSix.deepPart` retyped): the classes
`x ∈ H¹(Γ, V)` all of whose scalar Kummer coordinates over `N_K = ker ρ` are Kummer classes of
units that are deep for the **anchored** subgroup `ancSubgroup (kerAnc anc ρ)`. -/
def deepPartK (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C) :
    Set (H1 Γ V) :=
  {x | ∀ φ : V →+ ZMod 2,
    ∃ (A β : ℚ̄₂) (_ : SectionSix.IsDeepUnit (ancSubgroup (kerAnc anc ρ)) A) (_ : β ^ 2 = A)
      (_ : β ≠ 0),
      H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n))
        = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
          (fun n => φ ((Quotient.out x).1 (n : Γ)))}

omit [DistribMulAction C V] in
/-- **The `deepPart` bridge**, definitional half — `GQ2.LocalKummer.mem_deepPart_iff` retyped:
membership in the deep half is exactly "every scalar restriction is a deep Kummer class at the
splitting group's anchor". -/
theorem mem_deepPartK_iff (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (x : H1 Γ V) :
    x ∈ deepPartK (V := V) anc ρ ↔ ∀ φ : V →+ ZMod 2,
      phiResK ρ x φ ∈ deepClassesAt (kerAnc anc ρ) := by
  constructor
  · intro hx φ
    obtain ⟨A, β, hdeep, hsq, hβ0, heq⟩ := hx φ
    exact ⟨A, β, hdeep, hsq, hβ0, heq⟩
  · intro hx φ
    obtain ⟨A, β, hdeep, hsq, hβ0, heq⟩ := hx φ
    exact ⟨A, β, hdeep, hsq, hβ0, heq⟩

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **`H¹` of an exponent-2 module has exponent 2** — `GQ2.DeepPart.h1_add_self` retyped. -/
theorem h1_add_selfK (hV2 : ∀ v : V, v + v = 0) (x : H1 Γ V) : x + x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      funext g
      exact hV2 _
    show H1mk Γ V z + H1mk Γ V z = 0
    rw [← map_add, hz, map_zero]

/-- **Prop. 6.12, subgroup clause: the deep half `X₊` is an additive subgroup** of `H¹(Γ, V)` —
`GQ2.DeepPart.deepPartSubgroup` retyped. -/
def deepPartSubgroupK (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0) :
    AddSubgroup (H1 Γ V) where
  carrier := deepPartK (V := V) anc ρ
  zero_mem' := by
    intro φ
    refine ⟨1, 1, ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one],
      0, fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_lt_one⟩,
      one_pow 2, one_ne_zero, ?_⟩
    congr 1
    funext n
    rw [Kummer.kummerCocycleFun_eq0 (by rw [AlgEquiv.smul_def, map_one])]
    have hv := vanish_on_ker_of_H1mk_eq_zeroK ρ hρ (h1mk_outK (0 : H1 Γ V)) n
    rw [hv, map_zero]
  add_mem' := by
    intro x y hx hy φ
    obtain ⟨A₁, β₁, hd₁, hsq₁, hne₁, heq₁⟩ := hx φ
    obtain ⟨A₂, β₂, hd₂, hsq₂, hne₂, heq₂⟩ := hy φ
    refine ⟨A₁ * A₂, β₁ * β₂, isDeepUnit_mul hd₁ hd₂, by rw [mul_pow, hsq₁, hsq₂],
      mul_ne_zero hne₁ hne₂, ?_⟩
    -- LHS: the Kummer class of the product splits (anchored multiplicativity)
    rw [kummerAnc_class_mul (kerAnc anc ρ) hsq₁ hsq₂ hne₁ hne₂ hd₁.2.1 hd₂.2.1, heq₁, heq₂]
    -- RHS: `out(x+y) = out x + out y` on `ker ρ`
    have hRHS : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) =>
        φ ((Quotient.out (x + y)).1 (n : Γ)))
        = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => φ ((Quotient.out x).1 (n : Γ)))
          + fun n : ↥(ρ.toMonoidHom.ker : Subgroup Γ) => φ ((Quotient.out y).1 (n : Γ)) := by
      funext n
      have hd0 : H1mk Γ V (Quotient.out (x + y) - (Quotient.out x + Quotient.out y)) = 0 := by
        rw [map_sub, map_add, h1mk_outK, h1mk_outK, h1mk_outK, sub_self]
      have hv := vanish_on_ker_of_H1mk_eq_zeroK ρ hρ hd0 n
      have hpt : (Quotient.out (x + y)).1 (n : Γ)
          = (Quotient.out x).1 (n : Γ) + (Quotient.out y).1 (n : Γ) := by
        have hexp : (Quotient.out (x + y) - (Quotient.out x + Quotient.out y) : ↥(Z1 Γ V)).1 (n : Γ)
            = (Quotient.out (x + y)).1 (n : Γ)
              - ((Quotient.out x).1 (n : Γ) + (Quotient.out y).1 (n : Γ)) := by
          show (Quotient.out (x + y)).1 (n : Γ)
              - ((Quotient.out x).1 + (Quotient.out y).1) (n : Γ) = _
          rw [Pi.add_apply]
        rw [hexp] at hv
        exact sub_eq_zero.mp hv
      show φ ((Quotient.out (x + y)).1 (n : Γ)) = _
      rw [hpt, map_add]
      rfl
    rw [hRHS, DeepPart.H1ofFun_add (phiRestrict_mem_Z1K ρ hρ _ φ) (phiRestrict_mem_Z1K ρ hρ _ φ)]
  neg_mem' := by
    intro x hx
    rwa [neg_eq_of_add_eq_zero_left (h1_add_selfK hV2 x)]

@[simp] theorem mem_deepPartSubgroupK (anc : ContinuousMonoidHom Γ GalQ2)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) {x : H1 Γ V} :
    x ∈ deepPartSubgroupK (V := V) anc ρ hρ hV2 ↔ x ∈ deepPartK (V := V) anc ρ := Iff.rfl

end DeepPart

end GQ2.Dyadic
