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

open GQ2 GQ2.ContCoh GQ2.LocalKummer GQ2.QuadraticFp2

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
/-- `H¹(Θ, 𝔽₂)` is 2-torsion, so negation is the identity on it.  (`_dp` suffix: dedup against
any `GQ2.Dyadic` twin from a sibling LG file at merge.) -/
theorem h1_zmodTwo_add_self_dp (x : H1 Θ (ZMod 2)) : x + x = 0 := by
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
    rwa [neg_eq_of_add_eq_zero_left (h1_zmodTwo_add_self_dp x)]

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
    rwa [neg_eq_of_add_eq_zero_left (h1_zmodTwo_add_self_dp x)]

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
/-- **`H¹` of an exponent-2 module has exponent 2** — `GQ2.DeepPart.h1_add_self` retyped.
(`_dp` suffix: dedup against any `GQ2.Dyadic` twin from a sibling LG file at merge.) -/
theorem h1_add_self_dp (hV2 : ∀ v : V, v + v = 0) (x : H1 Γ V) : x + x = 0 := by
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
    rwa [neg_eq_of_add_eq_zero_left (h1_add_self_dp hV2 x)]

@[simp] theorem mem_deepPartSubgroupK (anc : ContinuousMonoidHom Γ GalQ2)
    (ρ : ContinuousMonoidHom Γ C) (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) {x : H1 Γ V} :
    x ∈ deepPartSubgroupK (V := V) anc ρ hρ hV2 ↔ x ∈ deepPartK (V := V) anc ρ := Iff.rfl

end DeepPart

/-! ## §4 The (H3) isotropy splice at a general local source

`GQ2/DeepDualityK.lean` :317–:578 retyped (memo §2 row 3; deferred from LG2 by design because it
is Kummer-theoretic and its home is the deep-unit package).  The `ℚ₂` file splices the Tier-5
eq.-(94) facts (`GQ2.LocalKummer.cup_deepClasses`, `GQ2.cup_midClasses_deepClasses`, both stated
over `k.fixingSubgroup ≤ G_ℚ₂`) to `pairingK` across two boundaries: the **group view** taken
pointwise, and the **coefficient bridge** `𝔽₂ ≃+ μ₂`.

Under the anchoring convention of the module docstring the first boundary is exactly the anchor:
the `ℚ₂` file's `hker : x ∈ ker ρ ↔ x ∈ k.fixingSubgroup` becomes
`hker : x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup`, and the identity inclusion
`kerToFixing` becomes `kerToFixingAt`, `n ↦ anc n`.  Again **no subgroup-equality cast is ever
formed**, and the two `k`-side inputs are consumed verbatim. -/

section IsotropySplice

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

/-- The identity-on-elements inclusion `↥(ker ρ) → ↥k.fixingSubgroup` supplied by the pointwise
anchoring hypothesis — `GQ2.kerToFixing` retyped through the anchor. -/
noncomputable def kerToFixingAt (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) : ↥k.fixingSubgroup :=
  ⟨kerAnc anc ρ n, (hker _).mp (mem_ancSubgroup (kerAnc anc ρ) n)⟩

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] in
theorem kerToFixingAt_mul (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (n m : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    kerToFixingAt anc ρ k hker (n * m)
      = kerToFixingAt anc ρ k hker n * kerToFixingAt anc ρ k hker m :=
  Subtype.ext (by
    show kerAnc anc ρ (n * m) = (kerAnc anc ρ n) * (kerAnc anc ρ m)
    rw [map_mul])

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] in
theorem continuous_kerToFixingAt (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup) :
    Continuous (kerToFixingAt anc ρ k hker) :=
  Continuous.subtype_mk (kerAnc anc ρ).continuous_toFun _

/-- `GQ2.SectionSix.IsDeepUnit` is antitone in the subgroup (only the two fixedness fields mention
it) — the public copy of `GQ2`'s private `isDeepUnit_of_le`. -/
theorem isDeepUnit_of_le' {N N' : Subgroup GalQ2} (hle : ∀ x ∈ N', x ∈ N) {A : ℚ̄₂}
    (hA : SectionSix.IsDeepUnit N A) : SectionSix.IsDeepUnit N' A := by
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hA
  exact ⟨hA0, fun g hg => hAfix g (hle g hg), b, fun g hg => hbfix g (hle g hg), hAeq, hb⟩

/-- `GQ2.IsMidUnit` is antitone in the subgroup (the `≤`-mirror). -/
theorem isMidUnit_of_le' {N N' : Subgroup GalQ2} (hle : ∀ x ∈ N', x ∈ N) {A : ℚ̄₂}
    (hA : IsMidUnit N A) : IsMidUnit N' A := by
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hA
  exact ⟨hA0, fun g hg => hAfix g (hle g hg), b, fun g hg => hbfix g (hle g hg), hAeq, hb⟩

variable (D : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup Γ) 2)

/-- **The shared witness-transport + `inv`-kill tail** of the two isotropy splices — the retype of
`GQ2.pairingK_kummer_eq_zero`: once the `k`-side cup of the two anchored Kummer classes vanishes,
the `pairingK`-value over `ker ρ` vanishes.  The `k`-side coboundary witness transports through
`kerToFixingAt` and the `𝔽₂ ≃+ μ₂` bridge, and the injective `D.inv` kills the class. -/
theorem pairingK_kummer_eq_zero_K (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    {A B β δ : ℚ̄₂} (hsqA : β ^ 2 = A) (hβ0 : β ≠ 0)
    (hAfix : ∀ g ∈ ancSubgroup (kerAnc anc ρ), g • A = A)
    (hsqB : δ ^ 2 = B) (hδ0 : δ ≠ 0)
    (hBfix : ∀ g ∈ ancSubgroup (kerAnc anc ρ), g • B = B)
    (hcup0 : (H1ofFun ↥k.fixingSubgroup fun n => Kummer.kummerCocycleFun β (n : GalQ2))
      ⌣[htriv] (H1ofFun ↥k.fixingSubgroup fun n => Kummer.kummerCocycleFun δ (n : GalQ2)) = 0) :
    pairingK ρ D
      (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) fun n =>
        Kummer.kummerCocycleFun β (kerAnc anc ρ n))
      (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) fun n =>
        Kummer.kummerCocycleFun δ (kerAnc anc ρ n)) = 0 := by
  -- anchored Kummer cocycles on the `Γ`-side, restricted Kummer cocycles on the `k`-side
  have hZ1β := kummerAnc_mem_Z1 (kerAnc anc ρ) hsqA hβ0 hAfix
  have hZ1δ := kummerAnc_mem_Z1 (kerAnc anc ρ) hsqB hδ0 hBfix
  have hZ1kβ : (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqA hβ0 (fun g hg => hAfix g ((hker g).mpr hg))
  have hZ1kδ : (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δ (n : GalQ2))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqB hδ0 (fun g hg => hBfix g ((hker g).mpr hg))
  -- the `k`-side vanishing in mk-form, and its coboundary witness
  rw [H1ofFun_of_mem hZ1kβ, H1ofFun_of_mem hZ1kδ] at hcup0
  have hB2k : cup11Fun (AddMonoidHom.mul)
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δ (n : GalQ2))
      ∈ B2 ↥k.fixingSubgroup (ZMod 2) := by
    have h0 : H2mk ↥k.fixingSubgroup (ZMod 2)
        ⟨cup11Fun (AddMonoidHom.mul)
            (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun β (n : GalQ2))
            (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δ (n : GalQ2)),
          cup11_mem_Z2 (AddMonoidHom.mul) (fun g m n => by rw [htriv, htriv, htriv])
            ⟨_, hZ1kβ⟩ ⟨_, hZ1kδ⟩⟩ = 0 := hcup0
    exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  obtain ⟨ψ, hψc, hψeq⟩ := hB2k
  -- kill `D.inv`; reduce to `B²`-membership of the `μ₂`-valued cup cocycle over `ker ρ`
  have hiv : ∀ W : H2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (MuN 2), D.inv W = 0 ↔ W = 0 := fun _ =>
    map_eq_zero_iff _ D.inv.injective
  rw [H1ofFun_of_mem hZ1β, H1ofFun_of_mem hZ1δ]
  show D.inv
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
        (H1congr zmodMuDualEquiv zmodMuDualEquiv_equivariant
          (H1mk _ _ ⟨_, hZ1β⟩)) (H1mk _ _ ⟨_, hZ1δ⟩)) = 0
  rw [H1congr_mk, cup11_mk_mk, hiv]
  refine (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  -- the transported witness: `μ₂-bridge ∘ ψ ∘ kerToFixingAt`
  refine AddSubgroup.mem_map.mpr
    ⟨fun n => LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixingAt anc ρ k hker n)),
      mem_C1_iff.mpr (continuous_of_discreteTopology.comp
        ((mem_C1_iff.mp hψc).comp (continuous_kerToFixingAt anc ρ k hker))), ?_⟩
  funext p
  -- the `smul` trap: at a general `Γ` neither the `𝔽₂`- nor the `μ₂`-action is `rfl`-trivial, so
  -- both are collapsed explicitly (`smul_zmodTwo`/`smul_muTwo`, `GQ2/Dyadic/LocalGauss/Q0.lean`)
  have hpair : ∀ a b : ZMod 2, muDualPairing 2 (ZMod 2) (zmodMuDualEquiv a) b
      = LocalLiftingDuality.muNTwoEquiv.symm (a * b) := fun _ _ => rfl
  show p.1 • LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixingAt anc ρ k hker p.2))
      - LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixingAt anc ρ k hker (p.1 * p.2)))
      + LocalLiftingDuality.muNTwoEquiv.symm (ψ (kerToFixingAt anc ρ k hker p.1))
    = muDualPairing 2 (ZMod 2)
        (zmodMuDualEquiv (Kummer.kummerCocycleFun β (kerAnc anc ρ p.1)))
        (p.1 • Kummer.kummerCocycleFun δ (kerAnc anc ρ p.2))
  rw [smul_zmodTwo, hpair, smul_muTwo, kerToFixingAt_mul, ← map_sub, ← map_add]
  congr 1
  calc ψ (kerToFixingAt anc ρ k hker p.2)
      - ψ (kerToFixingAt anc ρ k hker p.1 * kerToFixingAt anc ρ k hker p.2)
      + ψ (kerToFixingAt anc ρ k hker p.1)
      = (kerToFixingAt anc ρ k hker p.1) • ψ (kerToFixingAt anc ρ k hker p.2)
        - ψ (kerToFixingAt anc ρ k hker p.1 * kerToFixingAt anc ρ k hker p.2)
        + ψ (kerToFixingAt anc ρ k hker p.1) := by rw [htriv]
    _ = Kummer.kummerCocycleFun β (kerAnc anc ρ p.1)
          * ((kerToFixingAt anc ρ k hker p.1)
              • Kummer.kummerCocycleFun δ (kerAnc anc ρ p.2)) :=
        congrFun hψeq (kerToFixingAt anc ρ k hker p.1, kerToFixingAt anc ρ k hker p.2)
    _ = Kummer.kummerCocycleFun β (kerAnc anc ρ p.1)
          * Kummer.kummerCocycleFun δ (kerAnc anc ρ p.2) := by rw [htriv]

/-- **(H3) Isotropy of the deep classes under the `K`-level pairing** at a general local source —
`GQ2.pairingK_deep_deep` retyped.  Two deep Kummer classes pair to zero. -/
theorem pairingK_deep_deep_K (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    {ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)}
    (hξ : ξ ∈ deepClassesSubgroupAt (kerAnc anc ρ))
    (hη : η ∈ deepClassesSubgroupAt (kerAnc anc ρ)) :
    pairingK ρ D ξ η = 0 := by
  obtain ⟨A, β, hdA, hsqA, hβ0, rfl⟩ := hξ
  obtain ⟨B, δ, hdB, hsqB, hδ0, rfl⟩ := hη
  exact pairingK_kummer_eq_zero_K anc ρ D k htriv hker hsqA hβ0 hdA.2.1 hsqB hδ0 hdB.2.1
    (LocalKummer.cup_deepClasses k htriv
      ⟨A, β, isDeepUnit_of_le' (fun g hg => (hker g).mpr hg) hdA, hsqA, hβ0, rfl⟩
      ⟨B, δ, isDeepUnit_of_le' (fun g hg => (hker g).mpr hg) hdB, hsqB, hδ0, rfl⟩)

/-- **Mid ⟂ deep under the `K`-level pairing** at a general local source —
`GQ2.pairingK_mid_deep` retyped; the "easy half" of (H4)'s sharpness `Deep^⊥ = E`. -/
theorem pairingK_mid_deep_K (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    {ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)}
    (hξ : ξ ∈ midClassesSubgroupAt (kerAnc anc ρ))
    (hη : η ∈ deepClassesSubgroupAt (kerAnc anc ρ)) :
    pairingK ρ D ξ η = 0 := by
  obtain ⟨A, β, hdA, hsqA, hβ0, rfl⟩ := hξ
  obtain ⟨B, δ, hdB, hsqB, hδ0, rfl⟩ := hη
  exact pairingK_kummer_eq_zero_K anc ρ D k htriv hker hsqA hβ0 hdA.2.1 hsqB hδ0 hdB.2.1
    (cup_midClasses_deepClasses k htriv
      ⟨A, β, isMidUnit_of_le' (fun g hg => (hker g).mpr hg) hdA, hsqA, hβ0, rfl⟩
      ⟨B, δ, isDeepUnit_of_le' (fun g hg => (hker g).mpr hg) hdB, hsqB, hδ0, rfl⟩)

/-- **The `hiso` input of the abstract `hduality` engine in `pairPerp` form**: `Deep ≤ Deep^⊥`
under `pairingK` — `GQ2.deepClassesSubgroup_le_pairPerp_pairingK` retyped. -/
theorem deepClassesSubgroupAt_le_pairPerp_pairingK
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup) :
    deepClassesSubgroupAt (kerAnc anc ρ)
      ≤ pairPerp (pairingK ρ D) (deepClassesSubgroupAt (kerAnc anc ρ)) :=
  fun _ hξ => (mem_pairPerp_iff _ _ _).mpr fun _ hη =>
    pairingK_deep_deep_K anc ρ D k htriv hker hξ hη

/-- **The "easy half" of (H4) in `pairPerp` form**: `E = midClasses ≤ Deep^⊥` under `pairingK` —
`GQ2.midClassesSubgroup_le_pairPerp_pairingK` retyped. -/
theorem midClassesSubgroupAt_le_pairPerp_pairingK
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup) :
    midClassesSubgroupAt (kerAnc anc ρ)
      ≤ pairPerp (pairingK ρ D) (deepClassesSubgroupAt (kerAnc anc ρ)) :=
  fun _ hξ => (mem_pairPerp_iff _ _ _).mpr fun _ hη =>
    pairingK_mid_deep_K anc ρ D k htriv hker hξ hη

end IsotropySplice

/-! ## §5 Projective inflation–restriction (packet Def. 6.11(a))

`GQ2.LocalKummer.InflationVanishes` (`GQ2/LocalKummer.lean` :304) and `FamiliesExtend` (:898)
retyped, with their discharges.

**Binding attribution correction** (packet §12 over-attributes both clauses to Lemma 6.11
projectivity; adopted at AX5): `InflationVanishes` is discharged by **coprime averaging** over an
odd normal subgroup with no fixed vectors — `inflationVanishes_of_oddNormalK`, which is pure
2-torsion module algebra and mentions no projectivity.  Only `FamiliesExtend` uses Lemma 6.11.

The `ℚ₂` instantiation `GQ2.LocalKummer.inflationVanishes_ramifiedTame` (:587) routes through
`odd_orderOf_tameInertia` (:382) and `tameInertia_normal` (:409), both of which hard-code `q = 2`
(they read the relation off `GQ2.Ttame`).  The general-`q` instantiation below routes instead
through **F3's** `GQ2.Dyadic.TameQ.{odd_order, zpowers_normal}` at `T_q`, `q = q_K = 2^f`
(packet Lem. 3.1/3.2 in finite-image form) — equivalently **PJ1's** `tame_odd_order_pow` /
`tame_zpowers_normal_pow`, which are the same statements. -/

section Inflation

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable {C : Type} [Group C] [TopologicalSpace C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction Γ V] [DistribMulAction C V]

variable (ρ : ContinuousMonoidHom Γ C)

/-- **The ambient inflation-vanishing input** at a general local source —
`GQ2.LocalKummer.InflationVanishes` retyped: every continuous cocycle vanishing pointwise on
`N_K = ker ρ` is a coboundary. -/
def InflationVanishesK : Prop :=
  ∀ b : ↥(Z1 Γ V), (∀ n : ↥(ρ.toMonoidHom.ker : Subgroup Γ), b.1 (n : Γ) = 0) →
    ∃ w₀ : V, ∀ g : Γ, b.1 g = g • w₀ - w₀

variable {ρ}

variable [Finite C]

omit [IsTopologicalGroup Γ] in
/-- **`InflationVanishesK` from an odd normal subgroup with no fixed vectors** — the
**coprime-averaging** discharge (`GQ2.LocalKummer.inflationVanishes_of_oddNormal` retyped).  The
argument is Hochschild–Serre-free and mentions no projectivity: a cocycle vanishing on `ker ρ`
descends to the finite image `C`; averaging over the odd-order `I` makes it cohomologous to a
cocycle killed on `I`; the two-way evaluation forces the residue into `V^I = 0`. -/
theorem inflationVanishes_of_oddNormalK
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (hsurj : Function.Surjective ⇑ρ)
    (I : Subgroup C) (hInorm : I.Normal) (hIodd : Odd (Nat.card ↥I))
    (hVI : ∀ v : V, (∀ i ∈ I, i • v = v) → v = 0) :
    InflationVanishesK (V := V) ρ := by
  classical
  haveI : Fintype ↥I := Fintype.ofFinite _
  intro b hbN
  obtain ⟨-, hcoc⟩ := mem_Z1_iff.mp b.2
  -- `b.1` is constant on `ρ`-fibres (its kernel acts trivially, `hρ`)
  have hdesc : ∀ g₁ g₂ : Γ, ρ g₁ = ρ g₂ → b.1 g₁ = b.1 g₂ := by
    intro g₁ g₂ hg
    have hmem : g₁⁻¹ * g₂ ∈ (ρ.toMonoidHom.ker : Subgroup Γ) := by
      rw [MonoidHom.mem_ker]
      show ρ (g₁⁻¹ * g₂) = 1
      rw [map_mul, map_inv, hg, inv_mul_cancel]
    have h0 : b.1 (g₁⁻¹ * g₂) = 0 := hbN ⟨g₁⁻¹ * g₂, hmem⟩
    have := hcoc g₁ (g₁⁻¹ * g₂)
    rw [h0, smul_zero, add_zero, mul_inv_cancel_left] at this
    exact this.symm
  -- descend `b` to `b̄ : C → V`
  set σ := Function.surjInv hsurj with hσdef
  have hσ : ∀ c : C, ρ (σ c) = c := Function.surjInv_eq hsurj
  set bbar : C → V := fun c => b.1 (σ c) with hbbar
  have hbbar_spec : ∀ g : Γ, bbar (ρ g) = b.1 g := fun g => hdesc (σ (ρ g)) g (hσ (ρ g))
  have hbbar_coc : ∀ c d : C, bbar (c * d) = bbar c + c • bbar d := by
    intro c d
    have h1 : b.1 (σ (c * d)) = b.1 (σ c * σ d) := hdesc _ _ (by rw [hσ, map_mul, hσ, hσ])
    show b.1 (σ (c * d)) = b.1 (σ c) + c • b.1 (σ d)
    rw [h1, hcoc, hρ, hσ]
  -- the averaging witness `w₀ = ∑_{i ∈ I} b̄ i`
  set w₀ : V := ∑ i : ↥I, bbar (i : C) with hw₀def
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
    have hsub : bbar (g₀ : C) = w₀ - (g₀ : C) • w₀ := by
      rw [eq_sub_iff_add_eq]; exact hexpand.symm
    rw [hsub]
    have hna : -w₀ = w₀ := neg_eq_of_add_eq_zero_left (hV2 w₀)
    have hnb : -((g₀ : C) • w₀) = (g₀ : C) • w₀ := neg_eq_of_add_eq_zero_left (hV2 _)
    rw [sub_eq_add_neg, sub_eq_add_neg, hna, hnb, add_comm]
  -- the error cocycle `r c = b̄ c − (c • w₀ − w₀)` is a cocycle killed on `I`
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
  -- two-way evaluation forces `r c ∈ V^I = 0`
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
  refine ⟨w₀, fun g => ?_⟩
  have hz := hr_zero (ρ g)
  rw [hrdef] at hz
  simp only [hbbar_spec, sub_eq_zero] at hz
  rw [hz, hρ]

omit [IsTopologicalGroup Γ] in
/-- **`InflationVanishesK` for a ramified simple tame module at every `q_K = 2^f`** — the
general-`q` twin of `GQ2.LocalKummer.inflationVanishes_ramifiedTame`.  The inertia subgroup
`I = ⟨c τ⟩` is normal by **F3's** `TameQ.zpowers_normal` (packet Lem. 3.2) and has odd order by
`TameQ.odd_order` (packet Lem. 3.1: `q` even ⟹ `orderOf τ` odd — **the middle-layer split of
Rem. 6.13 has no "even inertia order" branch**), and `V^I = 0` from ramified simplicity.  The
`ℚ₂`-only `odd_orderOf_tameInertia`/`tameInertia_normal` are not used. -/
theorem inflationVanishes_ramifiedTameQ {f : ℕ} (hf : 1 ≤ f)
    (ρ : ContinuousMonoidHom Γ C) (c : ContinuousMonoidHom (Tq (2 ^ f)) C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hV2 : ∀ v : V, v + v = 0)
    (hsurj : Function.Surjective ⇑ρ)
    (hgen : Subgroup.closure {c (tqSigma (2 ^ f)), c (tqTau (2 ^ f))} = ⊤)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c (tqTau (2 ^ f)) • v ≠ v) :
    InflationVanishesK (V := V) ρ := by
  set t : C := c (tqTau (2 ^ f)) with ht
  have hrel : (c (tqSigma (2 ^ f)))⁻¹ * t * c (tqSigma (2 ^ f)) = t ^ 2 ^ f :=
    tame_rel_map_q c.toMonoidHom
  have heven : Even (2 ^ f) := by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨2 ^ f', by rw [pow_succ]; ring⟩
  have hInorm : (Subgroup.zpowers t).Normal := TameQ.zpowers_normal hgen hrel
  have hIodd : Odd (Nat.card ↥(Subgroup.zpowers t)) := by
    rw [Nat.card_zpowers]
    exact TameQ.odd_order (orderOf_pos _).ne' (pow_ne_zero _ two_ne_zero) heven hrel
  have hVI : ∀ v : V, (∀ i ∈ Subgroup.zpowers t, i • v = v) → v = 0 :=
    LocalKummer.fixedByNormal_eq_bot (Subgroup.zpowers t) hInorm hsimple
      (by obtain ⟨v, hv⟩ := hram; exact ⟨t, Subgroup.mem_zpowers _, v, hv⟩)
  exact inflationVanishes_of_oddNormalK hρ hV2 hsurj (Subgroup.zpowers t) hInorm hIodd hVI

end Inflation

/-! ## §6 The deep-class cup vanishing at the splitting group

The `hvanish` core of the square and free orbit layers (packet Rem. 6.13): the cup of two deep
block coordinates over `N_K = ker ρ` has trivial `H²`-class.  This is the retype of
`GQ2.InvolutionSplice.hvanish_cup_ker` (`GQ2/InvolutionSplice.lean` :544).

**Deviation of shape (deliberate, and the reason this fits in LG4a).**  The `ℚ₂` proof *builds*
the splitting field internally (`GQ2.ResidueLift.splitField ρ` and its
`fixingSubgroup_splitField`), which is the `ResidueLift` machinery the memo rates MEDIUM-HIGH
(§2 row 10) and which belongs to the dimension lane.  Here the field is threaded as the `(k, hker)`
parameter pair instead — exactly the pattern the memo prescribes for the retype ("the `(k, hker)`
parameter pattern survives as `(L, hker′)` for the splitting field `L ⊇ K`", §2 row 3).  The
consumer supplies `(k, hker)` once and reuses it for the isotropy splice of §4, which needs the
identical pair. -/

section CupVanish

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

section Rigidity

variable {Θ : Type} [Group Θ] [TopologicalSpace Θ] [IsTopologicalGroup Θ]
  [DistribMulAction Θ (ZMod 2)] [ContinuousSMul Θ (ZMod 2)]

/-- **Trivial-coefficient rigidity** at a general group: two continuous 1-cocycles with the same
`H1ofFun` class are equal (`B¹(Θ, 𝔽₂) = 0`).  Local copy of `GQ2.eq_of_H1ofFun_eq`
(`GQ2/InvolutionSplice.lean`, not imported here); `_dp` suffix to dedup at merge. -/
theorem eq_of_H1ofFun_eq_dp {φ ψ : Θ → ZMod 2} (hφ : φ ∈ Z1 Θ (ZMod 2))
    (hψ : ψ ∈ Z1 Θ (ZMod 2)) (h : H1ofFun Θ φ = H1ofFun Θ ψ) : φ = ψ := by
  rw [H1ofFun_of_mem hφ, H1ofFun_of_mem hψ] at h
  have h0 : H1mk Θ (ZMod 2) (⟨φ, hφ⟩ - ⟨ψ, hψ⟩) = 0 := by rw [map_sub, h, sub_self]
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp h0
  rwa [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub,
    B1_eq_bot_of_trivial (fun g m => smul_zmodTwo g m), AddSubgroup.mem_bot, sub_eq_zero] at hmem

end Rigidity

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **Cup-cochain pullback of a coboundary along the anchor.**  If two `𝔽₂`-cochains on `ker ρ`
are pullbacks of `k`-side cochains whose cup is a coboundary, then their own cup is a coboundary.
Shared tail of the isotropy splice (§4) and the `hvanish` core below; the two `smul`s that are
`rfl` at `G_ℚ₂` are collapsed by `smul_zmodTwo` (the LG2 `smul` trap). -/
theorem cupFun_mem_B2_of_kside (k : IntermediateField ℚ_[2] ℚ̄₂)
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    {α β : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2} {a b : ↥k.fixingSubgroup → ZMod 2}
    (hαa : ∀ n, α n = a (kerToFixingAt anc ρ k hker n))
    (hβb : ∀ n, β n = b (kerToFixingAt anc ρ k hker n))
    (hB2 : cup11Fun AddMonoidHom.mul a b ∈ B2 ↥k.fixingSubgroup (ZMod 2)) :
    cup11Fun AddMonoidHom.mul α β ∈ B2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) := by
  obtain ⟨ψ, hψc, hψeq⟩ := hB2
  refine AddSubgroup.mem_map.mpr
    ⟨fun n => ψ (kerToFixingAt anc ρ k hker n),
      mem_C1_iff.mpr ((mem_C1_iff.mp hψc).comp (continuous_kerToFixingAt anc ρ k hker)), ?_⟩
  funext p
  have hpt := congrFun hψeq (kerToFixingAt anc ρ k hker p.1, kerToFixingAt anc ρ k hker p.2)
  show p.1 • ψ (kerToFixingAt anc ρ k hker p.2)
      - ψ (kerToFixingAt anc ρ k hker (p.1 * p.2))
      + ψ (kerToFixingAt anc ρ k hker p.1)
    = AddMonoidHom.mul (α p.1) (p.1 • β p.2)
  rw [smul_zmodTwo, smul_zmodTwo, kerToFixingAt_mul, hαa, hβb]
  have hexp : (kerToFixingAt anc ρ k hker p.1) • ψ (kerToFixingAt anc ρ k hker p.2)
      - ψ (kerToFixingAt anc ρ k hker p.1 * kerToFixingAt anc ρ k hker p.2)
      + ψ (kerToFixingAt anc ρ k hker p.1)
    = AddMonoidHom.mul (a (kerToFixingAt anc ρ k hker p.1))
        ((kerToFixingAt anc ρ k hker p.1) • b (kerToFixingAt anc ρ k hker p.2)) := hpt
  simp only [smul_zmodTwo] at hexp
  exact hexp

/-- The deep-class witness *is* the cocycle (trivial-coefficient rigidity): a deep class's
representative cochain equals the anchored Kummer cocycle of its deep unit, on the nose. -/
theorem exists_deepUnit_eq_of_mem_deepClassesAt {α : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2}
    (hαZ1 : α ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hαdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) α ∈ deepClassesAt (kerAnc anc ρ)) :
    ∃ A β : ℚ̄₂, SectionSix.IsDeepUnit (ancSubgroup (kerAnc anc ρ)) A ∧ β ^ 2 = A ∧ β ≠ 0 ∧
      ∀ n, α n = Kummer.kummerCocycleFun β (kerAnc anc ρ n) := by
  obtain ⟨A, β, hdeep, hsq, hβ0, hclass⟩ := hαdeep
  refine ⟨A, β, hdeep, hsq, hβ0, fun n => ?_⟩
  exact congrFun
    (eq_of_H1ofFun_eq_dp hαZ1 (kummerAnc_mem_Z1 (kerAnc anc ρ) hsq hβ0 hdeep.2.1) hclass.symm) n

/-- **The square/free `hvanish` over `ker ρ`, at a general local source** —
`GQ2.InvolutionSplice.hvanish_cup_ker` retyped with the splitting field threaded as `(k, hker)`.
The cup of two deep block coordinates has trivial `H²ofFun` class; the field-side vanishing is
the Tier-5 eq.-(94) orthogonality `GQ2.LocalKummer.cup_deepClasses`. -/
theorem hvanish_cup_ker_K (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (hker : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k.fixingSubgroup)
    (α β : ↥(ρ.toMonoidHom.ker : Subgroup Γ) → ZMod 2)
    (hαZ1 : α ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hβZ1 : β ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2))
    (hαdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) α ∈ deepClassesAt (kerAnc anc ρ))
    (hβdeep : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) β ∈ deepClassesAt (kerAnc anc ρ)) :
    H2ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ) (cup11Fun AddMonoidHom.mul α β) = 0 := by
  have htrivK : ∀ (g : ↥k.fixingSubgroup) (m : ZMod 2), g • m = m := fun _ _ => rfl
  obtain ⟨A, βA, hdA, hsqA, hβA0, hαeq⟩ := exists_deepUnit_eq_of_mem_deepClassesAt anc ρ hαZ1 hαdeep
  obtain ⟨B, δB, hdB, hsqB, hδB0, hβeq⟩ := exists_deepUnit_eq_of_mem_deepClassesAt anc ρ hβZ1 hβdeep
  -- the `k`-side cocycles and their eq.-(94) vanishing
  have hZ1ka : (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun βA (n : GalQ2))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqA hβA0 (fun g hg => hdA.2.1 g ((hker g).mpr hg))
  have hZ1kb : (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δB (n : GalQ2))
      ∈ Z1 ↥k.fixingSubgroup (ZMod 2) :=
    GQ2.DeepPart.kummerRestrict_mem_Z1 hsqB hδB0 (fun g hg => hdB.2.1 g ((hker g).mpr hg))
  have hcup0 := LocalKummer.cup_deepClasses k htrivK
    (ξ := H1ofFun ↥k.fixingSubgroup fun n => Kummer.kummerCocycleFun βA (n : GalQ2))
    (η := H1ofFun ↥k.fixingSubgroup fun n => Kummer.kummerCocycleFun δB (n : GalQ2))
    ⟨A, βA, isDeepUnit_of_le' (fun g hg => (hker g).mpr hg) hdA, hsqA, hβA0, rfl⟩
    ⟨B, δB, isDeepUnit_of_le' (fun g hg => (hker g).mpr hg) hdB, hsqB, hδB0, rfl⟩
  rw [H1ofFun_of_mem hZ1ka, H1ofFun_of_mem hZ1kb] at hcup0
  have hB2k : cup11Fun (AddMonoidHom.mul)
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun βA (n : GalQ2))
      (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δB (n : GalQ2))
      ∈ B2 ↥k.fixingSubgroup (ZMod 2) := by
    have h0 : H2mk ↥k.fixingSubgroup (ZMod 2)
        ⟨cup11Fun (AddMonoidHom.mul)
            (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun βA (n : GalQ2))
            (fun n : ↥k.fixingSubgroup => Kummer.kummerCocycleFun δB (n : GalQ2)),
          cup11_mem_Z2 (AddMonoidHom.mul) (fun g m n => by rw [htrivK, htrivK, htrivK])
            ⟨_, hZ1ka⟩ ⟨_, hZ1kb⟩⟩ = 0 := hcup0
    exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  -- pull the coboundary back along the anchor
  have hB2 := cupFun_mem_B2_of_kside anc ρ k hker (α := α) (β := β) hαeq hβeq hB2k
  have hZ2 : cup11Fun AddMonoidHom.mul α β
      ∈ Z2 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2) :=
    cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by rw [smul_zmodTwo, smul_zmodTwo, smul_zmodTwo])
      ⟨_, hαZ1⟩ ⟨_, hβZ1⟩
  rw [H2ofFun_of_mem hZ2]
  exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hB2)

end CupVanish

/-! ## §7 Conjugation stability of the deep classes (the free-orbit input)

`GQ2.conjAct_deepClasses` (`GQ2/AdmissibleCount.lean` :131) retyped: the `Γ`-conjugation action
`conjAct ρ g` (LG2, `GQ2/Dyadic/LocalGauss/PairingK.lean` §1) carries deep classes to deep
classes.  Concretely `conjAct ρ g [κ_β] = [κ_{anc g • β}]`, and `anc g • A` is again deep for the
anchored subgroup: normality of `ker ρ` keeps it fixed, and `‖anc g • b‖ = ‖b‖`
(`GQ2.norm_galois`).  This is the `hvanish`-side input of the **free** orbit branch (packet
Rem. 6.13) and, for LG4b, the invariance that lets `deepClassesSubgroupAt` carry the restricted
`conjModule` action. -/

section ConjStability

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
variable {C : Type} [Group C] [TopologicalSpace C]
variable (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- The anchor of the splitting group intertwines `conjMap` with ambient conjugation. -/
theorem kerAnc_conjMap (g : Γ) (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) :
    kerAnc anc ρ (conjMap ρ g n) = (anc g)⁻¹ * kerAnc anc ρ n * anc g := by
  show anc (g⁻¹ * (n : Γ) * g) = (anc g)⁻¹ * anc (n : Γ) * anc g
  rw [map_mul, map_mul, map_inv]

/-- **Conjugation stability of the anchored deep classes** — `GQ2.conjAct_deepClasses` retyped. -/
theorem conjAct_deepClassesAt (g : Γ)
    {ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup Γ) (ZMod 2)}
    (hξ : ξ ∈ deepClassesAt (kerAnc anc ρ)) :
    conjAct ρ g ξ ∈ deepClassesAt (kerAnc anc ρ) := by
  obtain ⟨A, β, hdeep, hsq, hβ0, rfl⟩ := hξ
  obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hdeep
  -- the conjugated element of the anchored subgroup: `anc n · anc g = anc g · anc (g⁻¹ n g)`
  have key : ∀ (n : ↥(ρ.toMonoidHom.ker : Subgroup Γ)) (x : ℚ̄₂),
      (∀ y ∈ ancSubgroup (kerAnc anc ρ), y • x = x) →
      (kerAnc anc ρ n) • (anc g • x) = anc g • x := by
    intro n x hfix
    rw [← mul_smul, show kerAnc anc ρ n * anc g = anc g * ((anc g)⁻¹ * kerAnc anc ρ n * anc g)
      from by group, mul_smul,
      show ((anc g)⁻¹ * kerAnc anc ρ n * anc g) • x = x from
        hfix _ (by rw [← kerAnc_conjMap anc ρ g n]; exact mem_ancSubgroup _ _)]
  have hmove : ∀ (m : GalQ2) (_ : m ∈ ancSubgroup (kerAnc anc ρ)) (x : ℚ̄₂),
      (∀ y ∈ ancSubgroup (kerAnc anc ρ), y • x = x) → m • (anc g • x) = anc g • x := by
    rintro _ ⟨n, rfl⟩ x hfix
    exact key n x hfix
  refine ⟨anc g • A, anc g • β, ⟨?_, ?_, anc g • b, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [AlgEquiv.smul_def]; simpa using hA0
  · exact fun m hm => hmove m hm A hAfix
  · exact fun m hm => hmove m hm b hbfix
  · rw [hAeq, AlgEquiv.smul_def, map_add, map_one, map_mul, map_ofNat, ← AlgEquiv.smul_def]
  · rwa [norm_galois]
  · rw [AlgEquiv.smul_def, AlgEquiv.smul_def, ← map_pow, hsq]
  · rw [AlgEquiv.smul_def]; simpa using hβ0
  · symm
    calc conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
            (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ n)))
        = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
            (fun n => Kummer.kummerCocycleFun β (kerAnc anc ρ (conjMap ρ g n))) :=
          conjAct_h1ofFun ρ g (kummerAnc_mem_Z1 (kerAnc anc ρ) hsq hβ0 hAfix)
      _ = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup Γ)
            (fun n => Kummer.kummerCocycleFun (anc g • β) (kerAnc anc ρ n)) := by
          congr 1
          funext n
          rw [kerAnc_conjMap anc ρ g n]
          exact kcf_conj β (anc g) (kerAnc anc ρ n)

end ConjStability

/-! ## §8 Staged exports for LG4b (the vanishing side of the join)

LG4b owns `LocalGauss/Ramified.lean`: the dimension lane, the join
`card_Q0loc_zero_eq_of_dim_of_vanish_K` and the endpoint `prop_6_18_ramified_K`.  This section
fixes the shape of the two vanishing-side inputs it consumes, and discharges the half of the join
that lives on the vanishing side — the **Lagrangian Arf step** (packet Prop. 6.12: `X₊` is a
totally singular half-dimensional subspace, hence `arf Q⁰ = 0`, which is exactly packet
Prop. 6.14's `+`-sign input).

**The join LG4b should write** (the `ℚ₂` model is
`GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish`, `GQ2/DeepPart/Q0locLayer.lean` :547; the two
changes are `2*m ↦ 2*(m*n)` in the count and LG2a's Euler theorem replacing the `B7` calls
`finite_H1`/`card_H1_eq_card_of_simple`):

```lean
theorem card_Q0loc_zero_eq_of_dim_of_vanish_K (D : TateDualityG Γ 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) …
    (hV2 : ∀ v : V, v + v = 0)
    (hdim    : Nat.card (deepPartK (V := V) anc ρ) ^ 2 = Nat.card (H1 Γ V))   -- LG4b's lane
    (hvanish : Q0locVanishesOnDeep D dat anc ρ)                               -- ← LG4a, below
    (m n : ℕ) (hmn : 1 ≤ m * n) (hcard : Nat.card (H1 Γ V) = 2 ^ (2 * (m * n))) :
    Nat.card {x : H1 Γ V // Q0loc D dat ρ x = 0} = 2 ^ (2 * (m * n) - 1) + 2 ^ (m * n - 1)
```

and its body is `zeroCount_of_arf_zero` applied to `arf_Q0loc_zero_of_deep` below — so the only
work left in the join is the `hcard` plumbing (Euler collapse) and the dimension lane. -/

section JoinExports

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]
variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction Γ V] [ContinuousSMul Γ V] [DistribMulAction C V]

/-- **The vanishing clause of Lemma 6.17 as a named proposition** — the exact shape of the
`hvanish` slot of the `ℚ₂` join (`GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish`): `Q⁰_loc`
vanishes identically on the deep half `X₊`.  LG4b threads this; the vanishing lane's endpoint
`lemma_6_17_vanish_final_K` produces it. -/
def Q0locVanishesOnDeep (D : TateDualityG Γ 2) (dat : FactorSet C V)
    (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C) : Prop :=
  ∀ x ∈ deepPartK (V := V) anc ρ, Q0loc D dat ρ x = 0

/-- **Packet Prop. 6.12 / Prop. 6.14 input: the deep half is a Lagrangian, so `arf Q⁰ = 0`.**
This is the vanishing-side half of LG4b's join: given the dimension clause `#X₊² = #H¹` and the
vanishing clause, the Arf invariant of `Q⁰_loc` is `0` — whence the `+` Gauss sign
(`GQ2.QuadraticFp2.zeroCount_of_arf_zero`, which LG4b applies).  Retype of the inner two steps of
`GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish`; `hfin` is supplied downstream by LG2a's Euler
finiteness clause (`localEulerCharacteristic_open`), replacing the `ℚ₂` `B7` call. -/
theorem arf_Q0loc_zero_of_deep (D : TateDualityG Γ 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (anc : ContinuousMonoidHom Γ GalQ2) (ρ : ContinuousMonoidHom Γ C)
    (hρ : ∀ (g : Γ) (v : V), g • v = ρ g • v) (hinv : ∀ (c : C) (v : V), q (c • v) = q v)
    (hV2 : ∀ v : V, v + v = 0) (hfin : Finite (H1 Γ V))
    (hdim : Nat.card (deepPartK (V := V) anc ρ) ^ 2 = Nat.card (H1 Γ V))
    (hvanish : Q0locVanishesOnDeep D dat anc ρ) :
    arf (Q0loc D dat ρ (V := V)) = 0 := by
  haveI := hfin
  haveI : Fintype (H1 Γ V) := Fintype.ofFinite _
  have hqG : ∀ (g : Γ) (v : V), q (g • v) = q v := fun g v => by rw [hρ]; exact hinv _ v
  have hq' := isQuadraticFp2_Q0loc D q hq dat hdat ρ hρ hqG
  have hns' := nonsingular_Q0loc D q hq hns hV2 dat hdat ρ hρ hqG
  exact arf_zero_of_card_sq _ hq' (h1_add_self_dp hV2) hns'
    (deepPartSubgroupK anc ρ hρ hV2) hvanish hdim

end JoinExports

end GQ2.Dyadic
