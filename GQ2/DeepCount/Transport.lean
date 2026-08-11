/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DeepCount.Bounds

@[expose] public section

/-!
# Transport of first cohomology to the kernel field

The comparison between cohomology on `ker ρ` and the corresponding local Galois group.

See `GQ2.DeepCount` for the paper-facing overview, source citations, and deviations.
-/

namespace GQ2

open ContCoh LocalKummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The `ker ρ ↔ G_k` transport of `H¹`

`hker` is a POINTWISE identification, so the types `H1 ↥(ker ρ)` and `H1 k.fixingSubgroup`
differ as terms and an `Eq`-rewrite dies on dependent motives.  Instead: with trivial
coefficients the transport is plain COCYCLE PRECOMPOSITION along the identity inclusions
`kerToFixing`/`fixingToKer` (the `conjAct`-machinery pattern: `Quotient.out`-based maps with
`H1ofFun`-computation rules — the `B¹ = 0` argument makes the representative exact). -/

section KerTransport

variable {C : Type} [Group C] [TopologicalSpace C]
variable (ρ : ContinuousMonoidHom AbsGalQ2 C) (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The identity inclusion `↥k.fixingSubgroup → ↥(ker ρ)` (inverse of `kerToFixing`). -/
def fixingToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (n : ↥k.fixingSubgroup) : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
  ⟨(n : Kummer.GaloisGroup ℚ_[2]), (hker n.1).mpr n.2⟩

private theorem fixingToKer_mul (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (n m : ↥k.fixingSubgroup) :
    fixingToKer ρ k hker (n * m) = fixingToKer ρ k hker n * fixingToKer ρ k hker m :=
  Subtype.ext rfl

private theorem continuous_fixingToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    Continuous (fixingToKer ρ k hker) :=
  Continuous.subtype_mk continuous_subtype_val _

/-- Precomposition with `fixingToKer` carries `Z¹(ker ρ)` to `Z¹(G_k)`. -/
theorem comp_fixingToKer_mem_Z1 (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    (fun n => f (fixingToKer ρ k hker n)) ∈ Z1 k.fixingSubgroup (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_fixingToKer ρ k hker), fun n m => ?_⟩
  show f (fixingToKer ρ k hker (n * m))
    = f (fixingToKer ρ k hker n) + n • f (fixingToKer ρ k hker m)
  have htriv : ∀ (a : ↥(k.fixingSubgroup)) (z : ZMod 2), a • z = z := fun _ _ => rfl
  have htriv' : ∀ (a : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (z : ZMod 2),
      a • z = z := fun _ _ => rfl
  rw [fixingToKer_mul, hcoc, htriv, htriv']

/-- Precomposition with `kerToFixing` carries `Z¹(G_k)` to `Z¹(ker ρ)`. -/
theorem comp_kerToFixing_mem_Z1 (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(k.fixingSubgroup) → ZMod 2}
    (hf : f ∈ Z1 k.fixingSubgroup (ZMod 2)) :
    (fun n => f (kerToFixing ρ k hker n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) := by
  obtain ⟨hfc, hcoc⟩ := mem_Z1_iff.mp hf
  refine mem_Z1_iff.mpr ⟨hfc.comp (continuous_kerToFixing ρ k hker), fun n m => ?_⟩
  show f (kerToFixing ρ k hker (n * m))
    = f (kerToFixing ρ k hker n) + n • f (kerToFixing ρ k hker m)
  have htriv : ∀ (a : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (z : ZMod 2),
      a • z = z := fun _ _ => rfl
  have htriv' : ∀ (a : ↥(k.fixingSubgroup)) (z : ZMod 2), a • z = z := fun _ _ => rfl
  rw [kerToFixing_mul, hcoc, htriv, htriv']

/-- Transport `H¹(ker ρ) → H¹(G_k)` (cocycle precomposition with `fixingToKer`). -/
noncomputable def h1KerToFix (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    H1 k.fixingSubgroup (ZMod 2) :=
  H1ofFun k.fixingSubgroup (fun n => (Quotient.out ξ).1 (fixingToKer ρ k hker n))

/-- Transport `H¹(G_k) → H¹(ker ρ)` (cocycle precomposition with `kerToFixing`). -/
noncomputable def h1FixToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (η : H1 k.fixingSubgroup (ZMod 2)) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
  H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
    (fun n => (Quotient.out η).1 (kerToFixing ρ k hker n))

/-- Computation rule for `h1KerToFix` (the `B¹ = 0` argument: the canonical representative of
an `H1ofFun`-class is the function itself). -/
theorem h1KerToFix_h1ofFun (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) → ZMod 2}
    (hf : f ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) f)
      = H1ofFun k.fixingSubgroup (fun n => f (fixingToKer ρ k hker n)) := by
  set ξ := H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) f with hξ
  have hout : (Quotient.out ξ
      : ↥(Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))).1 = f := by
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
  unfold h1KerToFix
  rw [hout]

/-- Computation rule for `h1FixToKer`. -/
theorem h1FixToKer_h1ofFun (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    {f : ↥(k.fixingSubgroup) → ZMod 2}
    (hf : f ∈ Z1 k.fixingSubgroup (ZMod 2)) :
    h1FixToKer ρ k hker (H1ofFun k.fixingSubgroup f)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => f (kerToFixing ρ k hker n)) := by
  set η := H1ofFun k.fixingSubgroup f with hη
  have hout : (Quotient.out η : ↥(Z1 k.fixingSubgroup (ZMod 2))).1 = f := by
    have h1 : H1mk k.fixingSubgroup (ZMod 2) (Quotient.out η)
        = H1mk k.fixingSubgroup (ZMod 2) ⟨f, hf⟩ := by
      have hoe : H1mk k.fixingSubgroup (ZMod 2) (Quotient.out η) = η := Quotient.out_eq η
      rw [hoe, hη, H1ofFun_of_mem hf]
    have hz0 : H1mk k.fixingSubgroup (ZMod 2) (Quotient.out η - ⟨f, hf⟩) = 0 := by
      rw [map_sub, h1, sub_self]
    have hdiff := (QuotientAddGroup.eq_zero_iff _).mp hz0
    rw [AddSubgroup.mem_addSubgroupOf] at hdiff
    obtain ⟨w₀, hw₀⟩ := hdiff
    funext n
    have hn := congrFun hw₀ n
    have hz : (Quotient.out η - ⟨f, hf⟩ : ↥(Z1 k.fixingSubgroup (ZMod 2))).1 n = 0 := by
      rw [← hn]
      show n • w₀ - w₀ = 0
      rw [show n • w₀ = w₀ from rfl, sub_self]
    have : (Quotient.out η).1 n - f n = 0 := hz
    exact sub_eq_zero.mp this
  unfold h1FixToKer
  rw [hout]

/-- The round trip `ker → fix → ker` is the identity. -/
theorem h1FixToKer_h1KerToFix (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1FixToKer ρ k hker (h1KerToFix ρ k hker ξ) = ξ := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a
        : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) a.1
      from (H1ofFun_of_mem a.2).symm]
    rw [h1KerToFix_h1ofFun ρ k hker a.2,
      h1FixToKer_h1ofFun ρ k hker (comp_fixingToKer_mem_Z1 ρ k hker a.2)]
    exact congrArg _ (funext fun n => congrArg a.1 (Subtype.ext rfl))

/-- The round trip `fix → ker → fix` is the identity. -/
theorem h1KerToFix_h1FixToKer (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (η : H1 k.fixingSubgroup (ZMod 2)) :
    h1KerToFix ρ k hker (h1FixToKer ρ k hker η) = η := by
  induction η using QuotientAddGroup.induction_on with
  | H a =>
    rw [show (QuotientAddGroup.mk a : H1 k.fixingSubgroup (ZMod 2))
      = H1ofFun k.fixingSubgroup a.1 from (H1ofFun_of_mem a.2).symm]
    rw [h1FixToKer_h1ofFun ρ k hker a.2,
      h1KerToFix_h1ofFun ρ k hker (comp_kerToFixing_mem_Z1 ρ k hker a.2)]
    exact congrArg _ (funext fun n => congrArg a.1 (Subtype.ext rfl))

/-- `h1KerToFix` is additive. -/
theorem h1KerToFix_add (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ η : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker (ξ + η) = h1KerToFix ρ k hker ξ + h1KerToFix ρ k hker η := by
  induction ξ using QuotientAddGroup.induction_on with
  | H a =>
    induction η using QuotientAddGroup.induction_on with
    | H b =>
      show h1KerToFix ρ k hker (H1mk _ _ a + H1mk _ _ b)
        = h1KerToFix ρ k hker (H1mk _ _ a) + h1KerToFix ρ k hker (H1mk _ _ b)
      rw [← map_add, ← H1ofFun_of_mem (a + b).2, ← H1ofFun_of_mem a.2,
        ← H1ofFun_of_mem b.2, h1KerToFix_h1ofFun ρ k hker (a + b).2,
        h1KerToFix_h1ofFun ρ k hker a.2, h1KerToFix_h1ofFun ρ k hker b.2]
      exact GQ2.DeepPart.H1ofFun_add (comp_fixingToKer_mem_Z1 ρ k hker a.2)
        (comp_fixingToKer_mem_Z1 ρ k hker b.2)

/-- **The transport equivalence** `H¹(ker ρ) ≃+ H¹(G_k)`. -/
noncomputable def h1KerFixEquiv (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup) :
    H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ≃+
      H1 k.fixingSubgroup (ZMod 2) where
  toFun := h1KerToFix ρ k hker
  invFun := h1FixToKer ρ k hker
  left_inv := h1FixToKer_h1KerToFix ρ k hker
  right_inv := h1KerToFix_h1FixToKer ρ k hker
  map_add' := h1KerToFix_add ρ k hker

/-- `h1KerToFix` carries deep classes to deep classes, and conversely (the `(A, β)`-data
transports verbatim; memberships move along `hker`). -/
theorem h1KerToFix_mem_deep_iff (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker ξ ∈ LocalKummer.deepClasses k.fixingSubgroup
      ↔ ξ ∈ deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  constructor
  · rintro ⟨A, β, hd, hsq, hβ0, heq⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mp hg), b,
      fun g hg => hbfix g ((hker g).mp hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    have hZ1 : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
        ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    calc H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2))
        = h1FixToKer ρ k hker (H1ofFun k.fixingSubgroup
            (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))) := by
          rw [h1FixToKer_h1ofFun ρ k hker hZ1]
          exact congrArg _ (funext fun n => rfl)
      _ = h1FixToKer ρ k hker (h1KerToFix ρ k hker ξ) := by rw [heq]
      _ = ξ := h1FixToKer_h1KerToFix ρ k hker ξ
  · rintro ⟨A, β, hd, hsq, hβ0, rfl⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
        ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    show H1ofFun k.fixingSubgroup
        (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      = h1KerToFix ρ k hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
    rw [h1KerToFix_h1ofFun ρ k hker hZ1]
    exact congrArg _ (funext fun n => rfl)

/-- The mid-classes version of the transport. -/
theorem h1KerToFix_mem_mid_iff (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (ξ : H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :
    h1KerToFix ρ k hker ξ ∈ midClassesSubgroup k.fixingSubgroup
      ↔ ξ ∈ midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  constructor
  · rintro ⟨A, β, hd, hsq, hβ0, heq⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mp hg), b,
      fun g hg => hbfix g ((hker g).mp hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    have hZ1 : (fun n : ↥(k.fixingSubgroup) =>
        Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
        ∈ Z1 k.fixingSubgroup (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    calc H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2))
        = h1FixToKer ρ k hker (H1ofFun k.fixingSubgroup
            (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))) := by
          rw [h1FixToKer_h1ofFun ρ k hker hZ1]
          exact congrArg _ (funext fun n => rfl)
      _ = h1FixToKer ρ k hker (h1KerToFix ρ k hker ξ) := by rw [heq]
      _ = ξ := h1FixToKer_h1KerToFix ρ k hker ξ
  · rintro ⟨A, β, hd, hsq, hβ0, rfl⟩
    obtain ⟨hA0, hAfix, b, hbfix, hAeq, hb⟩ := hd
    have hZ1 : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
        Kummer.kummerCocycleFun β (n : AbsGalQ2))
        ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
      GQ2.DeepPart.kummerRestrict_mem_Z1 hsq hβ0 hAfix
    refine ⟨A, β, ⟨hA0, fun g hg => hAfix g ((hker g).mpr hg), b,
      fun g hg => hbfix g ((hker g).mpr hg), hAeq, hb⟩, hsq, hβ0, ?_⟩
    show H1ofFun k.fixingSubgroup
        (fun n => Kummer.kummerCocycleFun β (n : Kummer.GaloisGroup ℚ_[2]))
      = h1KerToFix ρ k hker (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (fun n => Kummer.kummerCocycleFun β (n : AbsGalQ2)))
    rw [h1KerToFix_h1ofFun ρ k hker hZ1]
    exact congrArg _ (funext fun n => rfl)

/-- **The transported structural count**, in `ker ρ`-vocabulary:
`#(H¹(ker ρ) ⧸ Deep) ≤ #E`. -/
theorem card_quot_deep_le_card_mid_ker [FiniteDimensional ℚ_[2] k]
    [Finite (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))]
    (hker : ∀ x : Kummer.GaloisGroup ℚ_[2],
      x ∈ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) ↔ x ∈ k.fixingSubgroup)
    (π : ℚ̄₂) (hπk : π ∈ k) (hπ0 : π ≠ 0) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : ℚ̄₂, x ∈ k → ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    {e : ℕ} (he : ‖(2 : ℚ̄₂)‖ = ‖π‖ ^ e) (he_pos : 1 ≤ e) {f : ℕ} (hf_pos : 1 ≤ f)
    (hcard_zero : Nat.card (↥(normUnits k) ⧸
      (depthUnits k π 1).subgroupOf (normUnits k)) = 2 ^ f - 1)
    (hcard_gr : ∀ i : ℕ, 1 ≤ i → Nat.card (↥(depthUnits k π i) ⧸
      (depthUnits k π (i + 1)).subgroupOf (depthUnits k π i)) = 2 ^ f) :
    Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      ≤ Nat.card ↥(midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) := by
  haveI hfinFix : Finite (H1 k.fixingSubgroup (ZMod 2)) :=
    Finite.of_equiv _ (h1KerFixEquiv ρ k hker).toEquiv
  have hcount := card_quot_deep_le_card_mid k π hπk hπ0 hπ1 hπmax he he_pos hf_pos
    hcard_zero hcard_gr
  -- (a) the ambient cards agree
  have ha : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
    Nat.card_congr (h1KerFixEquiv ρ k hker).toEquiv
  -- (b) the deep subgroups agree (through `coe_kummerDepth_deep`)
  have hb : Nat.card ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card ↥(kummerDepth k π (e + 1)) := by
    refine Nat.card_congr ((h1KerFixEquiv ρ k hker).toEquiv.subtypeEquiv (fun ξ => ?_))
    constructor
    · intro hξ
      have hset := Set.ext_iff.mp (coe_kummerDepth_deep k π hπk hπ0 hπ1 hπmax he_pos he)
        (h1KerToFix ρ k hker ξ)
      exact hset.mpr ((h1KerToFix_mem_deep_iff ρ k hker ξ).mpr hξ)
    · intro hη
      have hset := Set.ext_iff.mp (coe_kummerDepth_deep k π hπk hπ0 hπ1 hπmax he_pos he)
        (h1KerToFix ρ k hker ξ)
      exact (h1KerToFix_mem_deep_iff ρ k hker ξ).mp (hset.mp hη)
  -- (c) the mid subgroups agree (through `coe_kummerDepth_mid`)
  have hc : Nat.card ↥(midClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card ↥(kummerDepth k π e) := by
    refine Nat.card_congr ((h1KerFixEquiv ρ k hker).toEquiv.subtypeEquiv (fun ξ => ?_))
    constructor
    · intro hξ
      have hset := Set.ext_iff.mp (coe_kummerDepth_mid k π he) (h1KerToFix ρ k hker ξ)
      exact hset.mpr ((h1KerToFix_mem_mid_iff ρ k hker ξ).mpr hξ)
    · intro hη
      have hset := Set.ext_iff.mp (coe_kummerDepth_mid k π he) (h1KerToFix ρ k hker ξ)
      exact (h1KerToFix_mem_mid_iff ρ k hker ξ).mp (hset.mp hη)
  -- the quotient cards agree by Lagrange + cancellation
  haveI : Nonempty ↥(kummerDepth k π (e + 1)) := ⟨⟨0, zero_mem _⟩⟩
  have hL1 : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
        * Nat.card ↥(deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2)) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
  have hL2 : Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
        * Nat.card ↥(kummerDepth k π (e + 1))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2)) :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _).symm
  have hq : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
        deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
      = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1)) := by
    have hmm : Nat.card (H1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) ⧸
          deepClassesSubgroup (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
          * Nat.card ↥(kummerDepth k π (e + 1))
        = Nat.card (H1 k.fixingSubgroup (ZMod 2) ⧸ kummerDepth k π (e + 1))
          * Nat.card ↥(kummerDepth k π (e + 1)) := by
      rw [← hb, hL1, ha, ← hL2, hb]
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hmm
  rw [hq, hc]
  exact hcount

end KerTransport

end GQ2
