import GQ2.SectionEight.Fourier

/-!
# §8: central double covers, liftable counts, and the lift torsor

Central double covers and their pulled-back boundary-framed structure (Lemma 8.3 setup),
corestriction of continuous homs, the totalized stratum count `exactImageCountOn`, the
liftable count `u^β_Γ(p, J)` (`liftableCount`), and the scalar-twist torsor structure on
cover lifts (Lemma 8.2's second clause).  Split out of `GQ2.SectionEight` (wave 38a).
-/

open scoped Pointwise

namespace GQ2

namespace SectionEight

open QuadraticFp2

/-! ## Central double covers and the pulled-back boundary-framed structure  (Lemma 8.3 setup)

A **central double cover** `p : Ỹ ↠ Y` carries its own group/topology data (all finite
discrete).  The pulled-back marked target `(Ỹ, p⁻¹(L_Y), π_Y∘p, θ_Y∘p)` of Lemma 8.3 is
`pullTarget`; the paper's condition "the central kernel lies in `ker(π̃, θ̃)`" holds by
construction. -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/- `CentralCover` and `CentralCover.sq_eq_one_of_mem_ker` moved to `GQ2/RadicalEdgeData.lean`
(P-16a def-layer relocation, 2026-07-04; see `docs/p16-ticket-split.md`). -/

namespace CentralCover

variable {Y : Type} [Group Y] [Finite Y] (C : CentralCover Y)

/-- **The pulled-back boundary-framed structure** (Lemma 8.3): give `Ỹ` the marked normal
2-subgroup `p⁻¹(L_Y)`, head `π_Y ∘ p`, decoration `θ_Y ∘ p`. -/
noncomputable def pullTarget (T : MarkedTarget H E Y) : MarkedTarget H E C.cover where
  LY := T.LY.comap C.p
  normal := T.normal.comap C.p
  isPGroup_two := by
    intro x
    obtain ⟨k, hk⟩ := T.isPGroup_two ⟨C.p x.1, x.2⟩
    refine ⟨k + 1, ?_⟩
    have hker : x.1 ^ 2 ^ k ∈ C.p.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      simpa using congrArg Subtype.val hk
    ext
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_succ, pow_mul, pow_two]
    exact C.sq_eq_one_of_mem_ker hker
  piY := T.piY.comp C.p
  piY_surjective := T.piY_surjective.comp C.surj
  ker_piY := by
    ext x
    simp [MonoidHom.mem_ker, ← T.ker_piY]
  thetaY := T.thetaY.comp C.p

end CentralCover

/-! ## Corestriction of continuous homs to a subgroup

Mathlib has no `ContinuousMonoidHom.codRestrict`; we build the corestriction to a subgroup of
the codomain containing the image, and the bijection between homs onto a subgroup and homs into
the ambient group landing in it — the bookkeeping the Lemma 8.3 fibrations run on. -/

section CodRestrict

variable {G₁ G₂ : Type*} [Group G₁] [TopologicalSpace G₁] [Group G₂] [TopologicalSpace G₂]

/-- Corestrict a continuous hom to a subgroup of its codomain containing its image. -/
def cmhCodRestrict (f : ContinuousMonoidHom G₁ G₂) (S : Subgroup G₂) (h : ∀ x, f x ∈ S) :
    ContinuousMonoidHom G₁ ↥S where
  toFun x := ⟨f x, h x⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x y)
  continuous_toFun := f.continuous_toFun.subtype_mk h

/-- Include a continuous hom into a subgroup back into the ambient group. -/
def cmhInclude (S : Subgroup G₂) (g : ContinuousMonoidHom G₁ ↥S) : ContinuousMonoidHom G₁ G₂ :=
  ⟨(S.subtype).comp g.toMonoidHom, continuous_subtype_val.comp g.continuous_toFun⟩

end CodRestrict

/-! ## Liftable counts and the totalized stratum count -/

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- The covering map bundled as a continuous hom (continuous since the cover is discrete). -/
noncomputable def CentralCover.pCont (C : CentralCover Y) : ContinuousMonoidHom C.cover Y :=
  ⟨C.p, continuous_of_discreteTopology⟩

open scoped Classical in
/-- The exact-image count of the `J`-stratum, totalized (`0` when `J` does not project onto
`H`) — the summand shape of the partitions (124)/(138)/(142). -/
noncomputable def exactImageCountOn (b : ContinuousMonoidHom Γ ↥boundarySubgroup)
    (F : BoundaryFrame H E) (T : MarkedTarget H E Y) (J : Subgroup Y) : ℕ :=
  if h : Function.Surjective (T.piY.comp J.subtype) then exactImageCount b F (T.stratum J h)
  else 0

/-- **`u^β_Γ(p, J)`** (Lemma 8.3): the number of boundary-framed exact-image maps onto the
`J`-stratum whose pullback central cover is **split** — encoded as the existence of a
continuous lift through `p` (an unobstructed map has a lift, and conversely). -/
noncomputable def liftableCount (b : ContinuousMonoidHom Γ ↥boundarySubgroup)
    (F : BoundaryFrame H E) (T : MarkedTarget H E Y) (C : CentralCover Y)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) : ℕ :=
  Nat.card {f : BoundaryLifts b F (T.stratum J hJ) //
    ∃ g : ContinuousMonoidHom Γ C.cover, ∀ γ : Γ, C.p (g γ) = (f.1.1 γ : Y)}

/-! ## Scalar twisting  (Lemma 8.2's second clause — proved) -/

section Twist

variable {Y : Type} [Group Y] [Finite Y]

/-- `z`-powers indexed by `𝔽₂` are multiplicative (uses only `z² = 1`). -/
private lemma zpow_val_add (C : CentralCover Y) (x y : ZMod 2) :
    C.z ^ (x + y).val = C.z ^ x.val * C.z ^ y.val := by
  have hz : ∀ n : ℕ, C.z ^ n = C.z ^ (n % 2) := fun n => by
    conv_lhs => rw [← Nat.div_add_mod n 2]
    rw [pow_add, pow_mul, pow_two, C.z_sq, one_pow, one_mul]
  rw [hz (x + y).val, hz x.val, hz y.val, ← pow_add, hz (x.val % 2 + y.val % 2)]
  congr 1
  rw [ZMod.val_add]
  omega

/-- `z`-powers are central. -/
lemma z_pow_central (C : CentralCover Y) (n : ℕ) (w : C.cover) :
    C.z ^ n * w = w * C.z ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, C.central, ← mul_assoc, ih, mul_assoc]

/-- **Scalar twist** of a map into a central double cover by a `𝔽₂`-character
(Lemma 8.2/8.3: "multiplying a lift by a scalar character").  A homomorphism because `z` is
central of square one. -/
noncomputable def scalarTwist (C : CentralCover Y)
    (f : ContinuousMonoidHom Γ C.cover)
    (c : ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) :
    ContinuousMonoidHom Γ C.cover where
  toFun γ := f γ * C.z ^ ((c γ).toAdd).val
  map_one' := by simp
  map_mul' γ δ := by
    have hc : ((c (γ * δ)).toAdd).val = ((c γ).toAdd + (c δ).toAdd).val := by
      rw [map_mul]
      rfl
    rw [hc, zpow_val_add, map_mul]
    calc f γ * f δ * (C.z ^ ((c γ).toAdd).val * C.z ^ ((c δ).toAdd).val)
        = f γ * (f δ * C.z ^ ((c γ).toAdd).val) * C.z ^ ((c δ).toAdd).val := by
          group
      _ = f γ * (C.z ^ ((c γ).toAdd).val * f δ) * C.z ^ ((c δ).toAdd).val := by
          rw [z_pow_central]
      _ = f γ * C.z ^ ((c γ).toAdd).val * (f δ * C.z ^ ((c δ).toAdd).val) := by
          group
  continuous_toFun := by
    refine Continuous.mul (map_continuous f) ?_
    exact (continuous_of_discreteTopology
      (f := fun m : Multiplicative (ZMod 2) => C.z ^ (m.toAdd).val)).comp (map_continuous c)

/-! ### The torsor structure on cover lifts

The continuous-hom lifts of a fixed `f : Γ → Y` through `p` form a **torsor** under
`Hom_cont(Γ, 𝔽₂)`, acting by `scalarTwist`.  This is the combinatorial heart of Lemma 8.3 (and
the half-torsor of 8.6): `p_comp_scalarTwist` (the action stays in the fibre),
`scalarTwist_left_injective` (freeness), and `liftDiff`/`scalarTwist_liftDiff`
(transitivity — every two lifts differ by a unique character). -/

variable (C : CentralCover Y)

/-- `z` has order exactly 2. -/
lemma orderOf_z : orderOf C.z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact C.z_sq) C.z_ne

/-- `z^a = z^b` in the cover iff `a ≡ b [MOD 2]`. -/
lemma z_pow_eq_iff {a b : ℕ} : C.z ^ a = C.z ^ b ↔ a ≡ b [MOD 2] := by
  rw [pow_eq_pow_iff_modEq, orderOf_z]

/-- `p` kills `z`. -/
lemma p_z : C.p C.z = 1 := by
  rw [← MonoidHom.mem_ker, C.ker_eq]; exact Subgroup.mem_zpowers _

/-- `p` kills every `z`-power. -/
lemma p_z_pow (n : ℕ) : C.p (C.z ^ n) = 1 := by
  rw [map_pow, p_z, one_pow]

/-- Elements of `⟨z⟩` are `1` or `z`. -/
lemma eq_one_or_z_of_mem_ker {w : C.cover} (hw : w ∈ C.p.ker) : w = 1 ∨ w = C.z := by
  rw [C.ker_eq, Subgroup.mem_zpowers_iff] at hw
  obtain ⟨k, rfl⟩ := hw
  have hz2 : C.z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact C.z_sq
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact Or.inl (by rw [← two_mul, zpow_mul, hz2, one_zpow])
  · exact Or.inr (by rw [zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one])

/-- The twist projects to the same map: `p ∘ (twist g c) = p ∘ g`. -/
lemma p_comp_scalarTwist (g : ContinuousMonoidHom Γ C.cover)
    (c : ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) (γ : Γ) :
    C.p (scalarTwist C g c γ) = C.p (g γ) := by
  show C.p (g γ * C.z ^ ((c γ).toAdd).val) = C.p (g γ)
  rw [map_mul, p_z_pow, mul_one]

/-- For `a b : 𝔽₂`, congruence of vals mod 2 pins equality. -/
private lemma zmod2_eq_of_val_modEq {a b : ZMod 2} (h : a.val ≡ b.val [MOD 2]) : a = b := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have : a.val = b.val := by rw [Nat.ModEq] at h; omega
  exact ZMod.val_injective 2 this

/-- **Freeness of the torsor action**: `c ↦ scalarTwist C g c` is injective. -/
lemma scalarTwist_left_injective (g : ContinuousMonoidHom Γ C.cover) :
    Function.Injective (scalarTwist C g) := by
  intro c c' h
  ext γ
  have hg : g γ * C.z ^ ((c γ).toAdd).val = g γ * C.z ^ ((c' γ).toAdd).val :=
    DFunLike.congr_fun h γ
  exact Multiplicative.toAdd.injective
    (zmod2_eq_of_val_modEq ((z_pow_eq_iff C).mp (mul_left_cancel hg)))

open scoped Classical in
/-- The raw `𝔽₂`-valued difference of two lifts: `0` where they agree, `1` where they differ
by `z`. -/
private noncomputable def liftChar (g g' : ContinuousMonoidHom Γ C.cover) (γ : Γ) : ZMod 2 :=
  if g γ = g' γ then 0 else 1

/-- **Representation**: `g' γ = g γ · z^{liftChar γ}` for lifts agreeing under `p`. -/
private lemma liftChar_rep (g g' : ContinuousMonoidHom Γ C.cover)
    (h : ∀ γ, C.p (g γ) = C.p (g' γ)) (γ : Γ) :
    g' γ = g γ * C.z ^ (liftChar C g g' γ).val := by
  unfold liftChar
  by_cases hγ : g γ = g' γ
  · rw [if_pos hγ, show ((0 : ZMod 2)).val = 0 from rfl, pow_zero, mul_one, hγ]
  · rw [if_neg hγ, show ((1 : ZMod 2)).val = 1 from rfl, pow_one]
    have hmem : (g γ)⁻¹ * g' γ ∈ C.p.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h γ, inv_mul_cancel]
    rcases eq_one_or_z_of_mem_ker C hmem with he | he
    · exact absurd (inv_mul_eq_one.mp he) hγ
    · rw [← he, mul_inv_cancel_left]

/-- **Additivity** of the difference character (the torsor cocycle identity). -/
private lemma liftChar_add (g g' : ContinuousMonoidHom Γ C.cover)
    (h : ∀ γ, C.p (g γ) = C.p (g' γ)) (γ δ : Γ) :
    liftChar C g g' (γ * δ) = liftChar C g g' γ + liftChar C g g' δ := by
  apply zmod2_eq_of_val_modEq
  rw [← z_pow_eq_iff C]
  -- `z^{χ(γδ).val} = z^{(χγ+χδ).val}`, obtained by cancelling `g(γδ) = gγ·gδ`
  have key : g γ * g δ * C.z ^ (liftChar C g g' (γ * δ)).val
      = g γ * g δ * C.z ^ (liftChar C g g' γ + liftChar C g g' δ).val := by
    calc g γ * g δ * C.z ^ (liftChar C g g' (γ * δ)).val
        = g (γ * δ) * C.z ^ (liftChar C g g' (γ * δ)).val := by rw [map_mul]
      _ = g' (γ * δ) := (liftChar_rep C g g' h (γ * δ)).symm
      _ = g' γ * g' δ := by rw [map_mul]
      _ = (g γ * C.z ^ (liftChar C g g' γ).val) * (g δ * C.z ^ (liftChar C g g' δ).val) := by
          rw [liftChar_rep C g g' h γ, liftChar_rep C g g' h δ]
      _ = g γ * g δ * (C.z ^ (liftChar C g g' γ).val * C.z ^ (liftChar C g g' δ).val) := by
          rw [show g γ * C.z ^ (liftChar C g g' γ).val * (g δ * C.z ^ (liftChar C g g' δ).val)
                = g γ * (C.z ^ (liftChar C g g' γ).val * g δ) * C.z ^ (liftChar C g g' δ).val
              from by group, z_pow_central]
          group
      _ = g γ * g δ * C.z ^ ((liftChar C g g' γ).val + (liftChar C g g' δ).val) := by
          rw [pow_add]
      _ = g γ * g δ * C.z ^ (liftChar C g g' γ + liftChar C g g' δ).val := by
          congr 1
          rw [z_pow_eq_iff C, ZMod.val_add]
          exact (Nat.mod_modEq _ 2).symm
  exact mul_left_cancel key

/-- **The difference character** of two lifts agreeing under `p`.  Defined so that
`scalarTwist C g (liftDiff C g g' h) = g'` (`scalarTwist_liftDiff`, transitivity). -/
noncomputable def liftDiff (g g' : ContinuousMonoidHom Γ C.cover)
    (h : ∀ γ, C.p (g γ) = C.p (g' γ)) :
    ContinuousMonoidHom Γ (Multiplicative (ZMod 2)) where
  toFun γ := Multiplicative.ofAdd (liftChar C g g' γ)
  map_one' := by simp [liftChar]
  map_mul' γ δ := by
    show Multiplicative.ofAdd (liftChar C g g' (γ * δ))
      = Multiplicative.ofAdd (liftChar C g g' γ) * Multiplicative.ofAdd (liftChar C g g' δ)
    rw [liftChar_add C g g' h, ofAdd_add]
  continuous_toFun := by
    classical
    exact (continuous_of_discreteTopology (f := fun p : C.cover × C.cover =>
      Multiplicative.ofAdd (if p.1 = p.2 then (0 : ZMod 2) else 1))).comp
      ((map_continuous g).prodMk (map_continuous g'))

/-- **Transitivity of the torsor action**: `g'` is the `liftDiff`-twist of `g`. -/
lemma scalarTwist_liftDiff (g g' : ContinuousMonoidHom Γ C.cover)
    (h : ∀ γ, C.p (g γ) = C.p (g' γ)) :
    scalarTwist C g (liftDiff C g g' h) = g' := by
  ext γ
  show g γ * C.z ^ ((Multiplicative.ofAdd (liftChar C g g' γ)).toAdd).val = g' γ
  rw [toAdd_ofAdd]
  exact (liftChar_rep C g g' h γ).symm

/-- **The fibre of lifts over a fixed base is a torsor**: twisting `g₀` by a character bijects
`Hom_cont(Γ, 𝔽₂)` with the continuous-hom lifts sharing `g₀`'s projection under `p`.  Hence
every such fibre has exactly `|Hom_cont(Γ, 𝔽₂)|` elements — the "8 lifts" of Lemma 8.3. -/
noncomputable def fiberLiftEquiv (g₀ : ContinuousMonoidHom Γ C.cover) :
    ContinuousMonoidHom Γ (Multiplicative (ZMod 2))
      ≃ {g : ContinuousMonoidHom Γ C.cover // ∀ γ, C.p (g γ) = C.p (g₀ γ)} where
  toFun c := ⟨scalarTwist C g₀ c, fun γ => p_comp_scalarTwist C g₀ c γ⟩
  invFun g := liftDiff C g₀ g.1 (fun γ => (g.2 γ).symm)
  left_inv c :=
    scalarTwist_left_injective C g₀ (scalarTwist_liftDiff C g₀ (scalarTwist C g₀ c) _)
  right_inv g := Subtype.ext (scalarTwist_liftDiff C g₀ g.1 (fun γ => (g.2 γ).symm))

end Twist

end SectionEight

end GQ2
