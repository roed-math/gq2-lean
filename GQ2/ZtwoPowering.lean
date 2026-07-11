import GQ2.Zhat
import GQ2.MaxProP
import GQ2.PropOneOne
import GQ2.Reconstruction

/-!
# ℤ₂-powering on pro-2 groups  (ticket P-21)

The foundations layer requested by P-08's escalation (`docs/section3-extraction.md`
§Escalations 4): `x ^ u` for a 2-adic exponent `u ∈ ℤ₂` and `x` in any **pro-2** group, with the
laws the §3 proofs consume.  Everything is proved (no axioms, no sorries; std-3 throughout).

## Contents

**(i) The projection `ℤ̂ ↠ ℤ₂` and the seam isomorphism** (T-12's deferred nice-to-have).
* `zhatProjTwo : ℤ̂ → Multiplicative ℤ₂` — defined as `γ ↦ (ofAdd 1) ^ᶻ γ`, i.e. as a
  `ẑ`-power (T-06), so continuity/hom-ness/`ofInt`-anchors come from the existing API.
* `zhatProjTwo_surjective`, `ker_zhatProjTwo : ker = proPKernel 2 ℤ̂`.
* `ztwoEquivPadic : maxProPQuotient 2 ℤ̂ ≃ₜ* Multiplicative ℤ₂`, pinned by
  `maxProPMk (ofInt 1) ↦ ofAdd 1`.  Since `Ztwo := maxProPQuotient 2 Zhat`
  (`GQ2/BoundaryFrame.lean`, definitionally), **this is the `ι` of
  `SectionThree.prop_3_10_local_marked`** and the identification P-09's `nuTwo`-surjectivity
  can compose with.

**(ii) `ℤ₂`-powering on pro-2 groups.**
* `zpowZtwo (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) : P`, bundled as
  `zpowZtwoHom hP x : Multiplicative ℤ₂ →ₜ* P`; built from `zpowHatHom` through (i) via the
  universal property `maxProPHomEquiv`.
* Anchors: `zpowZtwo_intCast` (`= x ^ n` on integer exponents), exponent additivity (it is a
  hom), the composition law `zpowZtwo_zpowZtwo : (x^u)^v = x^{uv}`, naturality
  `map_zpowZtwo`, and the **uniqueness principle** `zpowZtwoHom_unique` (a continuous hom
  `ℤ₂ → P` is determined by its value at `1` — the tool for identifying constructed maps
  with powerings).
* **Bijectivity**: `zpowZtwo_bijective` (`x ↦ x^u` bijective for `u ∈ ℤ₂ˣ`, inverse `x ↦ x^{u⁻¹}`)
  and `pow_bijective_of_odd` (odd integer powers; P-08's "cube roots", inverse `x ↦ x^{m⁻¹}`).

**(iii) The `η`-facts** (shared P-07 `lemma_3_5_injective` / P-08 `prop_3_8_classification`
prerequisite).
* `isProP_two_unitsPadicInt : IsProP 2 ℤ₂ˣ` — so `η ^ u` makes sense for `η ∈ ℤ₂ˣ`, `u ∈ ℤ₂`.
* `zpowZtwo_injective_of_norm` — **`η`-injectivity**: if `‖η − 1‖ = 2⁻²` (i.e. `v₂(η−1) = 2`;
  the paper's `η = (−3)⁻¹`, cf. `norm_inv_neg_three_sub_one`) then `u ↦ η ^ u` is injective.
  This is the consumable form of the paper's "`η` topologically generates `1 + 4ℤ₂`"
  (Lemma 3.5's injectivity row and Prop. 3.8's `Ȳ`-coordinate forcing use exactly injectivity).

**(iv) Pro-2 Frattini/Burnside criterion — deliberately deferred (phase 2 of P-21).**
"Surjective on `G/Φ(G)` ⇒ surjective" for pro-2 `G`.  Its only §3 consumers (`lemma_3_7` /
`prop_3_8_lift`'s surjectivity legs) remain blocked on the escalation's (a) HNN gap regardless.
Route when picked up: a proper closed subgroup of a profinite group lies in a proper open one
(`⨅ (H·U) = H` by compactness); maximal open subgroups of pro-`p` groups are normal of index `p`
(finite `p`-groups: nilpotent ⇒ normalizer condition ⇒ maximal-normal; simple `p`-group ≅ `ℤ/p`);
`Φ(G) ≤ M` for every maximal `M`.

## Conventions

Multiplicative throughout: exponents live in `Multiplicative ℤ_[2]` (group law = addition of
exponents), matching `Zhat`'s convention (T-06); `zpowZtwo` takes the *additive* `u : ℤ_[2]` and
wraps it.  `2`-specific facts use `p = 2` instances (`Fact (Nat.Prime 2)` is found automatically).
-/

open scoped Classical

namespace GQ2

open Multiplicative

/-! ## The density/extension workhorse

`ℤ ⊆ ℤ₂` (indeed `ℕ ⊆ ℤ₂`) is dense, so a continuous monoid hom out of `Multiplicative ℤ₂`
into a Hausdorff monoid is determined by its value at `ofAdd 1`.  This single lemma powers all
the algebraic laws of `zpowZtwo` below. -/

/-- Two continuous monoid homs `Multiplicative ℤ₂ →* M` (`M` Hausdorff) agreeing at `ofAdd 1`
are equal.  (Via `DenseRange.addChar_eq_of_eval_one_eq` and `AddChar ℤ₂ M ≃ (Multiplicative ℤ₂ →* M)`.) -/
lemma multPadicIntHom_ext {M : Type*} [Monoid M] [TopologicalSpace M] [T2Space M]
    {f g : Multiplicative ℤ_[2] →* M} (hf : Continuous f) (hg : Continuous g)
    (h : f (ofAdd (1 : ℤ_[2])) = g (ofAdd (1 : ℤ_[2]))) : f = g := by
  have hext : AddChar.toMonoidHomEquiv.symm f = AddChar.toMonoidHomEquiv.symm g :=
    PadicInt.denseRange_natCast.addChar_eq_of_eval_one_eq
      (hf.comp continuous_ofAdd) (hg.comp continuous_ofAdd) (by simpa using h)
  simpa using congrArg AddChar.toMonoidHomEquiv hext

/-! ## `ℤ₂`-powering of an element of `2`-power order

The elementary building block: if `g ^ 2^k = 1` then `u ↦ g ^ (u mod 2^k)` is a continuous
monoid hom `Multiplicative ℤ₂ →* Q`.  Used for the kernel computation of `zhatProjTwo` (where
`Q` is a finite quotient of `ℤ̂`), and reusable for any finite 2-group target. -/

section PowOfTwoPowOrder

variable {Q : Type*} [Group Q]

/-- `u ↦ g ^ (u mod 2^k)` for an element `g` with `g ^ 2^k = 1`. -/
noncomputable def powZModTwoHom (g : Q) (k : ℕ) (hg : g ^ 2 ^ k = 1) :
    Multiplicative ℤ_[2] →* Q where
  toFun u := g ^ (PadicInt.toZModPow k u.toAdd).val
  map_one' := by
    haveI : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
    simp
  map_mul' a b := by
    haveI : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
    have hab : (PadicInt.toZModPow k (a * b).toAdd).val
        = ((PadicInt.toZModPow k a.toAdd).val + (PadicInt.toZModPow k b.toAdd).val) % 2 ^ k := by
      rw [show (a * b).toAdd = a.toAdd + b.toAdd from rfl, map_add, ZMod.val_add]
    rw [hab, ← pow_eq_pow_mod _ hg, pow_add]

/-- The fibres of `toZModPow k : ℤ₂ → ℤ/2^k` are open (cosets of the ball `span {2^k}`). -/
lemma isOpen_fiber_toZModPow (k : ℕ) (c : ZMod (2 ^ k)) :
    IsOpen (PadicInt.toZModPow (p := 2) k ⁻¹' {c}) := by
  rcases Set.eq_empty_or_nonempty (PadicInt.toZModPow (p := 2) k ⁻¹' {c}) with he | ⟨x₀, hx₀⟩
  · rw [he]; exact isOpen_empty
  · have hx₀' : PadicInt.toZModPow (p := 2) k x₀ = c := hx₀
    have hker : IsOpen {y : ℤ_[2] | ‖y‖ ≤ ((2 : ℕ) : ℝ) ^ (-(k : ℤ))} := by
      have hball : {y : ℤ_[2] | ‖y‖ ≤ ((2 : ℕ) : ℝ) ^ (-(k : ℤ))}
          = Metric.ball (0 : ℤ_[2]) (((2 : ℕ) : ℝ) ^ (-(k : ℤ) + 1)) := by
        ext y
        rw [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq,
          PadicInt.norm_le_pow_iff_norm_lt_pow_add_one]
      rw [hball]
      exact Metric.isOpen_ball
    have hset : PadicInt.toZModPow (p := 2) k ⁻¹' {c}
        = (fun y => y - x₀) ⁻¹' {y : ℤ_[2] | ‖y‖ ≤ ((2 : ℕ) : ℝ) ^ (-(k : ℤ))} := by
      ext y
      show PadicInt.toZModPow (p := 2) k y ∈ ({c} : Set _)
        ↔ ‖y - x₀‖ ≤ ((2 : ℕ) : ℝ) ^ (-(k : ℤ))
      rw [Set.mem_singleton_iff, PadicInt.norm_le_pow_iff_mem_span_pow,
        ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero, hx₀']
    rw [hset]
    exact hker.preimage (continuous_id.sub continuous_const)

/-- Every `toZModPow`-preimage is open (union of open fibres): `toZModPow k` is locally
constant. -/
lemma isOpen_preimage_toZModPow (k : ℕ) (T : Set (ZMod (2 ^ k))) :
    IsOpen (PadicInt.toZModPow (p := 2) k ⁻¹' T) := by
  rw [← Set.biUnion_preimage_singleton]
  exact isOpen_biUnion fun c _ => isOpen_fiber_toZModPow k c

/-- `powZModTwoHom` is continuous: it factors through the locally constant `toZModPow k`. -/
lemma continuous_powZModTwoHom [TopologicalSpace Q] (g : Q) (k : ℕ) (hg : g ^ 2 ^ k = 1) :
    Continuous (powZModTwoHom g k hg) := by
  refine IsLocallyConstant.continuous (fun s => ?_)
  show IsOpen ((fun u : Multiplicative ℤ_[2] =>
    g ^ (PadicInt.toZModPow k u.toAdd).val) ⁻¹' s)
  have hfact : (fun u : Multiplicative ℤ_[2] => g ^ (PadicInt.toZModPow k u.toAdd).val) ⁻¹' s
      = Multiplicative.toAdd ⁻¹'
        (PadicInt.toZModPow (p := 2) k ⁻¹' {c : ZMod (2 ^ k) | g ^ c.val ∈ s}) := rfl
  rw [hfact]
  exact (isOpen_preimage_toZModPow k _).preimage continuous_toAdd

end PowOfTwoPowOrder

/-- `g ^ ((n : ℤ/2^k).val) = g ^ n` for an element with `g ^ 2^k = 1`: reducing an integer
exponent mod `2^k` does not change the power. -/
private lemma pow_val_intCast_eq_zpow {Q : Type*} [Group Q] (g : Q) (k : ℕ)
    (hg : g ^ 2 ^ k = 1) (n : ℤ) :
    g ^ ((n : ZMod (2 ^ k))).val = g ^ n := by
  haveI : NeZero (2 ^ k) := ⟨(Nat.two_pow_pos k).ne'⟩
  have hmod : (((n : ZMod (2 ^ k)).val : ℤ)) ≡ n [ZMOD ((2 ^ k : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  have hdvd : (orderOf g : ℤ) ∣ (n - ((n : ZMod (2 ^ k)).val : ℤ)) := by
    have h2k : ((2 ^ k : ℕ) : ℤ) ∣ (n - ((n : ZMod (2 ^ k)).val : ℤ)) :=
      Int.ModEq.dvd hmod
    exact dvd_trans (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hg)) h2k
  have hone : g ^ (n - ((n : ZMod (2 ^ k)).val : ℤ)) = 1 :=
    orderOf_dvd_iff_zpow_eq_one.mp hdvd
  rw [zpow_sub] at hone
  rw [← zpow_natCast g ((n : ZMod (2 ^ k))).val]
  exact (mul_inv_eq_one.mp hone).symm

/-! ## The canonical projection `ℤ̂ ↠ ℤ₂`  (part (i))

`zhatProjTwo := γ ↦ (ofAdd 1) ^ᶻ γ` — the `ẑ`-power of `1 ∈ ℤ₂` (T-06 machinery), which on
integer exponents is just `n ↦ n : ℤ → ℤ₂`. -/

/-- The dense embedding `ℤ → ℤ̂`, bundled (multiplicative convention, as everywhere in
`GQ2/Zhat.lean`). -/
noncomputable def Zhat.ofIntHom : Multiplicative ℤ →* Zhat where
  toFun n := Zhat.ofInt n.toAdd
  map_one' := Zhat.ofInt_zero
  map_mul' _ _ := Zhat.ofInt_add _ _

/-- `ofInt` turns integer powers of `ofInt 1` into `ofInt` of the integer. -/
lemma Zhat.ofInt_one_zpow (n : ℤ) : (Zhat.ofInt 1) ^ n = Zhat.ofInt n := by
  have h := map_zpow Zhat.ofIntHom (ofAdd (1 : ℤ)) n
  rw [show (ofAdd (1 : ℤ)) ^ n = ofAdd n by rw [← ofAdd_zsmul, smul_eq_mul, mul_one]] at h
  exact h.symm

/-- **The canonical projection `ℤ̂ → ℤ₂`** (multiplicatively: onto `Multiplicative ℤ₂`), as the
`ẑ`-power morphism of `ofAdd 1`: `γ ↦ (ofAdd 1) ^ᶻ γ`.  On `ℤ ⊆ ℤ̂` it is the inclusion
`ℤ ⊆ ℤ₂` (`zhatProjTwo_ofInt`); it realizes `ℤ₂` as the maximal pro-2 quotient of `ℤ̂`
(`ker_zhatProjTwo`, `ztwoEquivPadic`). -/
noncomputable def zhatProjTwo : ContinuousMonoidHom Zhat (Multiplicative ℤ_[2]) :=
  (zpowHatHom (G := Multiplicative ℤ_[2]) (ofAdd (1 : ℤ_[2]))).hom

@[simp] lemma zhatProjTwo_ofInt (n : ℤ) :
    zhatProjTwo (Zhat.ofInt n) = ofAdd ((n : ℤ_[2])) := by
  have h : zhatProjTwo (Zhat.ofInt n) = (ofAdd (1 : ℤ_[2])) ^ᶻ (Zhat.ofInt n) := rfl
  rw [h, zpowHat_ofInt, ← ofAdd_zsmul, zsmul_eq_mul, mul_one]

/-- `zhatProjTwo` is surjective (closed range ⊇ the dense `ℕ ⊆ ℤ₂`). -/
lemma zhatProjTwo_surjective : Function.Surjective zhatProjTwo := by
  have hclosed : IsClosed (Set.range zhatProjTwo) :=
    (isCompact_range zhatProjTwo.continuous_toFun).isClosed
  have hnat : DenseRange (fun n : ℕ => ofAdd ((n : ℤ_[2]))) := PadicInt.denseRange_natCast
  have hsub : Set.range (fun n : ℕ => ofAdd ((n : ℤ_[2]))) ⊆ Set.range zhatProjTwo := by
    rintro _ ⟨n, rfl⟩
    exact ⟨Zhat.ofInt n, by rw [zhatProjTwo_ofInt]; norm_cast⟩
  have hdense : Dense (Set.range zhatProjTwo) := Dense.mono hsub hnat
  rw [← Set.range_eq_univ, ← hclosed.closure_eq]
  exact hdense.closure_eq

/-- The kernel of `zhatProjTwo` is contained in the pro-2 kernel: any element of `ℤ̂` killed by
the projection to `ℤ₂` dies in **every** finite 2-group quotient.  *Proof idea*: for an open
normal `U` with 2-group quotient, the quotient map `q : ℤ̂ → ℤ̂/U` and the composite of
`zhatProjTwo` with "`ℤ₂`-powering of `q(ofInt 1)`" (`powZModTwoHom`) are continuous maps
agreeing on the dense `ℤ ⊆ ℤ̂`, hence equal (`funext_ofInt`); the second visibly kills
`ker zhatProjTwo`. -/
theorem ker_zhatProjTwo_le : zhatProjTwo.toMonoidHom.ker ≤ proPKernel 2 Zhat := by
  intro γ hγ
  rw [MonoidHom.mem_ker] at hγ
  have hγ' : zhatProjTwo γ = 1 := hγ
  refine Subgroup.mem_iInf.mpr fun ⟨U, hU⟩ => ?_
  -- the quotient is discrete ({1} is open: its mk-preimage is the open U), hence T2
  haveI hdisc : DiscreteTopology (Zhat ⧸ U.toSubgroup) := by
    refine discreteTopology_of_isOpen_singleton_one ?_
    have hpre : (QuotientGroup.mk : Zhat → Zhat ⧸ U.toSubgroup) ⁻¹' {1}
        = (U.toSubgroup : Set Zhat) := by
      ext δ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
        QuotientGroup.eq_one_iff]
    rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
    exact U.isOpen'
  haveI hT2 : T2Space (Zhat ⧸ U.toSubgroup) := DiscreteTopology.toT2Space
  -- the generator image and its 2-power order
  set q : Zhat →* (Zhat ⧸ U.toSubgroup) := QuotientGroup.mk' U.toSubgroup with hqdef
  obtain ⟨k, hk⟩ := hU (q (Zhat.ofInt 1))
  -- q agrees with ℤ₂-powering of q(ofInt 1) through zhatProjTwo
  have hagree : (fun δ : Zhat => q δ)
      = fun δ : Zhat => powZModTwoHom (q (Zhat.ofInt 1)) k hk (zhatProjTwo δ) := by
    refine @Zhat.funext_ofInt (Zhat ⧸ U.toSubgroup) _ hT2 _ _ continuous_quot_mk
      ((continuous_powZModTwoHom _ k hk).comp zhatProjTwo.continuous_toFun) fun n => ?_
    -- LHS: q (ofInt n) = q(ofInt 1)^n; RHS: g ^ (n mod 2^k) = g^n
    rw [zhatProjTwo_ofInt]
    show q (Zhat.ofInt n)
      = (q (Zhat.ofInt 1)) ^ ((PadicInt.toZModPow k (ofAdd ((n : ℤ_[2]))).toAdd)).val
    rw [show (ofAdd ((n : ℤ_[2]))).toAdd = ((n : ℤ_[2])) from rfl, map_intCast,
      pow_val_intCast_eq_zpow _ k hk n, ← map_zpow, Zhat.ofInt_one_zpow]
  -- evaluate at γ
  have hγU : q γ = 1 := by
    have heval := congrFun hagree γ
    rwa [hγ', map_one] at heval
  rwa [hqdef, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hγU

/-- **`ker zhatProjTwo = proPKernel 2 ℤ̂`**: the projection to `ℤ₂` realizes exactly the
maximal pro-2 quotient of `ℤ̂` (the missing direction is `proPKernel_le_ker` for the pro-2
target `ℤ₂`, `GQ2/PropOneOne.lean`). -/
theorem ker_zhatProjTwo : zhatProjTwo.toMonoidHom.ker = proPKernel 2 Zhat :=
  le_antisymm ker_zhatProjTwo_le
    (proPKernel_le_ker PropOneOne.isProP_two_multPadicInt zhatProjTwo)

/-! ## The seam isomorphism `maxPro2(ℤ̂) ≅ ℤ₂`  (part (i), packaged)

`Ztwo := maxProPQuotient 2 Zhat` in `GQ2/BoundaryFrame.lean` (definitionally), so
`ztwoEquivPadic` **is** the `ι : Ztwo ≃ₜ* Multiplicative ℤ₂` of
`SectionThree.prop_3_10_local_marked`, pinned by `ztwoOne ↦ ofAdd 1`
(`ztwoEquivPadic_ofInt_one`). -/

/-- The descent of `zhatProjTwo` to the maximal pro-2 quotient. -/
noncomputable def ztwoDescend :
    ContinuousMonoidHom (maxProPQuotient 2 Zhat) (Multiplicative ℤ_[2]) :=
  quotientLift (proPKernel 2 Zhat) zhatProjTwo (le_of_eq ker_zhatProjTwo.symm)

@[simp] lemma ztwoDescend_maxProPMk (γ : Zhat) :
    ztwoDescend (maxProPMk 2 Zhat γ) = zhatProjTwo γ := rfl

lemma ztwoDescend_bijective : Function.Bijective ztwoDescend := by
  constructor
  · rw [show (⇑ztwoDescend : maxProPQuotient 2 Zhat → Multiplicative ℤ_[2])
      = ⇑ztwoDescend.toMonoidHom from rfl, injective_iff_map_eq_one ztwoDescend.toMonoidHom]
    intro x hx
    obtain ⟨γ, rfl⟩ := quotientMk_surjective (proPKernel 2 Zhat) x
    exact (quotientMk_eq_one_iff (proPKernel 2 Zhat)).mpr
      (ker_zhatProjTwo ▸ MonoidHom.mem_ker.mpr hx)
  · intro u
    obtain ⟨γ, hγ⟩ := zhatProjTwo_surjective u
    exact ⟨maxProPMk 2 Zhat γ, hγ⟩

/-- **`maxPro2(ℤ̂) ≅ ℤ₂`** — the T-12 "nice-to-have", and the `ι`-seam of
`prop_3_10_local_marked`/P-09's `nuTwo` (as `Ztwo = maxProPQuotient 2 Zhat` definitionally). -/
noncomputable def ztwoEquivPadic :
    ContinuousMulEquiv (maxProPQuotient 2 Zhat) (Multiplicative ℤ_[2]) :=
  continuousMulEquivOfBijective ztwoDescend ztwoDescend_bijective

@[simp] lemma ztwoEquivPadic_apply (x : maxProPQuotient 2 Zhat) :
    ztwoEquivPadic x = ztwoDescend x := rfl

/-- The generator pin: `ztwoOne = maxProPMk (ofInt 1) ↦ ofAdd 1` (the normalization
`prop_3_10_local_marked` requires of `ι`). -/
@[simp] lemma ztwoEquivPadic_ofInt_one :
    ztwoEquivPadic (maxProPMk 2 Zhat (Zhat.ofInt 1)) = ofAdd (1 : ℤ_[2]) := by
  rw [ztwoEquivPadic_apply, ztwoDescend_maxProPMk, zhatProjTwo_ofInt, Int.cast_one]

lemma ztwoEquivPadic_symm_ofAdd_one :
    ztwoEquivPadic.symm (ofAdd (1 : ℤ_[2])) = maxProPMk 2 Zhat (Zhat.ofInt 1) := by
  rw [← ztwoEquivPadic_ofInt_one]
  exact ztwoEquivPadic.symm_apply_apply _

/-! ## `ℤ₂`-powering on pro-2 groups  (part (ii))

For `x` in a pro-2 profinite group `P`, the `ẑ`-power morphism `zpowHatHom x : ℤ̂ ⟶ P` (T-06)
kills `proPKernel 2 ℤ̂` (universal property, since `P` is pro-2), so through
`ker zhatProjTwo = proPKernel 2 ℤ̂` (part (i)) it factors through `ℤ₂`: this is `zpowZtwoHom`.
Everything else follows from the extension-by-density workhorse `multPadicIntHom_ext`. -/

section ZpowZtwo

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- Evaluation of the `maxProPHomEquiv`-descended hom on classes: the descent of `F` at
`maxProPMk γ` is `F γ`.  (The `.symm` of the universal property is `quotientLift`.) -/
lemma maxProPHomEquiv_symm_apply_maxProPMk {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (hP : IsProP p P) (F : ContinuousMonoidHom G P) (γ : G) :
    (maxProPHomEquiv hP).symm F (maxProPMk p G γ) = F γ :=
  DFunLike.congr_fun ((maxProPHomEquiv hP).apply_symm_apply F) γ

/-- **The `ℤ₂`-power morphism** of `x` in a pro-2 group `P`: the unique continuous extension of
`n ↦ xⁿ` to exponents in `ℤ₂`, as a continuous hom `Multiplicative ℤ₂ →ₜ* P`.  Built by
factoring `zpowHatHom x : ℤ̂ ⟶ P` through `zhatProjTwo` via the universal property of the
maximal pro-2 quotient and the part-(i) isomorphism. -/
noncomputable def zpowZtwoHom (hP : IsProP 2 P) (x : P) :
    ContinuousMonoidHom (Multiplicative ℤ_[2]) P :=
  ((maxProPHomEquiv hP).symm ((zpowHatHom x).hom)).comp
    (ztwoEquivPadic.symm : ContinuousMonoidHom (Multiplicative ℤ_[2]) (maxProPQuotient 2 Zhat))

/-- `x ^ u` for a 2-adic exponent `u ∈ ℤ₂` (`x` in a pro-2 group; additive exponent
convention: `zpowZtwo hP x (u + v) = zpowZtwo hP x u * zpowZtwo hP x v`). -/
noncomputable def zpowZtwo (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) : P :=
  zpowZtwoHom hP x (ofAdd u)

lemma continuous_zpowZtwo (hP : IsProP 2 P) (x : P) : Continuous (zpowZtwo hP x) :=
  (zpowZtwoHom hP x).continuous_toFun.comp continuous_ofAdd

/-- The generator pin: `x ^ (1 : ℤ₂) = x`. -/
lemma zpowZtwoHom_ofAdd_one (hP : IsProP 2 P) (x : P) :
    zpowZtwoHom hP x (ofAdd (1 : ℤ_[2])) = x := by
  show ((maxProPHomEquiv hP).symm ((zpowHatHom x).hom))
    (ztwoEquivPadic.symm (ofAdd (1 : ℤ_[2]))) = x
  rw [ztwoEquivPadic_symm_ofAdd_one, maxProPHomEquiv_symm_apply_maxProPMk]
  show x ^ᶻ (Zhat.ofInt 1) = x
  rw [zpowHat_ofInt, zpow_one]

@[simp] lemma zpowZtwo_one_exp (hP : IsProP 2 P) (x : P) : zpowZtwo hP x 1 = x :=
  zpowZtwoHom_ofAdd_one hP x

/-- `ℤ₂`-powers extend ordinary integer powers. -/
@[simp] lemma zpowZtwo_intCast (hP : IsProP 2 P) (x : P) (n : ℤ) :
    zpowZtwo hP x ((n : ℤ_[2])) = x ^ n := by
  have h1 : (ofAdd ((n : ℤ_[2]))) = (ofAdd (1 : ℤ_[2])) ^ n := by
    rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one]
  show zpowZtwoHom hP x (ofAdd ((n : ℤ_[2]))) = x ^ n
  rw [h1, map_zpow, zpowZtwoHom_ofAdd_one]

@[simp] lemma zpowZtwo_natCast (hP : IsProP 2 P) (x : P) (n : ℕ) :
    zpowZtwo hP x ((n : ℤ_[2])) = x ^ n := by
  simpa using zpowZtwo_intCast hP x (n : ℤ)

/-- Exponent additivity (the hom law, in `zpowZtwo` clothing). -/
lemma zpowZtwo_add (hP : IsProP 2 P) (x : P) (u v : ℤ_[2]) :
    zpowZtwo hP x (u + v) = zpowZtwo hP x u * zpowZtwo hP x v := by
  rw [zpowZtwo, zpowZtwo, zpowZtwo, ← map_mul, ← ofAdd_add]

/-- **Uniqueness/identification principle**: any continuous hom `φ : ℤ₂ → P` *is* the
`ℤ₂`-powering of its value at `1`.  (The tool for recognizing constructed maps as powerings —
e.g. P-08's `Θ_b` legs.) -/
lemma zpowZtwoHom_unique (hP : IsProP 2 P) {φ : Multiplicative ℤ_[2] →* P}
    (hφ : Continuous φ) (u : ℤ_[2]) : φ (ofAdd u) = zpowZtwo hP (φ (ofAdd 1)) u := by
  have hext : φ = (zpowZtwoHom hP (φ (ofAdd 1))).toMonoidHom := by
    refine multPadicIntHom_ext hφ (zpowZtwoHom hP _).continuous_toFun ?_
    exact (zpowZtwoHom_ofAdd_one hP _).symm
  exact DFunLike.congr_fun hext (ofAdd u)

/-- **Composition law**: `(x ^ u) ^ v = x ^ (u * v)`. -/
lemma zpowZtwo_zpowZtwo (hP : IsProP 2 P) (x : P) (u v : ℤ_[2]) :
    zpowZtwo hP (zpowZtwo hP x u) v = zpowZtwo hP x (u * v) := by
  have hψcont : Continuous fun w : Multiplicative ℤ_[2] => ofAdd (u * w.toAdd) :=
    continuous_ofAdd.comp ((continuous_const_mul u).comp continuous_toAdd)
  have h := zpowZtwoHom_unique hP
    (φ := (zpowZtwoHom hP x).toMonoidHom.comp
      (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft u)))
    ((zpowZtwoHom hP x).continuous_toFun.comp hψcont) v
  -- both sides of h are definitionally `ℤ₂`-powers; bridge by `rfl` and normalize `u * 1`
  have hl : ((zpowZtwoHom hP x).toMonoidHom.comp
      (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft u))) (ofAdd v)
      = zpowZtwo hP x (u * v) := rfl
  have hr : ((zpowZtwoHom hP x).toMonoidHom.comp
      (AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft u))) (ofAdd 1)
      = zpowZtwo hP x (u * 1) := rfl
  rw [hl, hr, mul_one] at h
  exact h.symm

/-- Powering the identity: `1 ^ u = 1`. -/
@[simp] lemma zpowZtwo_one_base (hP : IsProP 2 P) (u : ℤ_[2]) :
    zpowZtwo hP (1 : P) u = 1 := by
  have h := zpowZtwoHom_unique hP (φ := (1 : Multiplicative ℤ_[2] →* P)) continuous_const u
  simpa using h.symm

/-- **Unit-power bijectivity**: for `u ∈ ℤ₂ˣ`, `x ↦ x ^ u` is a bijection of `P`, with inverse
`x ↦ x ^ u⁻¹`. -/
lemma zpowZtwo_bijective (hP : IsProP 2 P) (u : ℤ_[2]ˣ) :
    Function.Bijective (fun x : P => zpowZtwo hP x ((u : ℤ_[2]))) := by
  have hcancel : ∀ (a b : ℤ_[2]ˣ) (x : P),
      zpowZtwo hP (zpowZtwo hP x ((a : ℤ_[2]))) ((b : ℤ_[2]))
        = zpowZtwo hP x (((a * b : ℤ_[2]ˣ) : ℤ_[2])) := by
    intro a b x
    rw [zpowZtwo_zpowZtwo, Units.val_mul]
  refine Function.bijective_iff_has_inverse.mpr
    ⟨fun y => zpowZtwo hP y (((u⁻¹ : ℤ_[2]ˣ)) : ℤ_[2]), fun x => ?_, fun y => ?_⟩
  · show zpowZtwo hP (zpowZtwo hP x ((u : ℤ_[2]))) (((u⁻¹ : ℤ_[2]ˣ)) : ℤ_[2]) = x
    rw [hcancel, mul_inv_cancel, Units.val_one, zpowZtwo_one_exp]
  · show zpowZtwo hP (zpowZtwo hP y (((u⁻¹ : ℤ_[2]ˣ)) : ℤ_[2])) ((u : ℤ_[2])) = y
    rw [hcancel, inv_mul_cancel, Units.val_one, zpowZtwo_one_exp]

/-- Odd integers are units of `ℤ₂`. -/
lemma isUnit_intCast_of_odd {m : ℤ} (hm : Odd m) : IsUnit ((m : ℤ_[2])) := by
  rw [PadicInt.isUnit_iff, PadicInt.norm_intCast_eq_one_iff, Int.isCoprime_iff_gcd_eq_one]
  exact Nat.coprime_two_right.mpr (Int.natAbs_odd.mpr hm)


/-- **Naturality**: continuous homs of pro-2 groups commute with `ℤ₂`-powers. -/
lemma map_zpowZtwo {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hP : IsProP 2 P) (hQ : IsProP 2 Q)
    (f : ContinuousMonoidHom P Q) (x : P) (u : ℤ_[2]) :
    f (zpowZtwo hP x u) = zpowZtwo hQ (f x) u := by
  have h := zpowZtwoHom_unique hQ
    (φ := f.toMonoidHom.comp (zpowZtwoHom hP x).toMonoidHom)
    (f.continuous_toFun.comp (zpowZtwoHom hP x).continuous_toFun) u
  simp only [MonoidHom.comp_apply] at h
  calc f (zpowZtwo hP x u) = zpowZtwo hQ (f (zpowZtwoHom hP x (ofAdd 1))) u := h
    _ = zpowZtwo hQ (f x) u := by rw [zpowZtwoHom_ofAdd_one]

/-- **Bridge to `ẑ`-powers**: on a pro-2 group, `x ^ᶻ γ` computes the `ℤ₂`-power at the
projection of `γ` — the profinite exponents of T-06 (e.g. `ω₂`) factor through `ℤ₂` here. -/
lemma zpowHat_eq_zpowZtwo (hP : IsProP 2 P) (x : P) (γ : Zhat) :
    x ^ᶻ γ = zpowZtwo hP x (zhatProjTwo γ).toAdd := by
  have hfun : (fun γ : Zhat => x ^ᶻ γ)
      = fun γ : Zhat => zpowZtwo hP x (zhatProjTwo γ).toAdd := by
    refine Zhat.funext_ofInt (continuous_zpowHat x)
      ((continuous_zpowZtwo hP x).comp
        (continuous_toAdd.comp zhatProjTwo.continuous_toFun)) fun n => ?_
    rw [zpowHat_ofInt, zhatProjTwo_ofInt]
    show x ^ n = zpowZtwo hP x ((n : ℤ_[2]))
    rw [zpowZtwo_intCast]
  exact congrFun hfun γ

end ZpowZtwo

/-! ## `ℤ₂ˣ` is pro-2, and the `η`-injectivity  (part (iii))

The shared P-07/P-08 prerequisite.  Level-tracking is done **algebraically** (divisibility by
`2^k`, with unit witnesses for exact levels) — `p = 2` is what makes `ℤ₂ˣ` pro-2: every unit is
`≡ 1 (mod 2)`, and squaring gains exactly one level.  Real norms appear only once, bridging to
the open-ball description of a neighbourhood in `ℤ₂ˣ`. -/

section UnitsProTwo

/-- `2` is not a unit of `ℤ₂`. -/
lemma not_isUnit_two : ¬ IsUnit (2 : ℤ_[2]) := by
  intro h
  have hmem : (2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := by
    rw [PadicInt.maximalIdeal_eq_span_p]
    exact Ideal.mem_span_singleton_self _
  exact (IsLocalRing.mem_maximalIdeal _).mp hmem h

/-- `1 + 2x` is a unit of `ℤ₂` (its residue mod 2 is 1). -/
lemma isUnit_one_add_two_mul (x : ℤ_[2]) : IsUnit (1 + 2 * x) := by
  by_contra h
  have hmem : (1 + 2 * x : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] :=
    (IsLocalRing.mem_maximalIdeal _).mpr h
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
  have hone : (2 : ℤ_[2]) ∣ 1 := by
    have := dvd_sub hmem (Dvd.intro x rfl)
    simpa using this
  exact not_isUnit_two (isUnit_of_dvd_one hone)

/-- Every `2`-adic unit is `≡ 1 (mod 2)` (`p = 2`: the residue field has one nonzero class). -/
lemma two_dvd_val_sub_one (u : ℤ_[2]ˣ) : (2 : ℤ_[2]) ∣ (u : ℤ_[2]) - 1 := by
  have hne : PadicInt.toZModPow (p := 2) 1 ((u : ℤ_[2])) ≠ 0 := by
    intro h0
    have hmem : ((u : ℤ_[2])) ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := h0
    rw [PadicInt.ker_toZModPow, pow_one, ← PadicInt.maximalIdeal_eq_span_p] at hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hmem u.isUnit
  have h1 : PadicInt.toZModPow (p := 2) 1 ((u : ℤ_[2])) = 1 :=
    (by decide : ∀ c : ZMod (2 ^ 1), c ≠ 0 → c = 1) _ hne
  have hker : ((u : ℤ_[2])) - 1 ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := by
    rw [RingHom.mem_ker, map_sub, map_one, h1, sub_self]
  rwa [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hker

/-- **Level gain under 2-power powers**: `2^{k+1} ∣ u^{2^k} − 1` for every `u ∈ ℤ₂ˣ`
(squaring `1 + 2^m a` gains exactly one level: `(1+2^m a)² = 1 + 2^{m+1}(a + 2^{m-1}a²)`). -/
lemma two_pow_succ_dvd_pow_two_pow_sub_one (u : ℤ_[2]ˣ) (k : ℕ) :
    (2 : ℤ_[2]) ^ (k + 1) ∣ ((u ^ 2 ^ k : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  induction k with
  | zero => simpa using two_dvd_val_sub_one u
  | succ j ih =>
    obtain ⟨a, ha⟩ := ih
    have hval : ((u ^ 2 ^ (j + 1) : ℤ_[2]ˣ) : ℤ_[2]) = ((u ^ 2 ^ j : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, pow_succ]
    refine ⟨a + 2 ^ j * a ^ 2, ?_⟩
    rw [hval, sub_eq_iff_eq_add.mp ha]
    ring

/-- **Exact-level version** (unit-witnessed): if `η − 1 = 4a` with `a ∈ ℤ₂ˣ` (i.e.
`v₂(η−1) = 2` exactly), then `η^{2^k} − 1 = 2^{k+2}·(unit)` — the level grows by exactly one
per squaring, so no 2-power power of `η` is `1`. -/
lemma exists_unit_pow_two_pow_sub_one (η a : ℤ_[2]ˣ)
    (hη : ((η : ℤ_[2])) - 1 = 4 * a) (k : ℕ) :
    ∃ b : ℤ_[2]ˣ, ((η ^ 2 ^ k : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ (k + 2) * b := by
  induction k with
  | zero =>
    refine ⟨a, ?_⟩
    rw [pow_zero, pow_one, hη]
    norm_num
  | succ j ih =>
    obtain ⟨b, hb⟩ := ih
    have hval : ((η ^ 2 ^ (j + 1) : ℤ_[2]ˣ) : ℤ_[2]) = ((η ^ 2 ^ j : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, pow_succ]
    have hu : IsUnit ((b : ℤ_[2]) * (1 + 2 * ((2 : ℤ_[2]) ^ j * b))) :=
      b.isUnit.mul (isUnit_one_add_two_mul _)
    refine ⟨hu.unit, ?_⟩
    rw [hval, sub_eq_iff_eq_add.mp hb, IsUnit.unit_spec]
    ring

/-- The divisibility-to-metric bridge: `2^n ∣ x − 1` means `x` is within `2^{-n}` of `1`. -/
lemma dist_one_le_of_two_pow_dvd {x : ℤ_[2]} {n : ℕ} (h : (2 : ℤ_[2]) ^ n ∣ x - 1) :
    dist x 1 ≤ ((2 : ℕ) : ℝ) ^ (-(n : ℤ)) := by
  rw [dist_eq_norm]
  exact (PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr (Ideal.mem_span_singleton.mpr h)

/-- **`ℤ₂ˣ` is a pro-2 group**: every finite continuous quotient of the 2-adic units is a
2-group.  (Uniform annihilation: any open `U ∋ 1` contains all units within `2^{-(K+1)}` of `1`
— in both the value and the inverse coordinate of the `Units` topology — and
`u^{2^K} ≡ 1 (mod 2^{K+1})` for **every** unit `u`.) -/
theorem isProP_two_unitsPadicInt : IsProP 2 ℤ_[2]ˣ := by
  intro U
  -- unpack the induced (embedProduct) topology into a val-side and an inv-side ball
  obtain ⟨W, hWopen, hWpre⟩ :=
    (Units.isInducing_embedProduct (M := ℤ_[2])).isOpen_iff.mp U.isOpen'
  have h1W : ((1 : ℤ_[2]), MulOpposite.op (1 : ℤ_[2])) ∈ W := by
    have hmem : (1 : ℤ_[2]ˣ) ∈ Units.embedProduct ℤ_[2] ⁻¹' W := by
      rw [hWpre]
      exact U.toSubgroup.one_mem
    simpa [Units.embedProduct_apply] using hmem
  obtain ⟨A, B, hA, hB, h1A, h1B, hABW⟩ := isOpen_prod_iff.mp hWopen _ _ h1W
  obtain ⟨ε₁, hε₁, hballA⟩ := Metric.isOpen_iff.mp hA _ h1A
  have hB' : IsOpen (MulOpposite.op ⁻¹' B : Set ℤ_[2]) :=
    hB.preimage MulOpposite.continuous_op
  have h1B' : (1 : ℤ_[2]) ∈ MulOpposite.op ⁻¹' B := h1B
  obtain ⟨ε₂, hε₂, hballB⟩ := Metric.isOpen_iff.mp hB' _ h1B'
  -- the uniform annihilation exponent
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (lt_min hε₁ hε₂) (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hlt : ((2 : ℕ) : ℝ) ^ (-(((K + 1) : ℕ) : ℤ)) < min ε₁ ε₂ := by
    have heq : ((2 : ℕ) : ℝ) ^ (-(((K + 1) : ℕ) : ℤ)) = ((2 : ℝ)⁻¹) ^ (K + 1) := by
      rw [zpow_neg, ← inv_zpow, zpow_natCast]
      norm_num
    rw [heq]
    calc ((2 : ℝ)⁻¹) ^ (K + 1) ≤ ((2 : ℝ)⁻¹) ^ K :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ K)
      _ < min ε₁ ε₂ := hK
  intro g
  refine ⟨K, ?_⟩
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk_surjective g
  show (QuotientGroup.mk' U.toSubgroup g₀) ^ 2 ^ K = 1
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  -- both coordinates of `embedProduct (g₀ ^ 2^K)` land in the balls
  have hvA : ((g₀ ^ 2 ^ K : ℤ_[2]ˣ) : ℤ_[2]) ∈ A := by
    refine hballA ?_
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt
      (dist_one_le_of_two_pow_dvd (two_pow_succ_dvd_pow_two_pow_sub_one g₀ K))
      (lt_of_lt_of_le hlt (min_le_left _ _))
  have hvB : (((g₀ ^ 2 ^ K)⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) ∈ MulOpposite.op ⁻¹' B := by
    refine hballB ?_
    rw [Metric.mem_ball, show ((g₀ ^ 2 ^ K)⁻¹ : ℤ_[2]ˣ) = (g₀⁻¹) ^ 2 ^ K from
      (inv_pow g₀ (2 ^ K)).symm]
    exact lt_of_le_of_lt
      (dist_one_le_of_two_pow_dvd (two_pow_succ_dvd_pow_two_pow_sub_one g₀⁻¹ K))
      (lt_of_lt_of_le hlt (min_le_right _ _))
  have hmemW : Units.embedProduct ℤ_[2] (g₀ ^ 2 ^ K) ∈ W := by
    apply hABW
    rw [Units.embedProduct_apply]
    exact Set.mem_prod.mpr ⟨hvA, hvB⟩
  have hmemU : (g₀ ^ 2 ^ K : ℤ_[2]ˣ) ∈ Units.embedProduct ℤ_[2] ⁻¹' W := hmemW
  rwa [hWpre] at hmemU

/-! ### The profinite-group instances on `ℤ₂ˣ`

Mathlib provides `IsTopologicalGroup αˣ` (`[ContinuousMul α]`), `CompactSpace αˣ`
(`[T1Space α] [ContinuousMul α] [CompactSpace α]`), and `T2Space αˣ`; total disconnectedness
transfers along the `embedProduct` embedding.  With these, `zpowZtwo` applies to `ℤ₂ˣ`. -/

instance : TotallyDisconnectedSpace ℤ_[2]ᵐᵒᵖ :=
  (MulOpposite.opHomeomorph : ℤ_[2] ≃ₜ ℤ_[2]ᵐᵒᵖ).symm.isEmbedding.isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

instance : TotallyDisconnectedSpace ℤ_[2]ˣ :=
  (Units.isEmbedding_embedProduct (M := ℤ_[2])).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-! ### The `η`-injectivity -/

/-- **`η`-injectivity**: if `η − 1 = 4a` with `a ∈ ℤ₂ˣ` (equivalently `v₂(η − 1) = 2` — the
paper's "`η` topologically generates `1 + 4ℤ₂`", in the form Lemma 3.5's injectivity row and
Prop. 3.8's `Ȳ`-coordinate forcing consume), then `u ↦ η ^ u` is injective on `ℤ₂`-exponents.

*Proof*: a nonzero exponent factors as `c = w·2^m` (`w ∈ ℤ₂ˣ`, `m = v₂(c)`); `η^c = (η^{2^m})^w`,
so `η^c = 1` forces `η^{2^m} = 1` (unit powers are bijective), contradicting the exact level
`η^{2^m} − 1 = 2^{m+2}·(unit) ≠ 0`. -/
theorem zpowZtwo_injective_of_exact_level (η a : ℤ_[2]ˣ)
    (hη : ((η : ℤ_[2])) - 1 = 4 * a) :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt η) := by
  intro c₁ c₂ hc
  by_contra hne
  have hc0 : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  -- the difference exponent kills η
  have hker : zpowZtwo isProP_two_unitsPadicInt η (c₁ - c₂) = 1 := by
    have hadd := zpowZtwo_add isProP_two_unitsPadicInt η (c₁ - c₂) c₂
    rw [sub_add_cancel, hc] at hadd
    exact right_eq_mul.mp hadd
  -- factor the exponent: c = w · 2^m
  set m := (c₁ - c₂).valuation with hm
  set w := PadicInt.unitCoeff hc0 with hwdef
  have hspec : c₁ - c₂ = (w : ℤ_[2]) * 2 ^ m := PadicInt.unitCoeff_spec hc0
  -- η^{c} = (η^{2^m})^{w}
  have hfactor : zpowZtwo isProP_two_unitsPadicInt (η ^ 2 ^ m) ((w : ℤ_[2]))
      = zpowZtwo isProP_two_unitsPadicInt η (c₁ - c₂) := by
    rw [← zpowZtwo_natCast isProP_two_unitsPadicInt η (2 ^ m), zpowZtwo_zpowZtwo]
    congr 1
    rw [hspec]
    push_cast
    ring
  -- unit powers are injective, so η^{2^m} = 1 …
  have hbase : (η ^ 2 ^ m : ℤ_[2]ˣ) = 1 := by
    refine (zpowZtwo_bijective isProP_two_unitsPadicInt w).injective ?_
    show zpowZtwo _ (η ^ 2 ^ m) ((w : ℤ_[2])) = zpowZtwo _ 1 ((w : ℤ_[2]))
    rw [hfactor, hker, zpowZtwo_one_base]
  -- … contradicting the exact level
  obtain ⟨b, hb⟩ := exists_unit_pow_two_pow_sub_one η a hη m
  rw [hbase] at hb
  have hzero : (2 : ℤ_[2]) ^ (m + 2) * (b : ℤ_[2]) = 0 := by
    rw [← hb]
    simp
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℤ_[2]) ≠ 0)) b.ne_zero hzero

/-- The paper's `η = (−3)⁻¹` has exact level 2: `η − 1 = 4·η` (witness `a = η` itself),
since `η − 1 = η(1 − (−3))·… = 4η`. -/
lemma neg_three_inv_exact_level (y : ℤ_[2]ˣ) (hy : (y : ℤ_[2]) = -3) :
    ((y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 4 * ((y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by
  have hinv : ((y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (y : ℤ_[2]) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hsub : ((y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) - 1 = ((y⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - (y : ℤ_[2])) := by
    rw [mul_sub, mul_one, hinv]
  rw [hsub, hy]
  ring

/-- **The P-07/P-08 consumable**: `u ↦ ((−3)⁻¹) ^ u` is injective (`η = y⁻¹` for the class
`y = −3` of Lemma 3.5 / Prop. 3.8). -/
theorem zpowZtwo_injective_neg_three_inv (y : ℤ_[2]ˣ) (hy : (y : ℤ_[2]) = -3) :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt (y⁻¹)) :=
  zpowZtwo_injective_of_exact_level y⁻¹ y⁻¹ (neg_three_inv_exact_level y hy)

end UnitsProTwo

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 3.5 = ⟦lem-markedinitialform⟧
  * Prop 3.8 = ⟦prop-orientationlift⟧ (= proposition 3.9 in current tex)
-/
