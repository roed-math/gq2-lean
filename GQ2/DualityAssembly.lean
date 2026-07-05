import GQ2.Devissage
import GQ2.TrivialSelfDual
import GQ2.TameSimple
import GQ2.DevissageInduction

/-!
# P-13f: assembling `prop_5_15` (deformation duality) from the simple-module case + dévissage

`prop_5_15 : IsSelfDual t A` for every finite elementary `𝔽₂[C]`-module.  Route: the simple modules
are self-dual (trivial module via `trivialSelfDual`; nontrivial simples via `lemma_5_13` + the
degree-one pairing), then `lemma_5_11` (dévissage, `GQ2/Devissage.lean`) two-out-of-three along a
composition series.

This file lives outside `FoxHeisenberg.lean` because it needs `lemma_5_11` (in `Devissage`, which
imports `FoxHeisenberg`) — the import runs the other way, the `TrivialSelfDual.lean` pattern.

## Card bookkeeping for the simple case

For a nontrivial simple module the invariants `H⁰w(A) = A^C` vanish, so the normal form
`H¹w ≅ A` (`lemma_5_13`) forces `#Z¹w = #A²` and `#H²w = 1` — clauses 1 and 2 of `IsSelfDual`.
-/

namespace GQ2.FoxH

open scoped Classical

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- **`H¹w ≅ A` from the normal form**: when every `x₀`-supported tuple is a cocycle and every
cocycle is uniquely `x₀`-supported modulo coboundaries (`lemma_5_13`), the class map `A → H¹w`,
`c ↦ [x₀Supported c]`, is a bijection, so `#H¹w = #A`. -/
theorem card_H1w_of_normalForm (t : Marking C)
    (hx0mem : ∀ c : A, x0Supported c ∈ Z1w (A := A) t)
    (hnf : ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t) :
    Nat.card (H1w (A := A) t) = Nat.card A := by
  have key : ∀ (a b : Z1w (A := A) t),
      h1wMk t a = h1wMk t b ↔ b.val - a.val ∈ B1w (A := A) t := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ B1w (A := A) t ↔ b.val - a.val ∈ B1w (A := A) t
    rw [show -a.val + b.val = b.val - a.val from by abel]
  refine (Nat.card_eq_of_bijective (fun c => h1wMk t ⟨x0Supported c, hx0mem c⟩) ⟨?_, ?_⟩).symm
  · -- injective
    intro c c' hcc
    rw [key] at hcc
    -- `hcc : x₀Supported c' − x₀Supported c ∈ B¹w`
    obtain ⟨cu, -, huniq⟩ := hnf (x0Supported c) (hx0mem c)
    have e1 : c = cu := huniq c (show x0Supported c - x0Supported c ∈ B1w (A := A) t by
      rw [sub_self]; exact (B1w (A := A) t).zero_mem)
    have e2 : c' = cu := huniq c' (show x0Supported c - x0Supported c' ∈ B1w (A := A) t by
      have h := (B1w (A := A) t).neg_mem hcc; rwa [neg_sub] at h)
    exact e1.trans e2.symm
  · -- surjective
    intro h
    induction h using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc, -⟩ := hnf x.val x.2
      exact ⟨c, (key ⟨x0Supported c, hx0mem c⟩ x).mpr hc⟩

/-- **No invariants for a nontrivial simple module**: `H⁰w(A) = A^C = 0`.  `H⁰w` is the `C`-fixed
space (`H0w_eq_fixedPts`, using `hgen`), a `C`-submodule, so `⊥` or `⊤` by simplicity; `⊤` would make
the action trivial, contradicting `hnt`. -/
theorem card_H0w_eq_one_of_nontrivial (t : Marking C) (hgen : t.Generates)
    (hsimple : IsSimpleModTwo C A) (hnt : ∃ (c : C) (a : A), c • a ≠ a) :
    Nat.card (H0w (A := A) t) = 1 := by
  have hfix : (H0w (A := A) t : Set A) = fixedPts C A := H0w_eq_fixedPts t hgen
  have hmem : ∀ w : A, w ∈ H0w (A := A) t → ∀ g : C, g • w = w := by
    intro w hw g
    have : w ∈ fixedPts C A := by rw [← hfix]; exact hw
    exact this g
  have hstable : ∀ (g : C) (w : A), w ∈ H0w (A := A) t → g • w ∈ H0w (A := A) t := by
    intro g w hw; rw [hmem w hw g]; exact hw
  rcases hsimple.2 (H0w (A := A) t) hstable with h | h
  · rw [h]; exact AddSubgroup.card_bot
  · exfalso
    obtain ⟨c, a, hca⟩ := hnt
    exact hca (hmem a (h ▸ AddSubgroup.mem_top a) c)

/-- **Card clauses for a nontrivial simple module** (feeding `IsSelfDual`): `#H²w = 1` and
`#Z¹w = #A²`, from `#H¹w = #A` (`card_H1w_of_normalForm`), `#H⁰w = 1`, and the Euler characteristic
`card_H1w_eq` / `card_Z1w_eq_sq_mul_card_H2w`. -/
theorem card_H2w_and_Z1w_of_nontrivial_simple (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates) (hsimple : IsSimpleModTwo C A) (hnt : ∃ (c : C) (a : A), c • a ≠ a)
    (hx0mem : ∀ c : A, x0Supported c ∈ Z1w (A := A) t)
    (hnf : ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t) :
    Nat.card (H2w (A := A) t) = 1 ∧ Nat.card (Z1w (A := A) t) = Nat.card A ^ 2 := by
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hH0 : Nat.card (H0w (A := A) t) = 1 := card_H0w_eq_one_of_nontrivial t hgen hsimple hnt
  have hH1 : Nat.card (H1w (A := A) t) = Nat.card A := card_H1w_of_normalForm t hx0mem hnf
  have heuler := card_H1w_eq (A := A) t ht hw
  rw [hH1, hH0, mul_one] at heuler
  -- heuler : #A = #A * #H²w
  have hH2 : Nat.card (H2w (A := A) t) = 1 := by
    have : Nat.card A * 1 = Nat.card A * Nat.card (H2w (A := A) t) := by rw [mul_one]; exact heuler
    exact (Nat.eq_of_mul_eq_mul_left hApos this).symm
  refine ⟨hH2, ?_⟩
  rw [card_Z1w_eq_sq_mul_card_H2w, hH2, mul_one]

/-- **No dual invariants for a nontrivial simple module**: `#(A^∨)^C = 1`.  A nonzero `C`-invariant
`λ` has `C`-stable kernel, which is `⊥` by simplicity, so `λ` is injective; but `λ(c·a) = λ(a)`
(invariance) then forces `c·a = a`, a trivial action — contradicting `hnt`. -/
theorem card_fixedPts_elemDual_eq_one_of_nontrivial (hsimple : IsSimpleModTwo C A)
    (hnt : ∃ (c : C) (a : A), c • a ≠ a) :
    Nat.card (fixedPts C (ElemDual A)) = 1 := by
  have hzero : ∀ lam : ElemDual A, (∀ g : C, g • lam = lam) → lam = 0 := by
    intro lam hlam
    have hinv : ∀ (c : C) (a : A), lam (c • a) = lam a := by
      intro c a
      have h2 : (c⁻¹ • lam) a = lam a := by rw [hlam c⁻¹]
      rwa [ElemDual.smul_apply, inv_inv] at h2
    have hkerstable : ∀ (c : C) (a : A), a ∈ (lam : A →+ ZMod 2).ker →
        c • a ∈ (lam : A →+ ZMod 2).ker := by
      intro c a ha
      rw [AddMonoidHom.mem_ker] at ha ⊢
      exact (hinv c a).trans ha
    rcases hsimple.2 (lam : A →+ ZMod 2).ker hkerstable with hbot | htop
    · exfalso
      obtain ⟨c, a, hca⟩ := hnt
      have hinj : Function.Injective (lam : A →+ ZMod 2) :=
        (injective_iff_map_eq_zero (lam : A →+ ZMod 2)).mpr (fun u hu => by
          have hz : u ∈ (lam : A →+ ZMod 2).ker := AddMonoidHom.mem_ker.mpr hu
          rw [hbot, AddSubgroup.mem_bot] at hz; exact hz)
      exact hca (hinj (hinv c a))
    · ext a
      have hmem : a ∈ (lam : A →+ ZMod 2).ker := htop ▸ AddSubgroup.mem_top a
      rw [AddMonoidHom.mem_ker] at hmem
      rw [ElemDual.zero_apply]; exact hmem
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
    ⟨⟨0, fun c => smul_zero c⟩⟩⟩

/-- **Split/ramified dichotomy for a simple module**: either `τ` acts trivially (split, `V^T = V`)
or `V^T = 0` (ramified).  The `τ`-fixed space `V^T` is `C`-stable — `σ` preserves it via the tame
relation `σ⁻¹τσ = τ²` (`τ(σv) = σ(τ²v) = σv`), `x₀,x₁` act trivially (`wild_acts_trivially`), and the
stabilizer is a subgroup containing the generators, hence all of `C` (`hgen`) — so simplicity forces
`V^T = ⊥` or `⊤`. -/
theorem tau_split_or_ramified (t : Marking C) (ht : t.TameRel) (hgen : t.Generates)
    (hsimple : IsSimpleModTwo C A) (hcore : t.Pro2Core) (hV₂ : ∀ a : A, a + a = 0) :
    (∀ v : A, t.τ • v = v) ∨ (∀ v : A, t.τ • v = v → v = 0) := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  let W : AddSubgroup A :=
    { carrier := {v | t.τ • v = v}
      zero_mem' := smul_zero t.τ
      add_mem' := fun {a b} ha hb => by show t.τ • (a + b) = a + b; rw [smul_add, ha, hb]
      neg_mem' := fun {a} ha => by show t.τ • (-a) = -a; rw [smul_neg, ha] }
  have hmemW : ∀ v : A, v ∈ W ↔ t.τ • v = v := fun _ => Iff.rfl
  -- generators preserve `W`
  have hσW : ∀ v, v ∈ W → t.σ • v ∈ W := by
    intro v hv
    rw [hmemW] at hv ⊢
    have htame : t.σ⁻¹ * t.τ * t.σ = t.τ * t.τ := by
      have h := ht; rw [Marking.TameRel, conjP, pow_two] at h; exact h
    have hcomm : t.τ * t.σ = t.σ * (t.τ * t.τ) := by rw [← htame]; group
    have he : (t.τ * t.σ) • v = (t.σ * (t.τ * t.τ)) • v := by rw [hcomm]
    rw [mul_smul, mul_smul, mul_smul, hv, hv] at he
    exact he
  -- the stabilizer subgroup of `W`
  let S : Subgroup C :=
    { carrier := {g | ∀ v, v ∈ W → g • v ∈ W}
      one_mem' := fun v hv => by rw [one_smul]; exact hv
      mul_mem' := fun {a b} ha hb v hv => by rw [mul_smul]; exact ha _ (hb v hv)
      inv_mem' := fun {a} ha v hv => by
        have hφinj : Function.Injective (fun u : W => (⟨a • u.1, ha u.1 u.2⟩ : W)) := by
          intro x y hxy
          exact Subtype.ext (MulAction.injective a (congrArg Subtype.val hxy))
        obtain ⟨⟨u, hu⟩, hux⟩ := (Finite.injective_iff_surjective.mp hφinj) ⟨v, hv⟩
        have huv : a • u = v := congrArg Subtype.val hux
        rw [show a⁻¹ • v = u from by rw [← huv, inv_smul_smul]]; exact hu }
  have hgenS : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤ S := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hσW
    · intro v hv; rw [hmemW] at hv ⊢; rw [hv]; exact hv
    · intro v hv; rw [hmemW] at hv ⊢; rw [hx0]; exact hv
    · intro v hv; rw [hmemW] at hv ⊢; rw [hx1]; exact hv
  rw [hgen] at hgenS
  have hstable : ∀ (g : C) (v : A), v ∈ W → g • v ∈ W := fun g v hv => hgenS (Subgroup.mem_top g) v hv
  rcases hsimple.2 W hstable with hbot | htop
  · right
    intro v hv
    have : v ∈ W := (hmemW v).mpr hv
    rw [hbot, AddSubgroup.mem_bot] at this; exact this
  · left
    intro v
    exact (hmemW v).mp (htop ▸ AddSubgroup.mem_top v)

/-! ## `mixedB` descends to `H¹w` (the degree-one pairing) -/

/-- `mixedB` is invariant under changing the primal argument by a coboundary (against a cocycle
dual): `B(x + d⁰a, y) = B(x, y)` since `B(d⁰a, y) = ⟨a, L(y)⟩ = 0` (`prop_5_8_left`, `y` a cocycle).
Uses `mixedB` bilinearity. -/
theorem mixedB_left_congr (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (x x' : Fin 4 → A) (y : Fin 4 → ElemDual A) (hb : x - x' ∈ B1w (A := A) t)
    (hy : y ∈ Z1w (A := ElemDual A) t) :
    mixedB t x y = mixedB t x' y := by
  obtain ⟨a, ha⟩ := hb
  have hx : x = x' + d0 t a := by rw [ha]; abel
  rw [hx, mixedB_add_left, prop_5_8_left t ht hw a y]
  have hd1 : d1Fun (A := ElemDual A) t y = 0 := AddMonoidHom.mem_ker.mp hy
  simp [hd1]

/-- Dual version: `B(x, y + d⁰λ) = B(x, y)` (`prop_5_8_right`, `x` a cocycle). -/
theorem mixedB_right_congr (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (x : Fin 4 → A) (y y' : Fin 4 → ElemDual A) (hb : y - y' ∈ B1w (A := ElemDual A) t)
    (hx : x ∈ Z1w (A := A) t) :
    mixedB t x y = mixedB t x y' := by
  obtain ⟨lam, hlam⟩ := hb
  have hy : y = y' + d0 t lam := by rw [hlam]; abel
  rw [hy, mixedB_add_right, prop_5_8_right t ht hw x lam]
  have hd1 : d1Fun (A := A) t x = 0 := AddMonoidHom.mem_ker.mp hx
  simp [hd1]

/-- **Clause 3 (degree-one perfect pairing) from a normal form.**  Given that `x₀`-supported
cochains `x0Supported c` are cocycles and hit every `H¹w` class uniquely (the normal form of
`lemma_5_13`, for both `A` and `A∨`), and that the induced pairing `c, λ ↦ B(x0Supported c,
x0Supported λ)` is nondegenerate on both sides, `mixedB` descends to a perfect pairing
`H¹w(A) × H¹w(A∨) → 𝔽₂`.  Descent uses `mixedB_left_congr`/`mixedB_right_congr`; nondegeneracy
transports through the normal-form identification `H¹w ≅ A`. -/
theorem clause3_of_normalForm (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hx0memA : ∀ c : A, x0Supported c ∈ Z1w (A := A) t)
    (hnfA : ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t)
    (hx0memD : ∀ lam : ElemDual A, x0Supported lam ∈ Z1w (A := ElemDual A) t)
    (hnfD : ∀ y ∈ Z1w (A := ElemDual A) t,
        ∃! lam : ElemDual A, y - x0Supported lam ∈ B1w (A := ElemDual A) t)
    (hndL : ∀ c : A, c ≠ 0 → ∃ lam : ElemDual A, mixedB t (x0Supported c) (x0Supported lam) ≠ 0)
    (hndR : ∀ lam : ElemDual A, lam ≠ 0 → ∃ c : A, mixedB t (x0Supported c) (x0Supported lam) ≠ 0) :
    ∃ P : H1w (A := A) t → H1w (A := ElemDual A) t → ZMod 2,
      (∀ (x : Z1w (A := A) t) (y : Z1w (A := ElemDual A) t),
          P (h1wMk t x) (h1wMk t y) = mixedB t x.val y.val) ∧
      (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
      (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0) := by
  have hx0z : x0Supported (0 : A) = 0 := by ext i; fin_cases i <;> simp [x0Supported]
  have hx0zD : x0Supported (0 : ElemDual A) = 0 := by ext i; fin_cases i <;> simp [x0Supported]
  refine ⟨Quotient.lift₂ (fun (a : Z1w (A := A) t) (b : Z1w (A := ElemDual A) t) =>
      mixedB t a.val b.val) (fun a₁ b₁ a₂ b₂ h₁ h₂ => ?_), fun x y => rfl, ?_, ?_⟩
  · -- well-defined: `mixedB` is constant on cosets (`mixedB_left/right_congr`)
    have hbA : a₁.val - a₂.val ∈ B1w (A := A) t := by
      have h := QuotientAddGroup.leftRel_apply.mp h₁
      rw [AddSubgroup.mem_addSubgroupOf] at h
      rw [show a₁.val - a₂.val = -(↑(-a₁ + a₂) : Fin 4 → A) from by push_cast; abel]
      exact (B1w (A := A) t).neg_mem h
    have hbD : b₁.val - b₂.val ∈ B1w (A := ElemDual A) t := by
      have h := QuotientAddGroup.leftRel_apply.mp h₂
      rw [AddSubgroup.mem_addSubgroupOf] at h
      rw [show b₁.val - b₂.val = -(↑(-b₁ + b₂) : Fin 4 → ElemDual A) from by push_cast; abel]
      exact (B1w (A := ElemDual A) t).neg_mem h
    rw [mixedB_left_congr t ht hw a₁.val a₂.val b₁.val hbA b₁.2,
        mixedB_right_congr t ht hw a₂.val b₁.val b₂.val hbD a₂.2]
  · -- left nondegeneracy
    intro h hh
    induction h using QuotientAddGroup.induction_on with
    | H a =>
      obtain ⟨c, hc, _⟩ := hnfA a.val a.2
      have hc0 : c ≠ 0 := by
        intro hce
        rw [hce, hx0z, sub_zero] at hc
        exact hh ((QuotientAddGroup.eq_zero_iff a).mpr (AddSubgroup.mem_addSubgroupOf.mpr hc))
      obtain ⟨lam, hlam⟩ := hndL c hc0
      refine ⟨QuotientAddGroup.mk ⟨x0Supported lam, hx0memD lam⟩, ?_⟩
      show mixedB t a.val (x0Supported lam) ≠ 0
      rwa [mixedB_left_congr t ht hw a.val (x0Supported c) (x0Supported lam) hc (hx0memD lam)]
  · -- right nondegeneracy
    intro h hh
    induction h using QuotientAddGroup.induction_on with
    | H b =>
      obtain ⟨lam, hlam, _⟩ := hnfD b.val b.2
      have hlam0 : lam ≠ 0 := by
        intro hle
        rw [hle, hx0zD, sub_zero] at hlam
        exact hh ((QuotientAddGroup.eq_zero_iff b).mpr (AddSubgroup.mem_addSubgroupOf.mpr hlam))
      obtain ⟨c, hc⟩ := hndR lam hlam0
      refine ⟨QuotientAddGroup.mk ⟨x0Supported c, hx0memA c⟩, ?_⟩
      show mixedB t (x0Supported c) b.val ≠ 0
      rwa [mixedB_right_congr t ht hw (x0Supported c) b.val (x0Supported lam) hlam (hx0memA c)]

/-! ## Split simple case: `Z¹w`/`B¹w` shapes, normal form, `x₀`-support

These are phrased against the split *shapes* (rather than `lemma_5_13_split` directly) so they
apply equally to `A` and its contragredient dual `A∨`: the dual is split with trivial wild action
whenever `A` is, without needing "the dual of a simple module is simple". -/

/-- The split `Z¹w`/`B¹w` shapes from a *trivial wild action* (`hx0`, `hx1`) rather than from
simplicity — the body of `lemma_5_13_split` with `wild_acts_trivially` factored out as hypotheses,
so it is usable on `A∨` (where wild-triviality comes from the contragredient of `A`'s). -/
theorem split_shapes_of_wild (t : Marking C) (ht : t.TameRel)
    (hV₂ : ∀ v : A, v + v = 0) (hx0 : ∀ v : A, t.x₀ • v = v) (hx1 : ∀ v : A, t.x₁ • v = v)
    (htau : ∀ v : A, t.τ • v = v) (hU : ∀ v : A, t.sigma2 • v = v)
    (hVS : ∀ v : A, t.σ • v = v → v = 0) :
    (∀ x : Fin 4 → A, x ∈ Z1w (A := A) t ↔ x 1 = 0 ∧ x 3 = 0) ∧
    (∀ y : Fin 4 → A, y ∈ B1w (A := A) t ↔ ∃ v : A, y = ![t.σ • v - v, 0, 0, 0]) := by
  refine ⟨fun x => ?_, fun y => b1w_split_shape t htau hx0 hx1 y⟩
  rw [Z1w, AddMonoidHom.mem_ker, show (d1 t) x = d1Fun t x from rfl, Prod.ext_iff]
  rw [d1Fun_tame_split t ht htau hV₂ x,
    show (d1Fun t x).2 = x 1 + x 3 + t.σ⁻¹ • x 3 from
      liftMarking_wildValue_u t x hV₂ hx0 hx1 htau hU]
  simp only [Prod.fst_zero, Prod.snd_zero]
  constructor
  · rintro ⟨h1, h2⟩
    have hx1z : x 1 = 0 := by
      have := congrArg (t.σ • ·) h1
      rwa [smul_zero, smul_inv_smul] at this
    refine ⟨hx1z, ?_⟩
    apply hVS
    have h3 : t.σ⁻¹ • x 3 = x 3 := by
      have h2' : x 3 + t.σ⁻¹ • x 3 = 0 := by rw [hx1z] at h2; rwa [zero_add] at h2
      have : t.σ⁻¹ • x 3 = -x 3 := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h2'
      rw [this, neg_eq_of_add_eq_zero_left (hV₂ (x 3))]
    calc t.σ • x 3 = t.σ • (t.σ⁻¹ • x 3) := by rw [h3]
      _ = x 3 := smul_inv_smul _ _
  · rintro ⟨h1, h3⟩
    rw [h1, h3]
    refine ⟨smul_zero _, ?_⟩
    rw [smul_zero]; abel

/-- The `x₀`-supported cochains are cocycles, straight from the split `Z¹w` shape. -/
theorem x0mem_of_Z1wShape (t : Marking C)
    (hZ : ∀ x : Fin 4 → A, x ∈ Z1w (A := A) t ↔ x 1 = 0 ∧ x 3 = 0) :
    ∀ c : A, x0Supported c ∈ Z1w (A := A) t := fun c => by
  rw [hZ]; exact ⟨by simp [x0Supported], by simp [x0Supported]⟩

/-- **Split normal form**: from the `Z¹w`/`B¹w` shapes and surjectivity of `σ − 1` (from `V^S = 0`,
`hVS`), every degree-one class has a unique `x₀`-supported representative. -/
theorem normalForm_of_shapes (t : Marking C)
    (hZ : ∀ x : Fin 4 → A, x ∈ Z1w (A := A) t ↔ x 1 = 0 ∧ x 3 = 0)
    (hB : ∀ y : Fin 4 → A, y ∈ B1w (A := A) t ↔ ∃ v : A, y = ![t.σ • v - v, 0, 0, 0])
    (hVS : ∀ v : A, t.σ • v = v → v = 0) :
    ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t := by
  have hsurj : Function.Surjective (fun v : A => t.σ • v - v) :=
    (Finite.injective_iff_surjective).mp (fun a b hab => by
      have hab' : t.σ • a - a = t.σ • b - b := hab
      refine sub_eq_zero.mp (hVS (a - b) ?_)
      rw [smul_sub, show t.σ • a - t.σ • b = (t.σ • a - a) - (t.σ • b - b) + (a - b) from by abel,
        hab']
      abel)
  intro x hx
  rw [hZ] at hx
  obtain ⟨hx1, hx3⟩ := hx
  refine ⟨x 2, ?_, ?_⟩
  · show x - x0Supported (x 2) ∈ B1w (A := A) t
    rw [hB]
    obtain ⟨v, hv⟩ := hsurj (x 0)
    exact ⟨v, by funext i; fin_cases i <;> simp [x0Supported, Pi.sub_apply, hx1, hx3, hv]⟩
  · intro c hc
    rw [hB] at hc
    obtain ⟨w, hw'⟩ := hc
    have h2 := congrFun hw' 2
    simp only [x0Supported, Pi.sub_apply, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at h2
    exact (sub_eq_zero.mp h2).symm

/-! ## Split simple case: `IsSelfDual` -/

/-- **Proposition 5.15, split simple case.**  A nontrivial simple module on which `τ` acts trivially
(`htau`) and `σ` acts nontrivially (`hσ`) is self-dual.  The `σ`-tameness `hU` and fixed-point
freeness `hVS` come from P-13d; the contragredient dual `A∨` inherits split + trivial-wild action
from `A` (via `ElemDual.smul_apply`), giving both normal forms; the cards close clauses 1–2 and
`clause3_of_normalForm` (with the split pairing `(c,λ) ↦ λ(c)`) closes clause 3. -/
theorem selfDual_of_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hV₂ : ∀ v : A, v + v = 0) (hsimple : IsSimpleModTwo C A) (hcore : t.Pro2Core)
    (htau : ∀ v : A, t.τ • v = v) (hσ : ∃ v : A, t.σ • v ≠ v) :
    IsSelfDual t A := by
  obtain ⟨v₀, hv₀⟩ := hσ
  have hnt : ∃ (c : C) (a : A), c • a ≠ a := ⟨t.σ, v₀, hv₀⟩
  -- `A`-side hypotheses (P-13d) and the split shapes / normal form
  have hU : ∀ v : A, t.sigma2 • v = v := sigma2_smul_trivial t hgen hV₂ hsimple hcore htau
  have hVS : ∀ v : A, t.σ • v = v → v = 0 :=
    fixedPoints_sigma_eq_zero t hgen hV₂ hsimple hcore htau ⟨v₀, hv₀⟩
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  have hsurjA : Function.Surjective (fun v : A => t.σ • v - v) :=
    (Finite.injective_iff_surjective).mp (fun a b hab => by
      have hab' : t.σ • a - a = t.σ • b - b := hab
      refine sub_eq_zero.mp (hVS (a - b) ?_)
      rw [smul_sub, show t.σ • a - t.σ • b = (t.σ • a - a) - (t.σ • b - b) + (a - b) from by abel,
        hab']
      abel)
  obtain ⟨hZA, hBA⟩ := split_shapes_of_wild t ht hV₂ hx0 hx1 htau hU hVS
  have hnfA := normalForm_of_shapes t hZA hBA hVS
  have hx0A := x0mem_of_Z1wShape t hZA
  -- The contragredient dual is split with trivial wild action (transfer of `A`'s triviality)
  have dual_triv : ∀ g : C, (∀ a : A, g • a = a) → ∀ l : ElemDual A, g • l = l := by
    intro g hg l
    ext a
    rw [ElemDual.smul_apply]
    have hgi : g⁻¹ • a = a := by rw [inv_smul_eq_iff]; exact (hg a).symm
    rw [hgi]
  have hV₂D : ∀ l : ElemDual A, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]
    exact CharTwo.add_self_eq_zero (l v)
  have hVSD : ∀ l : ElemDual A, t.σ • l = l → l = 0 := by
    intro l hl
    have hlσ : ∀ x : A, l (t.σ • x) = l x := by
      intro x
      have h := ElemDual.smul_apply t.σ l (t.σ • x)
      rw [inv_smul_smul, hl] at h
      exact h
    ext a
    obtain ⟨b, hb⟩ := hsurjA a
    have hb' : t.σ • b - b = a := hb
    rw [ElemDual.zero_apply, ← hb', map_sub, hlσ b, sub_self]
  obtain ⟨hZD, hBD⟩ := split_shapes_of_wild (A := ElemDual A) t ht hV₂D
    (dual_triv t.x₀ hx0) (dual_triv t.x₁ hx1) (dual_triv t.τ htau) (dual_triv t.sigma2 hU) hVSD
  have hnfD := normalForm_of_shapes (A := ElemDual A) t hZD hBD hVSD
  have hx0D := x0mem_of_Z1wShape (A := ElemDual A) t hZD
  -- Cards (clauses 1–2) and the perfect pairing (clause 3)
  obtain ⟨hcard2, hcardZ⟩ :=
    card_H2w_and_Z1w_of_nontrivial_simple t ht hw hgen hsimple hnt hx0A hnfA
  have hfix1 := card_fixedPts_elemDual_eq_one_of_nontrivial (A := A) hsimple hnt
  refine ⟨by rw [hcard2, hfix1], by rw [hcardZ, hfix1, mul_one],
    clause3_of_normalForm t ht hw hx0A hnfA hx0D hnfD ?_ ?_⟩
  · intro c hc
    obtain ⟨lam, hlam⟩ := elemDual_separates hV₂ hc
    exact ⟨lam, by
      rw [lemma_5_13_pairing_split t ht hw hV₂ hsimple hcore htau hU c lam]; exact hlam⟩
  · intro lam hlam
    obtain ⟨c, hc⟩ := DFunLike.ne_iff.mp hlam
    exact ⟨c, by
      rw [lemma_5_13_pairing_split t ht hw hV₂ hsimple hcore htau hU c lam]; simpa using hc⟩

/-- **Trivial-action case.**  If all four generators act trivially then (by `hgen`) every element of
`C` does, and the module is self-dual by `trivialSelfDual`.  This is the split sub-case where `σ`
also acts trivially. -/
theorem selfDual_of_trivial_action (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0)
    (hσ : ∀ v : A, t.σ • v = v) (htau : ∀ v : A, t.τ • v = v)
    (hx0 : ∀ v : A, t.x₀ • v = v) (hx1 : ∀ v : A, t.x₁ • v = v) :
    IsSelfDual t A := by
  have htriv : ∀ (c : C) (v : A), c • v = v := by
    have hle : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤
        ({ carrier := {g | ∀ v : A, g • v = v}
           one_mem' := fun v => one_smul C v
           mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
           inv_mem' := fun {a} ha v => by rw [inv_smul_eq_iff]; exact (ha v).symm } : Subgroup C) := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact hσ
      · exact htau
      · exact hx0
      · exact hx1
    rw [hgen] at hle
    exact fun c v => hle (Subgroup.mem_top c) v
  exact trivialSelfDual t ht hw htriv hV₂

/-! ## Ramified simple case -/

/-- Elementwise contragredient triviality: if `g` acts trivially on `A` it acts trivially on
`A∨` (`(g•λ)a = λ(g⁻¹•a) = λ(a)`). -/
theorem elemDual_smul_trivial_of (g : C) (hg : ∀ a : A, g • a = a) :
    ∀ l : ElemDual A, g • l = l := by
  intro l
  ext a
  rw [ElemDual.smul_apply]
  have hgi : g⁻¹ • a = a := by rw [inv_smul_eq_iff]; exact (hg a).symm
  rw [hgi]

/-- In the ramified case the `x₀`-supported cochains are cocycles: the tame row (`d1Fun_tame`)
involves only coordinates 0 and 1, the wild row is `S⁻¹x₃`
(`liftMarking_wildValue_u_ramified`), and all three coordinates vanish on `x0Supported c`. -/
theorem x0Supported_mem_Z1w_ramified (t : Marking C) (ht : t.TameRel)
    (hV₂ : ∀ v : A, v + v = 0)
    (hx0 : ∀ v : A, t.x₀ • v = v) (hx1 : ∀ v : A, t.x₁ • v = v)
    (htau : ∀ v : A, t.τ • v = v → v = 0) (hTodd : ∀ v : A, powOmega2 t.τ • v = v) :
    ∀ c : A, x0Supported c ∈ Z1w (A := A) t := by
  intro c
  rw [Z1w, AddMonoidHom.mem_ker, show (d1 t) (x0Supported c) = d1Fun t (x0Supported c) from rfl,
    Prod.ext_iff]
  simp only [Prod.fst_zero, Prod.snd_zero]
  constructor
  · rw [d1Fun_tame t ht (x0Supported c)]
    simp [x0Supported]
  · rw [show (d1Fun t (x0Supported c)).2 = t.σ⁻¹ • (x0Supported c) 3 from
      liftMarking_wildValue_u_ramified t (x0Supported c) hV₂ hx0 hx1 htau hTodd]
    simp [x0Supported]

/-- **Proposition 5.15, ramified simple case.**  A simple module with `V^T = 0` is self-dual.
`hTodd` (τ odd-order) is derived (`tau_powOmega2_smul_trivial`); the dual `A∨` inherits
wild-triviality and `hTodd` (contragredient) and τ-fixed-point-freeness (`(τ⁻¹−1)` surjective);
the pairing `λ((1+U+U⁻¹)c)` (`lemma_5_13_pairing_ramified`) is perfect because the operator
`1+U+U⁻¹` is unipotent, hence bijective (`sigma2_pairing_operator_injective`) — no σ-tameness
`hU` anywhere (it is *not derivable*: `S₃`/`C₅⋊C₄` admissible counterexamples). -/
theorem selfDual_of_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0) (hsimple : IsSimpleModTwo C A)
    (hcore : t.Pro2Core) (htau : ∀ v : A, t.τ • v = v → v = 0) :
    IsSelfDual t A := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  have hTodd : ∀ v : A, powOmega2 t.τ • v = v :=
    tau_powOmega2_smul_trivial t ht hgen hV₂ hsimple hcore
  -- the action is nontrivial: `τ` is fixed-point-free on a nontrivial module
  haveI : Nontrivial A := hsimple.1
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : A)
  have hnt : ∃ (c : C) (a : A), c • a ≠ a := ⟨t.τ, a₀, fun h => ha₀ (htau a₀ h)⟩
  -- `A`-side normal form
  have hx0A := x0Supported_mem_Z1w_ramified t ht hV₂ hx0 hx1 htau hTodd
  have hnfA := lemma_5_13_ramified t ht hw hV₂ hx0 hx1 htau hTodd
  -- the pairing operator `1 + U + U⁻¹` is bijective (unipotent in char 2)
  have hop := sigma2_pairing_operator_injective (V := A) t hV₂
  have hopsurj := Finite.injective_iff_surjective.mp hop
  -- dual-side hypotheses
  have hV₂D : ∀ l : ElemDual A, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]
    exact CharTwo.add_self_eq_zero (l v)
  have hx0D := elemDual_smul_trivial_of (A := A) t.x₀ hx0
  have hx1D := elemDual_smul_trivial_of (A := A) t.x₁ hx1
  have hToddD := elemDual_smul_trivial_of (A := A) (powOmega2 t.τ) hTodd
  have hτsurj : Function.Surjective (fun v : A => t.τ⁻¹ • v - v) :=
    (Finite.injective_iff_surjective).mp (fun a b hab => by
      have hab' : t.τ⁻¹ • a - a = t.τ⁻¹ • b - b := hab
      refine sub_eq_zero.mp (htau (a - b) ?_)
      have hfix : t.τ⁻¹ • (a - b) = a - b := by
        rw [smul_sub, show t.τ⁻¹ • a - t.τ⁻¹ • b
            = (t.τ⁻¹ • a - a) - (t.τ⁻¹ • b - b) + (a - b) from by abel, hab']
        abel
      have := congrArg (t.τ • ·) hfix
      simpa [smul_inv_smul] using this.symm)
  have htauD : ∀ l : ElemDual A, t.τ • l = l → l = 0 := by
    intro l hl
    have hlτ : ∀ x : A, l (t.τ⁻¹ • x) = l x := by
      intro x
      have h := congrArg (fun m : ElemDual A => m x) hl
      rwa [ElemDual.smul_apply] at h
    ext a
    obtain ⟨b, hb⟩ := hτsurj a
    have hb' : t.τ⁻¹ • b - b = a := hb
    rw [ElemDual.zero_apply, ← hb', map_sub, hlτ b, sub_self]
  have hx0D' := x0Supported_mem_Z1w_ramified (A := ElemDual A) t ht hV₂D hx0D hx1D htauD
    hToddD
  have hnfD := lemma_5_13_ramified (V := ElemDual A) t ht hw hV₂D hx0D hx1D htauD hToddD
  -- cards (clauses 1–2) and the perfect pairing (clause 3)
  obtain ⟨hcard2, hcardZ⟩ :=
    card_H2w_and_Z1w_of_nontrivial_simple t ht hw hgen hsimple hnt hx0A hnfA
  have hfix1 := card_fixedPts_elemDual_eq_one_of_nontrivial (A := A) hsimple hnt
  refine ⟨by rw [hcard2, hfix1], by rw [hcardZ, hfix1, mul_one],
    clause3_of_normalForm t ht hw hx0A hnfA hx0D' hnfD ?_ ?_⟩
  · intro c hc
    have hne : c + t.sigma2 • c + t.sigma2⁻¹ • c ≠ 0 := by
      intro h0
      exact hc (hop (show (fun v : A => v + t.sigma2 • v + t.sigma2⁻¹ • v) c
        = (fun v : A => v + t.sigma2 • v + t.sigma2⁻¹ • v) 0 from by
          simp only [smul_zero, add_zero, h0]))
    obtain ⟨lam, hlam⟩ := elemDual_separates hV₂ hne
    refine ⟨lam, ?_⟩
    rw [lemma_5_13_pairing_ramified t ht hw hV₂ hx0 hx1 htau hTodd c lam]
    exact hlam
  · intro lam hlam
    obtain ⟨w, hw'⟩ := DFunLike.ne_iff.mp hlam
    obtain ⟨c, hc⟩ := hopsurj w
    refine ⟨c, ?_⟩
    rw [lemma_5_13_pairing_ramified t ht hw hV₂ hx0 hx1 htau hTodd c lam,
      show c + t.sigma2 • c + t.sigma2⁻¹ • c = w from hc]
    simpa using hw'

/-- **Split case of a simple module (complete).**  When `τ` acts trivially, the simple module is
self-dual — whether `σ` acts nontrivially (`selfDual_of_split`) or trivially
(`selfDual_of_trivial_action`).  This closes the entire `V^T = V` branch of the
`tau_split_or_ramified` dichotomy. -/
theorem selfDual_of_split_case (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates) (hV₂ : ∀ v : A, v + v = 0) (hsimple : IsSimpleModTwo C A)
    (hcore : t.Pro2Core) (htau : ∀ v : A, t.τ • v = v) :
    IsSelfDual t A := by
  by_cases hσ : ∃ v : A, t.σ • v ≠ v
  · exact selfDual_of_split t ht hw hgen hV₂ hsimple hcore htau hσ
  · push_neg at hσ
    obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
    exact selfDual_of_trivial_action t ht hw hgen hV₂ hσ htau hx0 hx1

/-- **The simple case of `prop_5_15`, unconditional**: every finite simple char-2 module at an
admissible-style marking is self-dual.  Dispatches on the `tau_split_or_ramified` dichotomy —
`selfDual_of_split_case` for `V^T = V`, `selfDual_of_ramified` for `V^T = 0`.  This is exactly
the `hsimp` input the dévissage induction (`prop_5_15_of_simple`) consumes. -/
theorem selfDual_of_simple (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates) (hcore : t.Pro2Core) (hV₂ : ∀ v : A, v + v = 0)
    (hsimple : IsSimpleModTwo C A) :
    IsSelfDual t A := by
  rcases tau_split_or_ramified t ht hgen hsimple hcore hV₂ with htau | htau
  · exact selfDual_of_split_case t ht hw hgen hV₂ hsimple hcore htau
  · exact selfDual_of_ramified t ht hw hgen hV₂ hsimple hcore htau

/-- **Prop 5.15 (candidate deformation duality) — PROVED**: the Fox–Heisenberg chain map is a
quasi-isomorphism for every finite elementary module — packaged: the display-(56) numerics hold
and the descended `B`-pairing is perfect.

The composition: the dévissage strong induction `prop_5_15_of_simple`
(`GQ2/DevissageInduction.lean`, via `lemma_5_11` along `0 → W → A → A/W → 0` for a proper
`C`-stable `W`) reduces to the simple case, which `selfDual_of_simple` closes by the
`tau_split_or_ramified` dichotomy — split (`lemma_5_13_split` + the P-13d tame providers) or
ramified (`lemma_5_13_ramified` + `hTodd` derived + the unipotent pairing operator).

Relocated here from `GQ2/FoxHeisenberg.lean` (statement unchanged, same fully qualified name
`GQ2.FoxH.prop_5_15`): the proof needs the dévissage and the simple-case assembly, which import
that file. -/
theorem prop_5_15 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hA₂ : ∀ a : A, a + a = 0) (hcore : t.Pro2Core) :
    IsSelfDual t A :=
  prop_5_15_of_simple t ht hw hgen hcore
    (fun B _ _ _ hB₂ hBsimple => selfDual_of_simple t ht hw hgen hcore hB₂ hBsimple) hA₂

end GQ2.FoxH
