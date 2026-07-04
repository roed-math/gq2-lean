import GQ2.Foundations.Axioms

/-!
# The Hilbert ledger for Lemma 6.16  (ticket P-15e — COMPLETE)

Proof layer for `GQ2.SectionSix.lemma_6_16` (deep-unit Evens norm vanishing, paper eq. (110)),
following the paper's ledger (111)–(114) through axioms **B9** (`evensKahn_dyadic`) and **B11**
(`dyadicNormCriterion`).  The tier structure, the sub-lemma interface, and the B11-consequence
tier are fixed here; **all bodies are now proved (file is sorry-free, ticket P-15e closed
2026-07-04)**.  Every theorem is `#print axioms` ⊆ std-3, except the Tier-4 assembly
`evensNorm_deepUnit_vanish`, which is std-3 ∪ {B9, B11}.

## The ledger (paper, proof of Lemma 6.16)

With `L = k(δ)`, `δ² = d`, `a = u + vδ` a deep unit (`a = 1 + 2b`, `‖b‖ < 1`), and
`n = u² − dv²`:

1. **(112)** `u = 1 + (b + sb)` is a unit (`‖b + sb‖ < 1`), and `n = 1 + 2t + 4m` with
   `t = b + sb`, `m = b·sb` — pure algebra after applying the reflection `s` (which sends
   `δ ↦ −δ` since `s ∉ Stab δ`).
2. **B9 degree 1** rearranged through `kummerClassK_mul` gives `cor α = [n]`.
3. **B9 degree 2** + bilinearity (`map_add`) + `(x,x) = (x,−1)` (`cup_self_eq_neg_one`)
   collapse to **(113)**: `N^{Ev}[a] = (u,−d) + (2du, n)` — equivalently, at the atom level
   used below, `N^{Ev}[a] = (u,−1) + (u,d) + (2u,n) + (d,n)`.
4. `(u,d) = 0` (`cup_unramified_unit` + `cup_comm`: `u` is a unit, `k(δ)/k` unramified) and
   `(d,n) = 0` (`cup_of_normForm`: `n = u² − dv²` **is** the norm form on the nose).
5. **(114)** `n/(2u−1) = 1 + 4m/(1+2t)` has `‖n/(2u−1) − 1‖ ≤ ‖4‖·‖b‖² < ‖4‖`, so
   `sq_of_near_one` (Hensel) gives `[n] = [2u−1]`.
6. Steinberg (`cup_steinberg`: `1 − 2u = 1² − 2u·1²`) gives `(2u, 2u−1) = (2u, −1)`; and
   `(2,−1) = 0` (`cup_two_neg_one`: `−1 = 1² − 2·1²`), so `(2u,−1) = (u,−1)` and the two
   surviving terms cancel by `h2_add_self`.

## O-finish list  (ALL 6 DONE ☑ 2026-07-04 — file is sorry-free; every theorem std-3, and the
Tier-4 assembly is std-3 ∪ {B9 `evensKahn_dyadic`, B11 `dyadicNormCriterion`})

* ☑ `h1_add_self` / `h2_add_self` — 2-torsion of the coefficient quotients (pointwise char-2 at
  `Z1`/`Z2` level + `H1mk`/`H2mk` quotient induction).
* ☑ `kummerClassK_mul`, `kummerClassK_one` — via the two `ℚ̄₂`-level helpers `kcf_root_indep'`
  and `kcf_mul_of_fixed` (off EvensKahn's `two_values_of_fixed`), transported through `H1mk`.
* ☑ `trivialCupPairing_comm` — graded-commutativity in char 2: the two cup cocycles differ by
  `dOne (g ↦ −(a g · b g))` (identity holds over ℤ) `∈ B2`; then `eq_zero_iff` + `h2_add_self`.
* ☑ `norm_galois` — Galois invariance of the spectral norm, via Mathlib
  `NormedAlgebra.norm_eq_spectralNorm ℚ_[2]` + `spectralNorm_eq_of_equiv`.
* ☑ `sq_of_near_one` — the Hensel depth `‖z−1‖ < ‖4‖ ⟹ z ∈ (k^×)²`: hand-rolled quadratic
  Newton `w ↦ w − (w²−z)/(2w)` from `w₀ = 1` inside `↥k`; invariants `‖wₙ−1‖ ≤ ‖2‖`,
  `‖wₙ²−z‖ ≤ ‖2‖²·qⁿ⁺¹` (`q = ‖z−1‖/‖4‖ < 1`) ⟹ `cauchySeq_of_le_geometric` ⟹ limit ⟹ root.
  `NormedField ↥k` restricts `ℚ̄₂`'s (`rfl`), `CompleteSpace ↥k := FiniteDimensional.complete
  ℚ_[2] ↥k`.  Mathlib's `Padic.hensels_lemma` is `ℤ_p`-specific; `ℚ̄₂` itself is NOT complete.
* ☑ `evensNorm_deepUnit_vanish` — the assembled ledger (5-step script above).  Proof: step 1
  `s'•δ = −δ` (`two_values_of_fixed` + `hs`); step 2 apply `s'` to `hA` ⟹ `(u:ℚ̄₂) = 1+b+s'•b`,
  `(n:ℚ̄₂) = (1+2b)(1+2s'•b)`, `‖u‖ = 1`, `‖n/(2u−1)−1‖ = ‖4‖‖b‖² < ‖4‖`; step 3 degree-1 B9 +
  `kummerClassK_mul`/`_inv`/`h1_add_self` ⟹ `cor = [n]`; step 5-prep `[n] = [2u−1]` (Hensel
  `sq_of_near_one` on `n/(2u−1)` + `kummerClassK_mul_self`); step 4 expand degree-2 (`map_add`),
  kill `(2,u)+(u,2)` (comm + `h2_add_self`), `(u,d)` (`cup_unramified_unit`), `(d,n)`
  (`cup_of_normForm`), `(u,u)=(u,−1)` (`cup_self_eq_neg_one`); step 5 `cup_steinberg` + Hensel ⟹
  `(2,−1) = 0` (`cup_two_neg_one`) closes it.  (Uses `set_option maxHeartbeats` — large context.)

The `lemma_6_16` splice additionally transports along the statement's `hLδ` (the Kummer
presentation of `L/k`, P-15e statement amendment — see `docs/section67-extraction.md`).
-/

namespace GQ2

open ContCoh

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## Tier 0: coefficient 2-torsion -/

section TwoTorsion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- `H¹(G, 𝔽₂)` is 2-torsion.  The representative satisfies `f + f = 0` pointwise (char 2), so
the sum is `H1mk` of the zero cocycle. -/
theorem h1_add_self (x : H1 G (ZMod 2)) : x + x = 0 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      simp only [AddMemClass.coe_add, ZeroMemClass.coe_zero]
      funext g; exact key _
    show H1mk G (ZMod 2) z + H1mk G (ZMod 2) z = 0
    rw [← map_add, hz, map_zero]

/-- `H²(G, 𝔽₂)` is 2-torsion.  Same shape as `h1_add_self`, at `Z2`. -/
theorem h2_add_self (x : H2 G (ZMod 2)) : x + x = 0 := by
  have key : ∀ a : ZMod 2, a + a = 0 := by decide
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      simp only [AddMemClass.coe_add, ZeroMemClass.coe_zero]
      funext g; exact key _
    show H2mk G (ZMod 2) z + H2mk G (ZMod 2) z = 0
    rw [← map_add, hz, map_zero]

end TwoTorsion

/-! ## Tier 1 helpers: base-general cocycle algebra over `ℚ̄₂` -/

section KummerCocycleGeneral

open Kummer

/-- Two square roots of the same `ℚ̄₂`-element give the same Kummer cocycle: `α² = β²` forces
`α = ±β`, and `κ` is sign-insensitive (`kummerCocycleFun_neg`).  Base-general analogue of
`Kummer.kummerCocycleFun_root_indep` (no `algebraMap`-image hypothesis on the radicand). -/
lemma kcf_root_indep' {α β : ℚ̄₂} (h : α ^ 2 = β ^ 2) :
    kummerCocycleFun α = kummerCocycleFun β := by
  have h2 : (α - β) * (α + β) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h' | h'
  · rw [sub_eq_zero.1 h']
  · rw [add_eq_zero_iff_eq_neg.1 h', kummerCocycleFun_neg]

/-- Base-general cocycle multiplicativity at a group element `g` fixing both radicands `A`, `B`
(the `two_values` case analysis with abstract fixed squares, via `two_values_of_fixed`).  Here
`γ` is any square root of `A·B`, so `κ_γ = κ_{αβ}` by `kcf_root_indep'`. -/
lemma kcf_mul_of_fixed {A B γ α β : ℚ̄₂}
    (hγ : γ ^ 2 = A * B) (hα : α ^ 2 = A) (hβ : β ^ 2 = B)
    (hα0 : α ≠ 0) (hβ0 : β ≠ 0)
    {g : Kummer.GaloisGroup ℚ_[2]} (hgA : g • A = A) (hgB : g • B = B) :
    kummerCocycleFun γ g = kummerCocycleFun α g + kummerCocycleFun β g := by
  have hγαβ : kummerCocycleFun γ = kummerCocycleFun (α * β) :=
    kcf_root_indep' (by rw [hγ, mul_pow, hα, hβ])
  rw [hγαβ]
  have hmul : g • (α * β) = (g • α) * (g • β) := by
    rw [AlgEquiv.smul_def, AlgEquiv.smul_def, AlgEquiv.smul_def, map_mul]
  have eq1 : ∀ {x : ℚ̄₂}, g • x = -x → x ≠ 0 → kummerCocycleFun x g = 1 :=
    fun hx hx0 => if_neg (fun e => ne_neg_of_ne_zero hx0 (e.symm.trans hx))
  rcases two_values_of_fixed hα hgA with hga | hga <;>
    rcases two_values_of_fixed hβ hgB with hgb | hgb
  · rw [kummerCocycleFun_eq0 hga, kummerCocycleFun_eq0 hgb,
        kummerCocycleFun_eq0 (by rw [hmul, hga, hgb])]; decide
  · rw [kummerCocycleFun_eq0 hga, eq1 hgb hβ0,
        eq1 (by rw [hmul, hga, hgb]; ring) (mul_ne_zero hα0 hβ0)]; decide
  · rw [eq1 hga hα0, kummerCocycleFun_eq0 hgb,
        eq1 (by rw [hmul, hga, hgb]; ring) (mul_ne_zero hα0 hβ0)]; decide
  · rw [eq1 hga hα0, eq1 hgb hβ0,
        kummerCocycleFun_eq0 (by rw [hmul, hga, hgb]; ring)]; decide

end KummerCocycleGeneral

/-! ## Tier 1: Kummer-class algebra over a finite dyadic base -/

section KummerAlgebra

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- Multiplicativity of the base-general Kummer class.  [O: `sqrtCl (ab)` and
`sqrtCl a · sqrtCl b` are square roots of the same nonzero element, so the cocycles agree by
`Kummer.kummerCocycleFun_root_indep`; then `Kummer.kummerCocycleFun_mul`
(`GQ2/Kummer.lean:179`) gives pointwise additivity, and `H1mk` is additive on `Z1`.] -/
theorem kummerClassK_mul (a b : (↥k)ˣ) :
    kummerClassK k (a * b) = kummerClassK k a + kummerClassK k b := by
  have hAB : ((↑(a * b) : ↥k) : ℚ̄₂)
      = ((↑a : ↥k) : ℚ̄₂) * ((↑b : ↥k) : ℚ̄₂) := by
    rw [Units.val_mul, MulMemClass.coe_mul]
  unfold kummerClassK
  rw [← map_add]
  congr 1
  apply Subtype.ext
  funext g
  simp only [AddMemClass.coe_add, Pi.add_apply]
  rw [hAB]
  exact kcf_mul_of_fixed (sqrtCl_sq _) (sqrtCl_sq _) (sqrtCl_sq _)
    (sqrtCl_ne_zero (unitCoe_ne_zero k a)) (sqrtCl_ne_zero (unitCoe_ne_zero k b))
    (fixingSubgroup_smul k g.2 (a : ↥k)) (fixingSubgroup_smul k g.2 (b : ↥k))

/-- The Kummer class of `1` vanishes.  [O: `1` is its own square root; root-independence
makes the cocycle `g ↦ if g • 1 = 1 then 0 else 1 ≡ 0`.] -/
theorem kummerClassK_one : kummerClassK k (1 : (↥k)ˣ) = 0 := by
  have h := kummerClassK_mul k (1 : (↥k)ˣ) 1
  rw [mul_one] at h
  have h2 : kummerClassK k (1 : (↥k)ˣ) + kummerClassK k 1 = kummerClassK k 1 + 0 := by
    rw [add_zero]; exact h.symm
  exact add_left_cancel h2

/-- `[a⁻¹] = [a]` (derived). -/
theorem kummerClassK_inv (a : (↥k)ˣ) : kummerClassK k a⁻¹ = kummerClassK k a := by
  have h := kummerClassK_mul k a a⁻¹
  rw [mul_inv_cancel, kummerClassK_one] at h
  have h2 : kummerClassK k a⁻¹ = -kummerClassK k a := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h.symm
  rw [h2, neg_eq_of_add_eq_zero_left (h1_add_self (kummerClassK k a))]

/-- `[a²] = 0` (derived). -/
theorem kummerClassK_mul_self (a : (↥k)ˣ) : kummerClassK k (a * a) = 0 := by
  rw [kummerClassK_mul]
  exact h1_add_self _

end KummerAlgebra

/-! ## Tier 2: cup-symbol algebra -/

section CupComm

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- Symmetry of the degree-(1,1) cup pairing in char 2.  [O: at representatives,
`cup11Fun a b + cup11Fun b a = δ¹(g ↦ a g · b g)` — expand `dOne`; the pointwise product of
two 1-cocycles is a continuous 1-cochain, so the difference is in `B2`; conclude by
`QuotientAddGroup.eq'` through `H2mk`.] -/
theorem trivialCupPairing_comm (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (x y : H1 G (ZMod 2)) :
    trivialCupPairing 2 G htriv x y = trivialCupPairing 2 G htriv y x := by
  induction x using QuotientAddGroup.induction_on with | _ a =>
  induction y using QuotientAddGroup.induction_on with | _ b =>
  show cup11 (AddMonoidHom.mul) _ (H1mk G (ZMod 2) a) (H1mk G (ZMod 2) b)
      = cup11 (AddMonoidHom.mul) _ (H1mk G (ZMod 2) b) (H1mk G (ZMod 2) a)
  rw [cup11_mk_mk, cup11_mk_mk]
  have hmul : ∀ (g : G) (m n : ZMod 2),
      (AddMonoidHom.mul) (g • m) (g • n) = g • (AddMonoidHom.mul) m n :=
    fun g m n => by rw [htriv, htriv, htriv]
  -- The two cocycles differ by the coboundary of `g ↦ -(a g · b g)` (holds over ℤ).
  have hcob : (cup11Fun (AddMonoidHom.mul : ZMod 2 →+ ZMod 2 →+ ZMod 2) a.1 b.1
      + cup11Fun (AddMonoidHom.mul) b.1 a.1) ∈ B2 G (ZMod 2) := by
    refine AddSubgroup.mem_map.mpr ⟨fun g => -(a.1 g * b.1 g), ?_, ?_⟩
    · exact mem_C1_iff.mpr (((mem_Z1_iff.mp a.2).1.mul (mem_Z1_iff.mp b.2).1).neg)
    · funext p
      obtain ⟨g, h⟩ := p
      have hca := (mem_Z1_iff.mp a.2).2 g h
      have hcb := (mem_Z1_iff.mp b.2).2 g h
      simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, cup11Fun, Pi.add_apply,
        AddMonoidHom.mul_apply, htriv, hca, hcb]
      ring
  have key : H2mk G (ZMod 2) ⟨cup11Fun (AddMonoidHom.mul) a.1 b.1, cup11_mem_Z2 _ hmul a b⟩
      + H2mk G (ZMod 2) ⟨cup11Fun (AddMonoidHom.mul) b.1 a.1, cup11_mem_Z2 _ hmul b a⟩ = 0 := by
    rw [← map_add]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    apply (AddSubgroup.mem_addSubgroupOf).mpr
    simpa using hcob
  have h2t := h2_add_self
    (H2mk G (ZMod 2) ⟨cup11Fun (AddMonoidHom.mul) a.1 b.1, cup11_mem_Z2 _ hmul a b⟩)
  exact (add_left_cancel (key.trans h2t.symm)).symm

end CupComm

section CupLedger

variable (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
  (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)

/-- The norm-form direction of the **B11** criterion, applied: an explicit representation
`b = x² − a y²` kills the symbol. -/
theorem cup_of_normForm (a b : (↥k)ˣ) (x y : ↥k)
    (hb : (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2) :
    trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k b) = 0 :=
  ((dyadicNormCriterion k htriv).1 a b).mpr ⟨x, y, hb⟩

/-- `(a, −a) = 0` — the norm form represents `−a` as `0² − a·1²`. -/
theorem cup_neg_self (a : (↥k)ˣ) :
    trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k (-a)) = 0 :=
  cup_of_normForm k htriv a (-a) 0 1 (by rw [Units.val_neg]; ring)

/-- Steinberg `(a, 1−a) = 0` — the norm form represents `1 − a` as `1² − a·1²`. -/
theorem cup_steinberg (a b : (↥k)ˣ) (hab : (b : ↥k) = 1 - (a : ↥k)) :
    trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k b) = 0 :=
  cup_of_normForm k htriv a b 1 1 (by rw [hab]; ring)

/-- `(2, −1) = 0` — `−1 = 1² − 2·1²` (the paper's `2 = N_{k(i)/k}(1+i)` step, replaced by the
explicit dyadic representation; cf. the B11 docstring). -/
theorem cup_two_neg_one :
    trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k (twoUnit k))
      (kummerClassK k (-1)) = 0 :=
  cup_of_normForm k htriv (twoUnit k) (-1) 1 1 (by
    simp only [Units.val_neg, Units.val_one, twoUnit, Units.val_mk0]
    ring)

/-- `(a, a) = (a, −1)` (derived: `0 = (a, −a) = (a, −1) + (a, a)` + 2-torsion). -/
theorem cup_self_eq_neg_one (a : (↥k)ˣ) :
    trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k a)
      = trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a)
          (kummerClassK k (-1)) := by
  have h0 := cup_neg_self k htriv a
  have hm : kummerClassK k (-a) = kummerClassK k (-1) + kummerClassK k a := by
    rw [← kummerClassK_mul, neg_one_mul]
  rw [hm, map_add] at h0
  rw [← neg_eq_of_add_eq_zero_left h0,
    neg_eq_of_add_eq_zero_left (h2_add_self
      (trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k a)))]

/-- Unramified unit-norm vanishing: if `k(δa)/k` has equal norm value groups then every unit
symbol `(a, u)` dies — the **B11** clause-2 consumer. -/
theorem cup_unramified_unit (a : (↥k)ˣ) (δa : ℚ̄₂)
    (hδa : δa ^ 2 = ((a : ↥k) : ℚ̄₂))
    (hunram : ∀ z : ℚ̄₂, z ≠ 0 → (∃ x y : ↥k, z = x + y * δa) →
      ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : ℚ̄₂)‖)
    (u : (↥k)ˣ) (hu : ‖((u : ↥k) : ℚ̄₂)‖ = 1) :
    trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k u) = 0 := by
  obtain ⟨x, y, hxy⟩ := (dyadicNormCriterion k htriv).2 a δa hδa hunram u hu
  exact cup_of_normForm k htriv a u x y hxy

end CupLedger

/-! ## Tier 3: dyadic arithmetic -/

section Arithmetic

/-- Galois invariance of the spectral norm on `ℚ̄₂`.  [O: `‖· ∘ g‖` is a field norm on `ℚ̄₂`
extending the `ℚ₂`-norm, and the extension norm on an algebraic extension of a complete field
is unique (Mathlib `spectralNorm` uniqueness layer); alternatively via the
`|N_{k(x)/ℚ₂}(x)|^{1/deg}` characterization, which is visibly `g`-invariant.] -/
theorem norm_galois (g : Kummer.GaloisGroup ℚ_[2]) (x : ℚ̄₂) : ‖g • x‖ = ‖x‖ := by
  rw [AlgEquiv.smul_def, NormedAlgebra.norm_eq_spectralNorm ℚ_[2],
    NormedAlgebra.norm_eq_spectralNorm ℚ_[2]]
  exact (spectralNorm_eq_of_equiv g x).symm

/-- **Hensel depth** over a finite dyadic base: anything within `< ‖4‖` of `1` is a square —
the (114) step `U_{2e+2}(k) ⊆ (k^×)²`.  [O: Newton contraction `w ↦ w − (w²−z)/(2w)` starting
at `w₀ = 1`, run inside `↥k`; needs `NormedField ↥k` (subfield of `ℚ̄₂`, `SubfieldClass`
instance) and `CompleteSpace ↥k` (`FiniteDimensional.complete ℚ_[2] ↥k` — finite-dimensional
over a complete field; NB `ℚ̄₂` itself is NOT complete, completeness is intrinsic to `k`).
Estimates: `‖w_n − 1‖ ≤ ‖2‖` throughout, `‖w_{n+1}² − z‖ ≤ (‖w_n² − z‖/‖2‖)²` — strictly
contracting below `‖4‖`.  Mathlib's `Padic.hensels_lemma` is `ℤ_p`-only; do not reach for it.] -/
theorem sq_of_near_one (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (z : ↥k) (hz : ‖((z : ℚ̄₂)) - 1‖ < ‖(4 : ℚ̄₂)‖) :
    ∃ w : ↥k, w ^ 2 = z := by
  haveI : CompleteSpace ↥k := FiniteDimensional.complete ℚ_[2] ↥k
  -- Norm bookkeeping in `↥k` (its norm is the restriction of `ℚ̄₂`'s, definitionally).
  have h2ne : (2 : ↥k) ≠ 0 := two_ne_zero
  have h2pos : (0 : ℝ) < ‖(2 : ↥k)‖ := norm_pos_iff.mpr h2ne
  have h2lt1 : ‖(2 : ↥k)‖ < 1 := by
    have he : ‖(2 : ↥k)‖ = ‖(2 : ℚ_[2])‖ := by
      rw [show (2 : ↥k) = algebraMap ℚ_[2] ↥k 2 from (map_ofNat _ 2).symm]
      exact norm_algebraMap' (𝕜' := ↥k) (2 : ℚ_[2])
    rw [he]; exact Padic.norm_p_lt_one
  have h4 : ‖(4 : ↥k)‖ = ‖(2 : ↥k)‖ ^ 2 := by
    rw [show (4 : ↥k) = 2 * 2 by norm_num, norm_mul, sq]
  have hsq2 : (0 : ℝ) < ‖(2 : ↥k)‖ ^ 2 := by positivity
  have hz' : ‖z - 1‖ < ‖(2 : ↥k)‖ ^ 2 := by
    have hzk : ‖z - 1‖ < ‖(4 : ↥k)‖ := hz
    rwa [h4] at hzk
  set q : ℝ := ‖z - 1‖ / ‖(2 : ↥k)‖ ^ 2 with hq_def
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := by rw [hq_def, div_lt_one hsq2]; exact hz'
  -- The Newton sequence `wₙ₊₁ = wₙ − (wₙ² − z)/(2wₙ)`, `w₀ = 1`.
  set w : ℕ → ↥k :=
    fun n => Nat.rec (1 : ↥k) (fun _ wn => wn - (wn ^ 2 - z) / (2 * wn)) n with hw_def
  have hw0 : w 0 = 1 := rfl
  have hwS : ∀ n, w (n + 1) = w n - (w n ^ 2 - z) / (2 * w n) := fun n => rfl
  -- Invariant: `wₙ` stays within `‖2‖` of `1`, and the error contracts geometrically.
  have inv : ∀ n, ‖w n - 1‖ ≤ ‖(2 : ↥k)‖ ∧ ‖w n ^ 2 - z‖ ≤ ‖(2 : ↥k)‖ ^ 2 * q ^ (n + 1) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [hw0, sub_self, norm_zero]; exact norm_nonneg _
      · rw [hw0, one_pow, pow_one, hq_def, mul_div_cancel₀ _ (ne_of_gt hsq2),
          show (1 : ↥k) - z = -(z - 1) by ring, norm_neg]
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hwn1 : ‖w n‖ = 1 := by
        have hlt : ‖w n - 1‖ < 1 := lt_of_le_of_lt ih1 h2lt1
        rw [show w n = (w n - 1) + 1 by ring,
          IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
            (by rw [norm_one]; exact ne_of_lt hlt),
          norm_one, max_eq_right (le_of_lt hlt)]
      have hwn0 : w n ≠ 0 := by
        intro h; rw [h, norm_zero] at hwn1; exact one_ne_zero hwn1.symm
      have hkey : w (n + 1) ^ 2 - z = (w n ^ 2 - z) ^ 2 / (4 * w n ^ 2) := by
        rw [hwS]; field_simp; ring
      have hen1 : ‖w (n + 1) ^ 2 - z‖ = ‖w n ^ 2 - z‖ ^ 2 / ‖(2 : ↥k)‖ ^ 2 := by
        rw [hkey, norm_div, norm_pow, norm_mul, norm_pow, hwn1, one_pow, mul_one, h4]
      have hbound : ‖w (n + 1) ^ 2 - z‖ ≤ ‖(2 : ↥k)‖ ^ 2 * q ^ (n + 1 + 1) := by
        rw [hen1]
        calc ‖w n ^ 2 - z‖ ^ 2 / ‖(2 : ↥k)‖ ^ 2
            ≤ (‖(2 : ↥k)‖ ^ 2 * q ^ (n + 1)) ^ 2 / ‖(2 : ↥k)‖ ^ 2 := by gcongr
          _ = ‖(2 : ↥k)‖ ^ 2 * q ^ (2 * (n + 1)) := by
              rw [div_eq_iff (ne_of_gt hsq2)]; ring
          _ ≤ ‖(2 : ↥k)‖ ^ 2 * q ^ (n + 1 + 1) := by
              apply mul_le_mul_of_nonneg_left _ (le_of_lt hsq2)
              exact pow_le_pow_of_le_one hq0 hq1.le (by omega)
      refine ⟨?_, hbound⟩
      have hjump : ‖w (n + 1) - w n‖ ≤ ‖(2 : ↥k)‖ := by
        rw [hwS, show w n - (w n ^ 2 - z) / (2 * w n) - w n = -((w n ^ 2 - z) / (2 * w n)) by ring,
          norm_neg, norm_div, norm_mul, hwn1, mul_one, div_le_iff₀ h2pos]
        calc ‖w n ^ 2 - z‖ ≤ ‖(2 : ↥k)‖ ^ 2 * q ^ (n + 1) := ih2
          _ ≤ ‖(2 : ↥k)‖ ^ 2 * 1 := by
              gcongr; exact pow_le_one₀ hq0 hq1.le
          _ = ‖(2 : ↥k)‖ * ‖(2 : ↥k)‖ := by rw [mul_one, sq]
      rw [show w (n + 1) - 1 = (w (n + 1) - w n) + (w n - 1) by ring]
      exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hjump ih1)
  have hnorm1 : ∀ n, ‖w n‖ = 1 := fun n => by
    have hlt : ‖w n - 1‖ < 1 := lt_of_le_of_lt (inv n).1 h2lt1
    rw [show w n = (w n - 1) + 1 by ring,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ne_of_lt hlt),
      norm_one, max_eq_right (le_of_lt hlt)]
  -- Cauchy via a geometric bound on the jumps.
  have hcauchy : CauchySeq w := by
    refine cauchySeq_of_le_geometric q (‖(2 : ↥k)‖ * q) hq1 (fun n => ?_)
    rw [dist_eq_norm, norm_sub_rev, hwS,
      show w n - (w n ^ 2 - z) / (2 * w n) - w n = -((w n ^ 2 - z) / (2 * w n)) by ring,
      norm_neg, norm_div, norm_mul, hnorm1 n, mul_one, div_le_iff₀ h2pos]
    calc ‖w n ^ 2 - z‖ ≤ ‖(2 : ↥k)‖ ^ 2 * q ^ (n + 1) := (inv n).2
      _ = ‖(2 : ↥k)‖ * q * q ^ n * ‖(2 : ↥k)‖ := by rw [pow_succ]; ring
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨L, ?_⟩
  have hLsq : Filter.Tendsto (fun n => w n ^ 2) Filter.atTop (nhds (L ^ 2)) := hL.pow 2
  have hzlim : Filter.Tendsto (fun n => w n ^ 2) Filter.atTop (nhds z) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (inv n).2) ?_
    have hqpow : Filter.Tendsto (fun n => q ^ (n + 1)) Filter.atTop (nhds 0) := by
      have hbase := (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul q
      rw [mul_zero] at hbase
      exact hbase.congr (fun n => by rw [pow_succ, mul_comm])
    simpa using hqpow.const_mul (‖(2 : ↥k)‖ ^ 2)
  exact tendsto_nhds_unique hLsq hzlim

end Arithmetic

/-! ## Tier 4: the assembled ledger -/

set_option maxHeartbeats 2400000 in
/-- **The Hilbert ledger** (paper, proof of Lemma 6.16; eqs. (111)–(114)) in the B9-native
vocabulary: for a deep unit `a = u + vδ = 1 + 2b` (`‖b‖ < 1`) over the unramified quadratic
Kummer datum `(d, δ)`, the index-two Evens norm of its Kummer cocycle vanishes.

Route (O-finish; every ingredient is in this file, B9, or B11):
1. `s • δ = −δ` from `hs` (`(s•δ)² = d` forces `±δ`; `+` would put `s` in the stabilizer).
2. **(112)**: from `hA` and its `s`-image, `(u:ℚ̄₂) = 1 + (b + s•b)` and
   `(n:ℚ̄₂) = (1+2b)(1+2(s•b))` — so `‖u − 1‖ < 1` and, with `norm_galois`,
   `‖n/(2u−1) − 1‖ ≤ ‖4‖·‖b‖² < ‖4‖` (`‖1+2t‖ = 1` by the ultrametric bound).
3. Apply `evensKahn_dyadic`; rearrange degree 1 with `kummerClassK_mul`/`h1_add_self` to
   `corH1 … α … = kummerClassK k nU` (`nU` the unit `n`).
4. Substitute into degree 2; expand with `map_add`/`kummerClassK_mul`; kill `(u,d)` by
   `cup_unramified_unit` + `trivialCupPairing_comm`, `(d,n)` by `cup_of_normForm` (witness
   `⟨u, v, hn⟩`), normalize `(x,x)` by `cup_self_eq_neg_one` — reaching (113) in the form
   `N^{Ev} = (u,−1) + (2u, n)`.
5. `sq_of_near_one` on `n/(2u−1)` + `kummerClassK_mul`/`kummerClassK_mul_self` give
   `[n] = [2u−1]`; `cup_steinberg` (at `a := 2u`, `b := 1−2u`, sign-flipped through
   `cup_neg_self`) turns `(2u, 2u−1)` into `(2u, −1)`; `cup_two_neg_one` reduces
   `(2u,−1) = (u,−1)`; `h2_add_self` cancels the two surviving terms. -/
theorem evensNorm_deepUnit_vanish
    (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (u n d : (↥k)ˣ) (v : ↥k)
    (hn : (n : ↥k) = (u : ↥k) ^ 2 - (d : ↥k) * v ^ 2)
    (δ β : ℚ̄₂)
    (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂))
    (hβ : β ^ 2 = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ)
    (hβ0 : β ≠ 0)
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (s : k.fixingSubgroup)
    (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup) → ZMod 2)
    (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
        ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hα : ∀ g h, α (g * h) = α g + α h)
    (hαc : Continuous α)
    (b : ℚ̄₂) (hb : ‖b‖ < 1)
    (hA : ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ = 1 + 2 * b)
    (hunram : ∀ z : ℚ̄₂, z ≠ 0 → (∃ x y : ↥k, z = x + y * δ) →
      ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : ℚ̄₂)‖) :
    evensNormH2 htriv hUo hidx hs α hα hαc = 0 := by
  set s' : Kummer.GaloisGroup ℚ_[2] := (↑s : Kummer.GaloisGroup ℚ_[2]) with hs'def
  -- Step 1: the reflection `s` sends `δ ↦ −δ` (it is not in the stabilizer of `δ`).
  have hsd : s' • δ = -δ := by
    rcases two_values_of_fixed hδ (fixingSubgroup_smul k s.2 (d : ↥k)) with h | h
    · exact absurd (Subgroup.mem_subgroupOf.mpr (MulAction.mem_stabilizer_iff.mpr h)) hs
    · exact h
  -- `s'` fixes the base field `k`, and numerals.
  have hfu : s' • ((u : ↥k) : ℚ̄₂) = ((u : ↥k) : ℚ̄₂) := fixingSubgroup_smul k s.2 (u : ↥k)
  have hfv : s' • (v : ℚ̄₂) = (v : ℚ̄₂) := fixingSubgroup_smul k s.2 v
  have hf1 : s' • (1 : ℚ̄₂) = 1 := by rw [AlgEquiv.smul_def, map_one]
  have hf2 : s' • (2 : ℚ̄₂) = 2 := by rw [AlgEquiv.smul_def, map_ofNat]
  -- Step 2 (112): the `s`-image of `hA`, and the resulting `u`, `n` identities in `ℚ̄₂`.
  have hArev : ((u : ↥k) : ℚ̄₂) - (v : ℚ̄₂) * δ = 1 + 2 * (s' • b) := by
    have h := congrArg (fun x => s' • x) hA
    simp only [smul_add, smul_mul', hfu, hfv, hsd, hf1, hf2] at h
    linear_combination h
  have hueq : ((u : ↥k) : ℚ̄₂) = 1 + (b + s' • b) := by
    linear_combination (hA + hArev) / 2
  have hu1 : ‖((u : ↥k) : ℚ̄₂)‖ = 1 := by
    have hbb : ‖b + s' • b‖ < 1 := by
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
      rw [norm_galois]; exact max_lt hb hb
    rw [hueq, add_comm 1 (b + s' • b),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact ne_of_lt hbb),
      norm_one, max_eq_right (le_of_lt hbb)]
  have hnc : ((n : ↥k) : ℚ̄₂) = ((u : ↥k) : ℚ̄₂) ^ 2 - ((d : ↥k) : ℚ̄₂) * (v : ℚ̄₂) ^ 2 := by
    rw [hn]; push_cast; ring
  have hneq : ((n : ↥k) : ℚ̄₂) = (1 + 2 * b) * (1 + 2 * (s' • b)) := by
    rw [hnc, ← hδ,
      show ((u : ↥k) : ℚ̄₂) ^ 2 - δ ^ 2 * (v : ℚ̄₂) ^ 2
        = (((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ) * (((u : ↥k) : ℚ̄₂) - (v : ℚ̄₂) * δ) by ring,
      hA, hArev]
  -- The two components of (111) from axiom B9.
  obtain ⟨hdeg1, hdeg2⟩ :=
    evensKahn_dyadic k u n d v hn δ β hδ hβ hβ0 hidx s hs htriv hUo α hαdef hα hαc
  -- Step 3: the degree-1 component forces `cor(α) = [n]`.
  have hcor : corH1 htriv hUo hidx hs α hα hαc = kummerClassK k n := by
    have e2 : kummerClassK k (twoUnit k * d * n * u⁻¹)
        = kummerClassK k (twoUnit k * d) + kummerClassK k n + kummerClassK k u := by
      rw [kummerClassK_mul, kummerClassK_mul, kummerClassK_inv]
    rw [kummerClassK_mul k (twoUnit k) u, e2] at hdeg1
    have hcancel :
        kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d) + kummerClassK k n
        = kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d)
          + corH1 htriv hUo hidx hs α hα hαc := by
      rw [← hdeg1,
        show kummerClassK k (twoUnit k) + kummerClassK k u
            + (kummerClassK k (twoUnit k * d) + kummerClassK k n + kummerClassK k u)
          = kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d) + kummerClassK k n
            + (kummerClassK k u + kummerClassK k u) by abel,
        h1_add_self, add_zero]
    exact (add_left_cancel hcancel).symm
  -- Step 5 prep: `[n] = [2u−1]`, since `n/(2u−1)` is a Hensel square.
  have h2lt1 : ‖(2 : ℚ̄₂)‖ < 1 := by
    rw [show (2 : ℚ̄₂) = algebraMap ℚ_[2] ℚ̄₂ 2 from (map_ofNat _ 2).symm,
      norm_algebraMap' (𝕜' := ℚ̄₂) (2 : ℚ_[2])]
    exact Padic.norm_p_lt_one
  have h2u : ‖2 * ((u : ↥k) : ℚ̄₂)‖ < 1 := by rw [norm_mul, hu1, mul_one]; exact h2lt1
  have h2unorm : ‖2 * ((u : ↥k) : ℚ̄₂) - 1‖ = 1 := by
    rw [show 2 * ((u : ↥k) : ℚ̄₂) - 1 = -(1 + -(2 * ((u : ↥k) : ℚ̄₂))) by ring, norm_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [norm_one, norm_neg]; exact (ne_of_lt h2u).symm),
      norm_one, norm_neg, max_eq_left (le_of_lt h2u)]
  have hpne : (2 * (u : ↥k) - 1 : ↥k) ≠ 0 := by
    intro h
    have hz0 : ‖2 * ((u : ↥k) : ℚ̄₂) - 1‖ = 0 := by
      rw [show 2 * ((u : ↥k) : ℚ̄₂) - 1 = ((2 * (u : ↥k) - 1 : ↥k) : ℚ̄₂) by norm_cast, h]
      simp
    rw [h2unorm] at hz0; exact one_ne_zero hz0
  set p : (↥k)ˣ := Units.mk0 (2 * (u : ↥k) - 1) hpne with hpdef
  have hpv : ((p : ↥k) : ℚ̄₂) = 2 * ((u : ↥k) : ℚ̄₂) - 1 := by
    rw [hpdef, Units.val_mk0]; norm_cast
  have hpne' : (2 * ((u : ↥k) : ℚ̄₂) - 1) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [h2unorm]; exact one_ne_zero)
  have hnum : ((n : ↥k) : ℚ̄₂) - (2 * ((u : ↥k) : ℚ̄₂) - 1) = 4 * b * (s' • b) := by
    rw [hneq, hueq]; ring
  have hzbound : ‖(((n : ↥k) * (p : ↥k)⁻¹ : ↥k) : ℚ̄₂) - 1‖ < ‖(4 : ℚ̄₂)‖ := by
    rw [show (((n : ↥k) * (p : ↥k)⁻¹ : ↥k) : ℚ̄₂)
        = ((n : ↥k) : ℚ̄₂) * ((p : ↥k) : ℚ̄₂)⁻¹ by push_cast; ring, hpv,
      show ((n : ↥k) : ℚ̄₂) * (2 * ((u : ↥k) : ℚ̄₂) - 1)⁻¹ - 1
        = (((n : ↥k) : ℚ̄₂) - (2 * ((u : ↥k) : ℚ̄₂) - 1)) * (2 * ((u : ↥k) : ℚ̄₂) - 1)⁻¹ by
          field_simp,
      hnum, norm_mul, norm_inv, h2unorm, inv_one, mul_one, norm_mul, norm_mul, norm_galois]
    have h4pos : (0 : ℝ) < ‖(4 : ℚ̄₂)‖ := by rw [norm_pos_iff]; norm_num
    have hbb : ‖b‖ * ‖b‖ < 1 := by nlinarith [norm_nonneg b, hb]
    calc ‖(4 : ℚ̄₂)‖ * ‖b‖ * ‖b‖ = ‖(4 : ℚ̄₂)‖ * (‖b‖ * ‖b‖) := by ring
      _ < ‖(4 : ℚ̄₂)‖ * 1 := mul_lt_mul_of_pos_left hbb h4pos
      _ = ‖(4 : ℚ̄₂)‖ := mul_one _
  obtain ⟨w, hw⟩ := sq_of_near_one k ((n : ↥k) * (p : ↥k)⁻¹) hzbound
  have hwne : w ≠ 0 := by
    intro h
    have : ((n : ↥k) * (p : ↥k)⁻¹) ≠ 0 := mul_ne_zero (Units.ne_zero n) (inv_ne_zero (Units.ne_zero p))
    apply this; rw [← hw, h]; ring
  set wU : (↥k)ˣ := Units.mk0 w hwne with hwUdef
  have hnp : n = p * (wU * wU) := by
    apply Units.ext
    have hwv : (wU : ↥k) = w := by rw [hwUdef, Units.val_mk0]
    rw [Units.val_mul, Units.val_mul, hwv, ← pow_two, hw,
      mul_comm ((n : ↥k)) ((p : ↥k))⁻¹, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero p), one_mul]
  have hn2u1 : kummerClassK k n = kummerClassK k p := by
    rw [hnp, kummerClassK_mul, kummerClassK_mul_self, add_zero]
  -- Steps 4–5: the degree-2 cup algebra collapses `N^{Ev}` to `0`.
  set C := trivialCupPairing 2 k.fixingSubgroup htriv with hCdef
  have hv_du : C (kummerClassK k d) (kummerClassK k u) = 0 :=
    cup_unramified_unit k htriv d δ hδ hunram u hu1
  have hv_dn : C (kummerClassK k d) (kummerClassK k n) = 0 :=
    cup_of_normForm k htriv d n (u : ↥k) v hn
  have hv_2m : C (kummerClassK k (twoUnit k)) (kummerClassK k (-1)) = 0 :=
    cup_two_neg_one k htriv
  have h2u : kummerClassK k (twoUnit k * u) = kummerClassK k (twoUnit k) + kummerClassK k u :=
    kummerClassK_mul k (twoUnit k) u
  have h2d : kummerClassK k (twoUnit k * d) = kummerClassK k (twoUnit k) + kummerClassK k d :=
    kummerClassK_mul k (twoUnit k) d
  have h2dnu : kummerClassK k (twoUnit k * d * n * u⁻¹)
      = kummerClassK k (twoUnit k) + kummerClassK k d + kummerClassK k n + kummerClassK k u := by
    rw [kummerClassK_mul, kummerClassK_mul, kummerClassK_mul, kummerClassK_inv]
  have h2p2d : kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d) = kummerClassK k d := by
    rw [h2d, ← add_assoc, h1_add_self, zero_add]
  -- Step 5: `[2]∪[n] + [u]∪[n] = [u]∪[−1]` (Hensel `[n]=[2u−1]` + Steinberg).
  have hCn : C (kummerClassK k (twoUnit k)) (kummerClassK k n)
      + C (kummerClassK k u) (kummerClassK k n) = C (kummerClassK k u) (kummerClassK k (-1)) := by
    rw [← AddMonoidHom.add_apply, ← map_add, ← h2u, hn2u1]
    have hpsplit : kummerClassK k p = kummerClassK k (-1) + kummerClassK k (-p) := by
      have hpp : ((-1) * (-p) : (↥k)ˣ) = p := by rw [neg_mul_neg, one_mul]
      nth_rewrite 1 [← hpp]
      rw [kummerClassK_mul]
    have hstein : C (kummerClassK k (twoUnit k * u)) (kummerClassK k (-p)) = 0 := by
      refine cup_steinberg k htriv (twoUnit k * u) (-p) ?_
      rw [Units.val_neg, hpdef, Units.val_mk0, Units.val_mul, twoUnit, Units.val_mk0]; ring
    rw [hpsplit, map_add, hstein, add_zero, h2u, map_add, AddMonoidHom.add_apply, hv_2m, zero_add]
  rw [hcor, h2p2d, hv_dn, add_zero, h2u, h2dnu, h2d] at hdeg2
  simp only [map_add, AddMonoidHom.add_apply] at hdeg2
  rw [trivialCupPairing_comm htriv (kummerClassK k u) (kummerClassK k d), hv_du,
    cup_self_eq_neg_one k htriv u,
    trivialCupPairing_comm htriv (kummerClassK k (twoUnit k)) (kummerClassK k u),
    ← hCdef, hCn, add_zero,
    show (C (kummerClassK k (twoUnit k))) (kummerClassK k (twoUnit k))
        + (C (kummerClassK k u)) (kummerClassK k (twoUnit k))
        + (C (kummerClassK k (twoUnit k))) (kummerClassK k d)
        + (C (kummerClassK k u)) (kummerClassK k (-1))
        + ((C (kummerClassK k u)) (kummerClassK k (twoUnit k))
          + (C (kummerClassK k u)) (kummerClassK k (-1)))
      = (C (kummerClassK k (twoUnit k))) (kummerClassK k (twoUnit k))
          + (C (kummerClassK k (twoUnit k))) (kummerClassK k d)
        + ((C (kummerClassK k u)) (kummerClassK k (twoUnit k))
          + (C (kummerClassK k u)) (kummerClassK k (twoUnit k)))
        + ((C (kummerClassK k u)) (kummerClassK k (-1))
          + (C (kummerClassK k u)) (kummerClassK k (-1))) from by abel,
    h2_add_self, h2_add_self, add_zero, add_zero] at hdeg2
  have hfin : ((C (kummerClassK k (twoUnit k))) (kummerClassK k (twoUnit k))
        + (C (kummerClassK k (twoUnit k))) (kummerClassK k d))
      + evensNormH2 htriv hUo hidx hs α hα hαc
      = ((C (kummerClassK k (twoUnit k))) (kummerClassK k (twoUnit k))
        + (C (kummerClassK k (twoUnit k))) (kummerClassK k d)) + 0 := by
    rw [add_zero]; exact hdeg2.symm
  exact add_left_cancel hfin

end GQ2
