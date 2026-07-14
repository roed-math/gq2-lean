import GQ2.AdmissibleLimit
import GQ2.AppendixB
import GQ2.BoundaryFrame
import GQ2.FrameEnrichment
import GQ2.HalfTorsorGammaA
import GQ2.Prop23
import GQ2.RadicalEdge.Data
import GQ2.RadicalEdge.Local
import GQ2.SectionSeven

/-!
# §8: the finite Fourier and Gauss engines (Lemmas 8.4, 8.5)

The sign calculus over `𝔽₂` and the two multiplied-out integer identities it powers:
**Lemma 8.4** (Fourier inversion, display (125)) and **Lemma 8.5** (the constrained
quadratic Gauss transform, display (126)).  Split out of `GQ2.SectionEight` (wave 38a).
-/

open scoped Pointwise

namespace GQ2

namespace SectionEight

open QuadraticFp2

/-! ## The sign calculus over `𝔽₂`

`(−1)^{(·).val} : ZMod 2 → ℤ` is the additive character; the two orthogonality relations
(over the group and over its dual) are the single lemma `sum_sign_eq_zero` below. -/

/-- The sign `(−1)^s` of `s : 𝔽₂`, as an integer. -/
def sign (s : ZMod 2) : ℤ := (-1) ^ s.val

@[simp] lemma sign_zero : sign 0 = 1 := rfl

@[simp] lemma sign_one : sign 1 = -1 := rfl

lemma sign_add (s t : ZMod 2) : sign (s + t) = sign s * sign t := by
  fin_cases s <;> fin_cases t <;> decide

/-- `1 + (−1)^u = 2·[u = 0]`. -/
lemma one_add_sign (u : ZMod 2) : 1 + sign u = if u = 0 then 2 else 0 := by
  fin_cases u <;> decide

/-- **Character orthogonality**: a nonzero additive functional to `𝔽₂` on a finite abelian
group has sign-sum zero.  (Both orthogonality relations of §8 — over the group for (126),
over the dual for (125) — are instances.) -/
lemma sum_sign_eq_zero {A : Type*} [AddCommGroup A] [Finite A] (ψ : A → ZMod 2)
    (hadd : ∀ a b : A, ψ (a + b) = ψ a + ψ b) (hne : ¬∀ a, ψ a = 0) :
    ∑ᶠ a : A, sign (ψ a) = 0 := by
  haveI : Fintype A := Fintype.ofFinite A
  simp only [not_forall] at hne
  obtain ⟨a₀, ha₀⟩ := hne
  have ha₀' : ψ a₀ = 1 :=
    ((show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (ψ a₀)).resolve_left ha₀
  rw [finsum_eq_sum_of_fintype]
  -- pair `a ↦ a + a₀`: signs cancel
  have hpair : ∀ a : A, sign (ψ (a + a₀)) = -sign (ψ a) := fun a => by
    rw [hadd, sign_add, ha₀', sign_one, mul_neg_one]
  have hS : ∑ a : A, sign (ψ a) = -∑ a : A, sign (ψ a) :=
    calc ∑ a : A, sign (ψ a)
        = ∑ a : A, sign (ψ (a + a₀)) :=
          (Fintype.sum_equiv (Equiv.addRight a₀)
            (fun a => sign (ψ (a + a₀))) (fun a => sign (ψ a)) (fun a => by simp)).symm
      _ = ∑ a : A, -sign (ψ a) := Finset.sum_congr rfl fun a _ => hpair a
      _ = -∑ a : A, sign (ψ a) := by rw [Finset.sum_neg_distrib]
  omega

/-- The sign is the `±1`-indicator: `sign u = 2·[u = 0] − 1`. -/
lemma sign_eq_indicator (u : ZMod 2) : sign u = (if u = 0 then 2 else 0) - 1 := by
  fin_cases u <;> decide

/-- The `𝔽₂`-linear dual of a finite module is finite (inject into the function space). -/
private instance finite_dual {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] :
    Finite (Module.Dual (ZMod 2) W) :=
  Finite.of_injective (fun f => (f : W → ZMod 2)) DFunLike.coe_injective

open scoped Classical in
/-- Orthogonality over the dual, summed form: `Σ_{φ ∈ W^∨} (−1)^{φ w} = |W^∨|·[w = 0]`. -/
lemma sum_dual_sign {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W] (w : W) :
    ∑ᶠ φ : Module.Dual (ZMod 2) W, sign (φ w)
      = if w = 0 then (Nat.card (Module.Dual (ZMod 2) W) : ℤ) else 0 := by
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  by_cases hw : w = 0
  · subst hw
    simp only [map_zero, sign_zero, if_pos]
    rw [finsum_eq_sum_of_fintype, Finset.sum_const, Nat.card_eq_fintype_card]
    simp
  · rw [if_neg hw]
    exact sum_sign_eq_zero (fun φ : Module.Dual (ZMod 2) W => φ w) (fun φ φ' => rfl)
      (mt (Module.forall_dual_apply_eq_zero_iff (ZMod 2) w).mp hw)

/-! ## Lemma 8.4: Fourier inversion  (display (125)) -/

/-- **Lemma 8.4 (Fourier inversion, eq. (125))**, multiplied-out integer form: for a finite
`𝔽₂`-obstruction space `W`, an obstruction assignment `o : X → W` on a finite index set, and
`m_φ = #{x ∣ φ(o(x)) = 0}`,
`|W^∨| · #{x ∣ o(x) = 0} = Σ_{φ ∈ W^∨} (2 m_φ − |X|)`.
(Paper form: divide by `|D|`, `D = W^∨`.)  **Proved** — the `𝔽₂`-character engine of the
final `R`-lifting stage (136). -/
theorem lemma_8_4 {X W : Type*} [Finite X] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (o : X → W) :
    (Nat.card (Module.Dual (ZMod 2) W) : ℤ) * Nat.card {x : X // o x = 0}
      = ∑ᶠ φ : Module.Dual (ZMod 2) W,
          (2 * (Nat.card {x : X // φ (o x) = 0} : ℤ) - Nat.card X) := by
  classical
  haveI : Fintype X := Fintype.ofFinite X
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- rewrite each summand as a sign-sum over `X`
  have hsummand : ∀ φ : Module.Dual (ZMod 2) W,
      2 * (Nat.card {x : X // φ (o x) = 0} : ℤ) - Nat.card X
        = ∑ x : X, sign (φ (o x)) := by
    intro φ
    have hcard : (Nat.card {x : X // φ (o x) = 0} : ℤ)
        = ∑ x : X, if φ (o x) = 0 then (1 : ℤ) else 0 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.sum_filter]
      simp
    have hX : (Nat.card X : ℤ) = ∑ _x : X, (1 : ℤ) := by
      simp [Nat.card_eq_fintype_card]
    rw [hcard, hX, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [sign_eq_indicator]
    by_cases h : φ (o x) = 0 <;> simp [h]
  rw [Finset.sum_congr rfl fun φ _ => hsummand φ, Finset.sum_comm]
  -- inner sum over the dual is the `[o x = 0]`-indicator
  have hinner : ∀ x : X, ∑ φ : Module.Dual (ZMod 2) W, sign (φ (o x))
      = if o x = 0 then (Nat.card (Module.Dual (ZMod 2) W) : ℤ) else 0 := by
    intro x
    rw [← finsum_eq_sum_of_fintype]
    exact sum_dual_sign (o x)
  rw [Finset.sum_congr rfl fun x _ => hinner x, ← Finset.sum_filter, Finset.sum_const,
    Nat.card_eq_fintype_card (α := {x : X // o x = 0}), Fintype.card_subtype]
  simp [mul_comm]

/-! ## Lemma 8.5: the constrained quadratic Gauss transform  (display (126)) -/

/-- The Gauss sum `G(Q) = Σ_{x ∈ W} (−1)^{Q(x)}` of an `𝔽₂`-valued form. -/
noncomputable def gaussSum {W : Type*} [Finite W] (Q : W → ZMod 2) : ℤ :=
  ∑ᶠ x : W, sign (Q x)

/-- In an `𝔽₂`-module, every element is self-inverse. -/
lemma add_self_fp2 {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (m : M) : m + m = 0 := by
  rw [← two_smul (ZMod 2) m, show (2 : ZMod 2) = 0 by decide, zero_smul]

/-- **Lemma 8.5 (constrained quadratic Gauss transform, eq. (126))**, multiplied-out form:
for finite `𝔽₂`-spaces `W, E`, a surjective linear `L : W ↠ E`, a form `Q : W → 𝔽₂` with
polar form `B_Q`, and **data** `a : E^∨ → W` with the paper's defining property
`B_Q(a_χ, x) = χ(L x)` (the paper produces `a_χ` from nonsingularity of `Q`; the identity
needs only the property), the constrained count `N(κ,ε) = #{x ∣ Lx = κ, Q(x) = ε}`
satisfies `2|E^∨| · N(κ,ε) = |W| + G(Q) · Σ_{χ ∈ E^∨} (−1)^{χ(κ)+ε+Q(a_χ)}`.
(`|E^∨| = |E|` for finite `𝔽₂`-spaces, giving the paper's `1/(2|E|)`-form.)
**Proved** — the affine-fibre engine of the (140)-clause of Prop 8.9. -/
theorem lemma_8_5 {W E : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (L : W →ₗ[ZMod 2] E) (hL : Function.Surjective L)
    (Q : W → ZMod 2)
    (a : Module.Dual (ZMod 2) E → W)
    (ha : ∀ (χ : Module.Dual (ZMod 2) E) (x : W), polar Q (a χ) x = χ (L x))
    (κ : E) (ε : ZMod 2) :
    2 * (Nat.card (Module.Dual (ZMod 2) E) : ℤ) * Nat.card {x : W // L x = κ ∧ Q x = ε}
      = Nat.card W + gaussSum Q *
          ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ κ + ε + Q (a χ)) := by
  classical
  haveI : Fintype W := Fintype.ofFinite W
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype (Module.Dual (ZMod 2) E) := Fintype.ofFinite _
  -- The master double sum, computed two ways.
  set T : ℤ := ∑ x : W, ∑ χ : Module.Dual (ZMod 2) E,
    sign (χ (L x + κ)) * (1 + sign (Q x + ε)) with hT
  -- Way 1: inner dual-sum is the `[L x = κ]`-indicator; the master sum is the count.
  have hway1 : T = 2 * (Nat.card (Module.Dual (ZMod 2) E) : ℤ)
      * Nat.card {x : W // L x = κ ∧ Q x = ε} := by
    have hx : ∀ x : W, ∑ χ : Module.Dual (ZMod 2) E, sign (χ (L x + κ)) * (1 + sign (Q x + ε))
        = if L x = κ ∧ Q x = ε
            then 2 * (Nat.card (Module.Dual (ZMod 2) E) : ℤ) else 0 := by
      intro x
      rw [← Finset.sum_mul, ← finsum_eq_sum_of_fintype, sum_dual_sign (L x + κ)]
      have hLiff : L x + κ = 0 ↔ L x = κ :=
        ⟨fun h => by simpa [add_assoc, add_self_fp2] using congrArg (· + κ) h,
         fun h => by rw [h]; exact add_self_fp2 _⟩
      have hQiff : Q x + ε = 0 ↔ Q x = ε :=
        (show ∀ u v : ZMod 2, (u + v = 0 ↔ u = v) from by decide) (Q x) ε
      rw [one_add_sign]
      simp only [hLiff, hQiff]
      by_cases h1 : L x = κ <;> by_cases h2 : Q x = ε <;> simp [h1, h2, mul_comm]
    rw [hT, Finset.sum_congr rfl fun x _ => hx x, ← Finset.sum_filter, Finset.sum_const,
      Nat.card_eq_fintype_card (α := {x : W // L x = κ ∧ Q x = ε}), Fintype.card_subtype]
    ring
  -- Way 2: expand the product; the two double sums are `|W|` and the Gauss term.
  have hway2 : T = (Nat.card W : ℤ) + gaussSum Q *
      ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ κ + ε + Q (a χ)) := by
    have hsplit : T = (∑ χ : Module.Dual (ZMod 2) E, ∑ x : W, sign (χ (L x + κ)))
        + ∑ χ : Module.Dual (ZMod 2) E, ∑ x : W, sign (χ (L x + κ)) * sign (Q x + ε) := by
      rw [hT, Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    -- first double sum: only `χ = 0` survives, contributing `|W|`
    have hfirst : (∑ χ : Module.Dual (ZMod 2) E, ∑ x : W, sign (χ (L x + κ)))
        = (Nat.card W : ℤ) := by
      rw [Finset.sum_eq_single (0 : Module.Dual (ZMod 2) E)]
      · simp [sign_zero, Nat.card_eq_fintype_card, Finset.sum_const]
      · intro χ _ hχ
        have hcomp : ¬∀ x : W, χ (L x) = 0 := by
          intro hall
          apply hχ
          ext e
          obtain ⟨x, rfl⟩ := hL e
          exact hall x
        have hzero : ∑ᶠ x : W, sign (χ (L x)) = 0 :=
          sum_sign_eq_zero (fun x => χ (L x)) (fun x y => by rw [map_add, map_add]) hcomp
        calc ∑ x : W, sign (χ (L x + κ))
            = ∑ x : W, sign (χ κ) * sign (χ (L x)) :=
              Finset.sum_congr rfl fun x _ => by rw [map_add, sign_add, mul_comm]
          _ = sign (χ κ) * ∑ x : W, sign (χ (L x)) := by rw [Finset.mul_sum]
          _ = 0 := by rw [← finsum_eq_sum_of_fintype, hzero, mul_zero]
      · exact fun h => absurd (Finset.mem_univ _) h
    -- second double sum: complete the square, translate, factor the Gauss sum
    have hsecond : (∑ χ : Module.Dual (ZMod 2) E, ∑ x : W,
          sign (χ (L x + κ)) * sign (Q x + ε))
        = gaussSum Q * ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ κ + ε + Q (a χ)) := by
      rw [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      -- per-`χ`: `Σ_x sign(χ(Lx+κ))·sign(Qx+ε) = G(Q) · sign(χκ + ε + Q(a χ))`
      have hcs : ∀ x : W, Q x + χ (L x) = Q (a χ + x) + Q (a χ) := by
        intro x
        rw [← ha χ x]
        show Q x + polar Q (a χ) x = Q (a χ + x) + Q (a χ)
        rw [polar]
        have hz : ∀ u v w : ZMod 2, u + (v + w + u) = v + w := by decide
        exact hz (Q x) (Q (a χ + x)) (Q (a χ))
      have hsigns : ∀ x : W, sign (Q x) * sign (χ (L x))
          = sign (Q (a χ + x)) * sign (Q (a χ)) := by
        intro x
        rw [← sign_add, ← sign_add, hcs x]
      have hterm : ∀ x : W, sign (χ (L x + κ)) * sign (Q x + ε)
          = sign (χ κ + ε + Q (a χ)) * sign (Q (a χ + x)) := by
        intro x
        have h1 : sign (χ (L x + κ)) * sign (Q x + ε)
            = (sign (Q x) * sign (χ (L x))) * (sign (χ κ) * sign ε) := by
          rw [map_add, sign_add, sign_add]
          ring
        have h2 : sign (χ κ + ε + Q (a χ)) * sign (Q (a χ + x))
            = (sign (Q (a χ + x)) * sign (Q (a χ))) * (sign (χ κ) * sign ε) := by
          rw [sign_add, sign_add]
          ring
        rw [h1, h2, hsigns x]
      calc ∑ x : W, sign (χ (L x + κ)) * sign (Q x + ε)
          = ∑ x : W, sign (χ κ + ε + Q (a χ)) * sign (Q (a χ + x)) :=
            Finset.sum_congr rfl fun x _ => hterm x
        _ = sign (χ κ + ε + Q (a χ)) * ∑ x : W, sign (Q (a χ + x)) := by
            rw [← Finset.mul_sum]
        _ = sign (χ κ + ε + Q (a χ)) * gaussSum Q := by
            congr 1
            rw [gaussSum, finsum_eq_sum_of_fintype]
            exact Fintype.sum_equiv (Equiv.addLeft (a χ))
              (fun x => sign (Q (a χ + x))) (fun y => sign (Q y)) (fun x => rfl)
        _ = gaussSum Q * sign (χ κ + ε + Q (a χ)) := mul_comm _ _
    rw [hsplit, hfirst, hsecond]
  rw [← hway1, hway2]

end SectionEight

end GQ2
