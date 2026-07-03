import GQ2.BoundaryFrame
import GQ2.SectionSeven
import GQ2.AppendixB
import GQ2.AdmissibleLimit
import GQ2.Prop23

/-!
# §8: central covers, affine fibres, and Fourier inversion — statements  (ticket P-16)

Statement-first extraction of the paper's §8 (pages 38–44): the **half-torsor count**
(Lemma 8.6) and the **closed exact-image recursion** (Prop 8.9, displays (136)–(142)),
together with the finite Fourier/Gauss engines they run on (Lemmas 8.4/8.5 — **proved
here**) and the central-cover bookkeeping (Lemma 8.2/8.3).  Proofs of the sorried
statements are the O-half of P-16; the §9 induction (P-17) consumes only the boxed
system of Prop 8.9 plus Lemma 8.3.

Setting (§8 opening): the simple-head block of §7 (`GQ2.SectionSeven.MinimalBlock`) on a
boundary-framed marked target `𝒴 = (Y, L_Y, π_Y, θ_Y)` (`GQ2.MarkedTarget`), with
`R = Φ(K)`, `M = K/R`, `0 → T → M → V → 0`, `B = Y/R`, `C = Y/K`, and `T = T₀ = (K∩S)R/R`
(Lemma 7.1).  All counts are the exact-image counts `e^β_Γ(·)` of eq. (29)
(`GQ2.exactImageCount`) for the two sources `Γ ∈ {Γ_A, G_ℚ₂}` through a `BoundaryMaps`
witness (P-11).

## Encoding decisions (design note; deviations flagged for P-20)

1. **Lemmas 8.4/8.5 are proved, in multiplied-out integer form.**  (125) is stated as
   `|D| · #{o = 0} = Σ_λ (2 m_λ − |X|)` over `ℤ` (no division), with `D` the `𝔽₂`-linear
   dual; (126) as `2|E| · N(κ,ε) = |W| + G(Q) Σ_χ (−1)^{χ(κ)+ε+Q(a_χ)}`.  In (126) the
   paper *defines* `a_χ` from nonsingularity; here `a` is **data with the defining spec**
   `B_Q(a_χ, x) = χ(L x)` (house style, cf. `prop_7_4`'s `lam`), and nonsingularity is not
   needed for the identity itself.
2. **Central double covers are a structure** (`CentralCover`): a surjection `p : Ỹ ↠ Y`
   with central kernel `⟨z⟩` of order 2.  The pulled-back boundary-framed structure of
   Lemma 8.3 is `CentralCover.pullTarget`; the paper's side condition "the central kernel
   lies in `ker(π̃, θ̃)`" holds by construction (`π̃ = π_Y ∘ p` kills `ker p`).
3. **"Scalar pushout vanishes" / "pullback cover is split" is encoded as liftability**:
   `u^β_Γ(p, J)` (`liftableCount`) counts boundary-framed exact-image maps to the
   `J`-stratum that lift through `p` as continuous homomorphisms.  This is the paper's
   torsor description verbatim (an unobstructed map has a lift, and its exact-image lifts
   are the summands of (124)).
4. **Lemma 8.6's edge class is carried operationally.**  The `H¹`-valued edge `[ε̄]` of
   (128) exists iff the cover does **not** descend to `B/T`; the paper's own descent
   clause says a descended cover is exactly *a normal complement to the preimage of `T`*.
   We therefore phrase "edge ≠ 0" as `¬∃ N ◁ B̃, N.map p = T ∧ z ∉ N`, and state the
   half-torsor count in consequence form, **per source** (the degree-one duality that
   makes the variation functional (127) nonzero is B6 on the local side and §5 content on
   the candidate side, so a source-generic statement would need a duality hypothesis —
   flagged deviation; the `H¹`-form (128)/(127) is P-16-proof-internal).
5. **Lemma 8.7 and Prop 8.8 are not separately stated** (P-14 precedent: 6.7/6.10/6.11):
   they are proof mechanisms for the (140)-clause of Prop 8.9.  Their content enters the
   statement layer only through the `∃`-form of (140) below.  If P-17 needs (131)/(135)
   as standalone statements, that is a reviewed addition.
6. **Prop 8.9 is frozen as the boxed system.**  (136)–(139) are stated verbatim (integer
   multiplied-out forms, target-side data from the §7 block).  The scalar characters
   `λ ∈ D_R = (R^∨)^C` are encoded as **`Y`-normal subgroups `R' ≤ R` of index ≤ 2**
   (the kernel of `λ`; `Y`-normality = `C`-invariance — same encoding as
   `lemma_7_1_dual`), and the scalar cover `p_λ : B_λ ↠ B` is the quotient map
   `Y/R' ↠ Y/R`.  **(140)–(142) are frozen in `∃`-family form**: there exist a constant
   `μ` and a target-side family of central covers of the `C`-stratum, indexed by the
   scalar duals of `T`, satisfying (140) with `s_Γ` folded through (141)/(142) (the
   `n_{Γ,0}`-liftability form).  The family is target-side data, so **one** witness
   serves both sources — which is all the §9 induction uses.  Pinning the family to the
   phase classes `Δ_{χ,κ}` of (133)/(134) is the O-half's work (via 6.21/6.22/8.8).

Axioms: none in this file (statement layer; sorried statements are allowlisted under
P-16; the **Ax** budget B6/B7/B9 is consumed by the O-half proofs).
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
  have ha₀' : ψ a₀ = 1 := by
    have h2 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rcases h2 (ψ a₀) with h | h
    · exact absurd h ha₀
    · exact h
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
  linarith

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
    refine sum_sign_eq_zero (fun φ : Module.Dual (ZMod 2) W => φ w) (fun φ φ' => rfl) ?_
    intro hall
    exact hw ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) w).mp (fun φ => hall φ))

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
  have h : ((1 : ZMod 2) + 1) • m = m + m := by rw [add_smul, one_smul]
  rw [← h, show ((1 : ZMod 2) + 1) = 0 from by decide, zero_smul]

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
      have hLiff : L x + κ = 0 ↔ L x = κ := by
        constructor
        · intro h
          have h' := congrArg (· + κ) h
          simpa [add_assoc, add_self_fp2] using h'
        · rintro rfl
          exact add_self_fp2 _
      have hQiff : Q x + ε = 0 ↔ Q x = ε :=
        (show ∀ u v : ZMod 2, (u + v = 0 ↔ u = v) from by decide) (Q x) ε
      rw [one_add_sign]
      by_cases h1 : L x = κ <;> by_cases h2 : Q x = ε
      · rw [if_pos (hLiff.mpr h1), if_pos (hQiff.mpr h2), if_pos ⟨h1, h2⟩]
        ring
      · rw [if_pos (hLiff.mpr h1), if_neg (fun h : Q x + ε = 0 => h2 (hQiff.mp h)),
          if_neg (fun h : L x = κ ∧ Q x = ε => h2 h.2)]
        ring
      · rw [if_neg (fun h : L x + κ = 0 => h1 (hLiff.mp h)),
          if_neg (fun h : L x = κ ∧ Q x = ε => h1 h.1)]
        ring
      · rw [if_neg (fun h : L x + κ = 0 => h1 (hLiff.mp h)),
          if_neg (fun h : L x = κ ∧ Q x = ε => h1 h.1)]
        ring
    rw [hT, Finset.sum_congr rfl fun x _ => hx x, ← Finset.sum_filter, Finset.sum_const,
      Nat.card_eq_fintype_card (α := {x : W // L x = κ ∧ Q x = ε}), Fintype.card_subtype]
    ring
  -- Way 2: expand the product; the two double sums are `|W|` and the Gauss term.
  have hway2 : T = (Nat.card W : ℤ) + gaussSum Q *
      ∑ᶠ χ : Module.Dual (ZMod 2) E, sign (χ κ + ε + Q (a χ)) := by
    have hsplit : T = (∑ χ : Module.Dual (ZMod 2) E, ∑ x : W, sign (χ (L x + κ)))
        + ∑ χ : Module.Dual (ZMod 2) E, ∑ x : W, sign (χ (L x + κ)) * sign (Q x + ε) := by
      rw [hT, Finset.sum_comm]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
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
            = ∑ x : W, sign (χ κ) * sign (χ (L x)) := by
              refine Finset.sum_congr rfl fun x _ => ?_
              rw [map_add, sign_add, mul_comm]
          _ = sign (χ κ) * ∑ x : W, sign (χ (L x)) := by rw [Finset.mul_sum]
          _ = 0 := by rw [← finsum_eq_sum_of_fintype, hzero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
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

/-! ## Central double covers and the pulled-back boundary-framed structure  (Lemma 8.3 setup)

A **central double cover** `p : Ỹ ↠ Y` carries its own group/topology data (all finite
discrete).  The pulled-back marked target `(Ỹ, p⁻¹(L_Y), π_Y∘p, θ_Y∘p)` of Lemma 8.3 is
`pullTarget`; the paper's condition "the central kernel lies in `ker(π̃, θ̃)`" holds by
construction. -/

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **A central double cover** of the finite group `Y` (§8): a surjection whose kernel is
generated by a central element `z ≠ 1` of square one. -/
structure CentralCover (Y : Type) [Group Y] [Finite Y] where
  /-- The covering group. -/
  cover : Type
  [group : Group cover]
  [finite : Finite cover]
  [topo : TopologicalSpace cover]
  [disc : DiscreteTopology cover]
  /-- The covering surjection. -/
  p : cover →* Y
  surj : Function.Surjective p
  /-- The central kernel generator. -/
  z : cover
  z_ne : z ≠ 1
  z_sq : z * z = 1
  central : ∀ x : cover, z * x = x * z
  ker_eq : p.ker = Subgroup.zpowers z

attribute [instance] CentralCover.group CentralCover.finite CentralCover.topo
  CentralCover.disc

namespace CentralCover

variable {Y : Type} [Group Y] [Finite Y] (C : CentralCover Y)

/-- Squares die in the kernel subgroup `⟨z⟩` (its elements have order ≤ 2). -/
lemma sq_eq_one_of_mem_ker {x : C.cover} (hx : x ∈ C.p.ker) : x * x = 1 := by
  rw [C.ker_eq] at hx
  obtain ⟨n, rfl⟩ := hx
  rw [← Commute.mul_zpow (Commute.refl C.z), C.z_sq, one_zpow]

/-- **The pulled-back boundary-framed structure** (Lemma 8.3): give `Ỹ` the marked normal
2-subgroup `p⁻¹(L_Y)`, head `π_Y ∘ p`, decoration `θ_Y ∘ p`. -/
noncomputable def pullTarget (T : MarkedTarget H E Y) : MarkedTarget H E C.cover where
  LY := T.LY.comap C.p
  normal := T.normal.comap C.p
  isPGroup_two := by
    intro x
    obtain ⟨k, hk⟩ := T.isPGroup_two ⟨C.p x.1, x.2⟩
    refine ⟨k + 1, ?_⟩
    have hval : (C.p x.1) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h
    have hker : x.1 ^ 2 ^ k ∈ C.p.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hval
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

/-! ## Liftable counts and the totalized stratum count -/

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

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

variable [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]

variable {Y : Type} [Group Y] [Finite Y]

omit [TopologicalSpace (ZMod 2)]
  [DiscreteTopology (ZMod 2)] in
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
    rw [hc, zpow_val_add]
    -- move the central factor across `f δ`
    have hcentral : ∀ (n : ℕ) (w : C.cover), C.z ^ n * w = w * C.z ^ n := by
      intro n w
      induction n with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, mul_assoc, C.central, ← mul_assoc, ih, mul_assoc]
    rw [map_mul]
    calc f γ * f δ * (C.z ^ ((c γ).toAdd).val * C.z ^ ((c δ).toAdd).val)
        = f γ * (f δ * C.z ^ ((c γ).toAdd).val) * C.z ^ ((c δ).toAdd).val := by
          group
      _ = f γ * (C.z ^ ((c γ).toAdd).val * f δ) * C.z ^ ((c δ).toAdd).val := by
          rw [hcentral]
      _ = f γ * C.z ^ ((c γ).toAdd).val * (f δ * C.z ^ ((c δ).toAdd).val) := by
          group
  continuous_toFun := by
    refine Continuous.mul (map_continuous f) ?_
    exact (continuous_of_discreteTopology
      (f := fun m : Multiplicative (ZMod 2) => C.z ^ (m.toAdd).val)).comp (map_continuous c)

/-- **Scalar twisting preserves the boundary-framed condition** on a pulled-back cover
target (Lemma 8.2, second clause): the twist changes only the central coordinate, which
`π̃` and `θ̃` kill.  **Proved.** -/
theorem isBoundaryLift_scalarTwist {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) (C : CentralCover Y)
    (f : ContinuousMonoidHom Γ C.cover)
    (c : ContinuousMonoidHom Γ (Multiplicative (ZMod 2)))
    (hf : IsBoundaryLift b F (C.pullTarget T) f) :
    IsBoundaryLift b F (C.pullTarget T) (scalarTwist C f c) := by
  intro γ
  have hz : ∀ n : ℕ, C.p (C.z ^ n) = 1 := by
    intro n
    rw [map_pow]
    have : C.p C.z = 1 := by
      have : C.z ∈ C.p.ker := by
        rw [C.ker_eq]
        exact Subgroup.mem_zpowers _
      rwa [MonoidHom.mem_ker] at this
    rw [this, one_pow]
  have hval : ∀ (g : Γ → C.cover) (γ), (C.pullTarget T).piY (g γ) = T.piY (C.p (g γ)) := by
    intro g γ
    rfl
  show ((C.pullTarget T).piY _, (C.pullTarget T).thetaY _) = F.frameMap (b γ)
  have h1 : (C.pullTarget T).piY (scalarTwist C f c γ) = (C.pullTarget T).piY (f γ) := by
    show T.piY (C.p (f γ * C.z ^ ((c γ).toAdd).val)) = T.piY (C.p (f γ))
    rw [map_mul, hz, mul_one]
  have h2 : (C.pullTarget T).thetaY (scalarTwist C f c γ)
      = (C.pullTarget T).thetaY (f γ) := by
    show T.thetaY (C.p (f γ * C.z ^ ((c γ).toAdd).val)) = T.thetaY (C.p (f γ))
    rw [map_mul, hz, mul_one]
  rw [h1, h2]
  exact hf γ

end Twist

/-! ## Lemma 8.2: the common scalar character group

The `Γ_A`-side proof runs entirely over the P-04/P-05 layer: continuous characters of
`Γ_A` are `F₄`-generator values killing `N_A`; killing `N_A` forces `c(τ) = 1`
(`tameRelator_mem_NA`), and conversely `c(τ) = 1` makes `ker c` admissible — because in an
**exponent-2 abelian** quotient the whole `ω₂`-word ledger collapses and the wild relation
(6) holds *unconditionally* (`wildRel_of_comm2` below, the §8 counterpart of the
`AppendixB` ledger evaluations). -/

section ExpTwoLedger

variable {A : Type*} [Group A]

/-- `powOmega2` is the identity on involutions (`orderOf ∣ 2` means order `2^0` or `2^1`). -/
lemma powOmega2_eq_self_of_sq (h2 : ∀ a : A, a * a = 1) (a : A) : powOmega2 a = a := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2 a)
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd) with h | h
  · exact powOmega2_eq_self_of_orderOf_two_pow (k := 0) (by simpa using h)
  · exact powOmega2_eq_self_of_orderOf_two_pow (k := 1) (by simpa using h)

/-- In an abelian group, the paper's conjugation is trivial. -/
lemma conjP_of_comm (hcomm : ∀ a b : A, a * b = b * a) (x g : A) : conjP x g = x := by
  rw [conjP, hcomm g⁻¹ x, mul_assoc, inv_mul_cancel, mul_one]

/-- In an abelian group, the paper's commutator is trivial. -/
lemma commP_of_comm (hcomm : ∀ a b : A, a * b = b * a) (x y : A) : commP x y = 1 := by
  rw [commP, mul_assoc x⁻¹ y⁻¹ x, hcomm y⁻¹ x, ← mul_assoc x⁻¹ x y⁻¹, inv_mul_cancel,
    one_mul, inv_mul_cancel]

/-- **The wild relation holds in every exponent-2 abelian group** (the `ω₂`-ledger
collapse: `σ₂ = σ`, `uᵢ = xᵢτ`, `d₀ = τ`, `c₀ = h_c = 1`, `g₀ = 1`, `h₀ = τ`, and (6)
telescopes to `1`).  This is why scalar characters see no wild obstruction. -/
lemma Marking.wildRel_of_comm2 (hcomm : ∀ a b : A, a * b = b * a)
    (h2 : ∀ a : A, a * a = 1) (t : Marking A) : t.WildRel := by
  have hpow : ∀ a : A, powOmega2 a = a := powOmega2_eq_self_of_sq h2
  have hconj : ∀ x g : A, conjP x g = x := conjP_of_comm hcomm
  have hcommP : ∀ x y : A, commP x y = 1 := commP_of_comm hcomm
  have hσ2 : t.sigma2 = t.σ := by rw [Marking.sigma2, hpow]
  have hu0 : t.u0 = t.x₀ * t.τ := by rw [Marking.u0, Marking.u, hpow]
  have hu1 : t.u1 = t.x₁ * t.τ := by rw [Marking.u1, Marking.u, hpow]
  have hd0 : t.d0 = t.τ := by
    rw [Marking.d0, hu0, hcomm t.x₀ t.τ, mul_assoc, mul_inv_cancel, mul_one]
  have hg0 : t.g0 = 1 := by rw [Marking.g0, pow_two, hσ2, h2]
  have hz0 : t.z0 = t.x₀ := by rw [Marking.z0, hconj]
  have hc0 : t.c0 = 1 := by rw [Marking.c0, hcommP]
  have hdg : t.dg = t.τ := by rw [Marking.dg, hconj, hd0]
  have hhc : t.hc = 1 := by rw [Marking.hc, hcommP]
  have hh0 : t.h0 = t.τ := by
    rw [Marking.h0, hconj, hdg, hd0, hhc, pow_two, h2, h2]
    simp only [one_mul, mul_one]
  show t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0 = 1
  rw [hh0, hu1, hconj, hc0, mul_one, mul_inv_rev, ← mul_assoc t.τ t.τ⁻¹ t.x₁⁻¹,
    mul_inv_cancel, one_mul, inv_mul_cancel]

/-- In an exponent-2 abelian group, the tame relation says exactly `τ = 1`. -/
lemma Marking.tameRel_iff_of_comm2 (hcomm : ∀ a b : A, a * b = b * a)
    (h2 : ∀ a : A, a * a = 1) (t : Marking A) : t.TameRel ↔ t.τ = 1 := by
  rw [Marking.TameRel, conjP_of_comm hcomm, pow_two, h2]

/-- Exponent 2 forces commutativity (`ab = (ab)⁻¹ = b⁻¹a⁻¹ = ba`). -/
lemma mul_comm_of_exp_two (h2 : ∀ a : A, a * a = 1) (a b : A) : a * b = b * a := by
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h2 x)
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [hinv, hinv]

end ExpTwoLedger

/-! ### The `Γ_A`-side character count -/

section CharGammaA

variable [TopologicalSpace (ZMod 2)]
  [DiscreteTopology (ZMod 2)]

omit [DiscreteTopology (ZMod 2)] in
private lemma comp_quotientMk_ker
    (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) (Multiplicative (ZMod 2))) :
    NA ≤ ((φ.comp (quotientMk NA)).toMonoidHom).ker := fun x hx => by
  rw [MonoidHom.mem_ker]
  show φ (quotientMk NA x) = 1
  rw [(quotientMk_eq_one_iff NA).mpr hx, map_one]

omit [DiscreteTopology (ZMod 2)] in
private lemma quotientLift_comp_eq
    (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) (Multiplicative (ZMod 2))) :
    quotientLift NA (φ.comp (quotientMk NA)) (comp_quotientMk_ker φ) = φ := by
  ext y
  obtain ⟨x, rfl⟩ := quotientMk_surjective NA y
  rfl

omit [DiscreteTopology (ZMod 2)] in
private lemma comp_quotientLift_eq
    (c : {c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Multiplicative (ZMod 2)) //
      NA ≤ c.toMonoidHom.ker}) :
    (quotientLift NA c.1 c.2).comp (quotientMk NA) = c.1 := by
  ext x
  rfl

/-- Characters of `Γ_A = F₄ ⧸ N_A` are characters of `F₄` killing `N_A`
(the P-05 `push`/`descend` mechanics, without surjectivity). -/
noncomputable def charEquiv :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) (Multiplicative (ZMod 2))
      ≃ {c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Multiplicative (ZMod 2)) //
          NA ≤ c.toMonoidHom.ker} where
  toFun φ := ⟨φ.comp (quotientMk NA), comp_quotientMk_ker φ⟩
  invFun c := quotientLift NA c.1 c.2
  left_inv φ := quotientLift_comp_eq φ
  right_inv c := Subtype.ext (comp_quotientLift_eq c)

private lemma homEquiv_symm_hom_of_values
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Multiplicative (ZMod 2))) :
    ((FreeProfiniteGroup.homEquiv (Fin 4)
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm
        (fun i => c (FreeProfiniteGroup.of i))).hom = c := by
  have h : (FreeProfiniteGroup.homEquiv (Fin 4)
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm
        (fun i => c (FreeProfiniteGroup.of i))
      = CategoryTheory.ConcreteCategory.ofHom (C := ProfiniteGrp) c := by
    rw [Equiv.symm_apply_eq]
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply]
    rfl
  rw [h]
  rfl

/-- Characters of `F₄` are their generator values (the universal property, in
`ContinuousMonoidHom` form via the P-05 uniqueness lemma). -/
noncomputable def cmhEquivFun :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Multiplicative (ZMod 2))
      ≃ (Fin 4 → Multiplicative (ZMod 2)) where
  toFun c i := c (FreeProfiniteGroup.of i)
  invFun v :=
    ((FreeProfiniteGroup.homEquiv (Fin 4)
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm v).hom
  left_inv c := homEquiv_symm_hom_of_values c
  right_inv v := funext fun i =>
    FreeProfiniteGroup.homEquiv_symm_of (ProfiniteGrp.of (Multiplicative (ZMod 2))) v i

/-- **The kills-`N_A` criterion**: a character of `F₄` kills `N_A` iff it kills `τ`.
Forward: `N_A` contains the tame relator (P-04), whose `𝔽₂`-image is `c(τ)`.  Backward:
`ker c` is then an *admissible* open normal subgroup (generation is automatic, the tame
relation is the `τ`-kill, and the wild relation and 2-core are unconditional in an
exponent-2 abelian quotient), so `N_A ≤ ker c` by the P-04 characterization. -/
theorem ker_char_NA_le_iff
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Multiplicative (ZMod 2))) :
    NA ≤ c.toMonoidHom.ker ↔ c univMarking.τ = 1 := by
  constructor
  · intro hNA
    have htame : c univMarking.tameRelator = 1 := by
      have := hNA tameRelator_mem_NA
      rwa [MonoidHom.mem_ker] at this
    rw [Marking.tameRelator, map_mul, map_inv, map_pow,
      show c (conjP univMarking.τ univMarking.σ)
          = (c univMarking.σ)⁻¹ * c univMarking.τ * c univMarking.σ from by
        rw [conjP, map_mul, map_mul, map_inv]] at htame
    have hM2 : ∀ s t : Multiplicative (ZMod 2),
        s⁻¹ * t * s * (t ^ 2)⁻¹ = 1 → t = 1 := by
      decide
    exact hM2 _ _ htame
  · intro hτ
    -- the kernel, as an open normal subgroup
    have hker_open :
        IsOpen ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
      have hset : ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
          = c ⁻¹' {1} := by
        ext g
        simp [MonoidHom.mem_ker]
      rw [hset]
      exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod 2)))).preimage
        c.continuous_toFun
    set U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
      { toSubgroup := c.toMonoidHom.ker, isOpen' := hker_open } with hU
    -- the quotient has order dividing 2, hence is exponent-2 abelian
    haveI : Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) := by
      exact Finite.of_equiv _
        (QuotientGroup.quotientKerEquivRange c.toMonoidHom).symm.toEquiv
    have hcard : Nat.card (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) ∣ 2 := by
      have h3 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
        rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
      calc Nat.card (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)
          = Nat.card c.toMonoidHom.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange c.toMonoidHom).toEquiv
        _ ∣ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_subgroup_dvd_card _
        _ = 2 := h3
    have h2q : ∀ y : FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup, y * y = 1 := by
      intro y
      have horder : orderOf y ∣ 2 := (orderOf_dvd_natCard y).trans hcard
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp horder
    have hcommq : ∀ y z : FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup, y * z = z * y :=
      mul_comm_of_exp_two h2q
    -- `ker c` is admissible
    have hadm : IsAdmissibleU U := by
      refine ⟨generates_univMarking_map U, ?_, Marking.wildRel_of_comm2 hcommq h2q _, ?_⟩
      · refine (Marking.tameRel_iff_of_comm2 hcommq h2q _).mpr ?_
        show QuotientGroup.mk' U.toSubgroup univMarking.τ = 1
        exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr hτ)
      · intro g
        refine ⟨1, ?_⟩
        ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one,
          show (2 : ℕ) ^ 1 = 2 from rfl, pow_two]
        exact h2q _
    exact (isAdmissibleU_iff_NA_le U).mp hadm

/-- Splitting off the `τ`-coordinate. -/
def vecEquiv : {v : Fin 4 → Multiplicative (ZMod 2) // v 1 = 1}
    ≃ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) where
  toFun v := (v.1 0, v.1 2, v.1 3)
  invFun p := ⟨![p.1, 1, p.2.1, p.2.2], rfl⟩
  left_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · rfl
    · exact v.2.symm
    · rfl
    · rfl
  right_inv p := rfl

end CharGammaA

/-- **Lemma 8.2, candidate source**: `|Hom_cont(Γ_A, 𝔽₂)| = 8`.  **Proved** over the
P-04/P-05 layer: characters of `Γ_A` are `F₄`-generator values killing `N_A`
(`charEquiv`/`cmhEquivFun`), and killing `N_A` is exactly killing `τ`
(`ker_char_NA_le_iff` — the tame relator forces it, and conversely `ker c` is admissible
because the wild relation is unconditional in exponent-2 abelian quotients,
`Marking.wildRel_of_comm2`).  That leaves the free `𝔽₂³` of `σ, x₀, x₁`-values. -/
theorem lemma_8_2_gammaA [TopologicalSpace (ZMod 2)]
    [DiscreteTopology (ZMod 2)] :
    Nat.card (ContinuousMonoidHom GammaA (Multiplicative (ZMod 2))) = 8 := by
  have e := charEquiv.trans
    ((Equiv.subtypeEquiv cmhEquivFun (fun c => ker_char_NA_le_iff c)).trans vecEquiv)
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact (Nat.card_congr e).trans (by rw [Nat.card_prod, Nat.card_prod, h2])

/-- **Lemma 8.2, local source**: `|Hom_cont(G_ℚ₂, 𝔽₂)| = 8` (`= |ℚ₂ˣ/(ℚ₂ˣ)²|`; via the
common marked maximal pro-2 quotient).  [P-16 statement; proof = O-half.] -/
theorem lemma_8_2_local [TopologicalSpace (ZMod 2)]
    [DiscreteTopology (ZMod 2)] :
    Nat.card (ContinuousMonoidHom AbsGalQ2 (Multiplicative (ZMod 2))) = 8 := by
  sorry

/-! ## Lemma 8.3: the eight-lift partition  (display (124)) -/

/-- **Lemma 8.3 (central-cover exact-image transform, eq. (124))**: for a central double
cover `p : Ỹ ↠ Y` with pulled-back boundary-framed structure, and an exact-image subgroup
`J ≤ Y` projecting onto `H`,
`8 · u^β_Γ(p, J) = Σ_{J̃ ≤ p⁻¹(J), p(J̃) = J} e^β_Γ(J̃)`,
where the right side runs over the exact-image strata of the cover target.  The `8` is the
scalar character count of Lemma 8.2, carried as the hypothesis `hscalar`; scalar twisting
(the proved `isBoundaryLift_scalarTwist`) is the torsor action behind the partition.
[P-16 statement; proof = O-half.] -/
theorem lemma_8_3 [TopologicalSpace (ZMod 2)]
    [DiscreteTopology (ZMod 2)]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) (C : CentralCover Y)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    8 * liftableCount b F T C J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
          exactImageCountOn b F (C.pullTarget T) J' := by
  sorry

/-! ## Lemma 8.6: radical edge and the half-torsor count

The §8 datum: a central double cover of `B` whose restriction to the elementary abelian
`M ◁ B` is a quadratic form (the square map into `⟨z⟩`) with polar radical `T` and vanishing
on `T`.  The `H¹`-valued edge class of (128) is carried **operationally**: the cover
descends to `B/T` iff `p⁻¹(T)` has a normal complement missing `z` (the paper's own descent
clause), and "edge ≠ 0" is the negation. -/

/-- The multiplicative polar form of a `𝔽₂`-valued square function on (a subgroup of) a
group: `B_q(m, m') = q(mm') + q(m) + q(m')`. -/
def polarMul {M : Type*} (q : M → ZMod 2) (mul : M → M → M) (m m' : M) : ZMod 2 :=
  q (mul m m') + q m + q m'

/-- **The Lemma 8.6 datum**: a central double cover of `Bg` restricting to a quadratic form
on the elementary abelian normal subgroup `M`, with polar radical containing `T ≤ M` and
vanishing on `T` (paper §8, setting of Lemma 8.6; `M = K/R`, `T = T₀` after §7). -/
structure RadicalCoverData (Bg : Type) [Group Bg] [Finite Bg] where
  /-- The central double cover `p : B̃ ↠ B`. -/
  C : CentralCover Bg
  /-- The elementary abelian layer `M` (paper: `M = K/R`). -/
  M : Subgroup Bg
  hM : M.Normal
  /-- The polar radical `T` (paper: `T = T₀`). -/
  T : Subgroup Bg
  hT : T.Normal
  hTM : T ≤ M
  helem : ∀ m ∈ M, m * m = 1
  hcomm : ∀ m ∈ M, ∀ m' ∈ M, m * m' = m' * m
  /-- The square form of the cover on `M`: `x̃² = z^{q(x)}` for any lift `x̃` of `x ∈ M`. -/
  q : ↥M → ZMod 2
  hq : ∀ (x : C.cover) (hx : C.p x ∈ M), x * x = C.z ^ (q ⟨C.p x, hx⟩).val
  /-- `T` lies in the polar radical of `q`. -/
  hrad : ∀ (t : Bg) (ht : t ∈ T) (m : Bg) (hm : m ∈ M),
    polarMul q (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩) ⟨t, hTM ht⟩ ⟨m, hm⟩ = 0
  /-- `q` vanishes on `T`. -/
  hTzero : ∀ (t : Bg) (ht : t ∈ T), q ⟨t, hTM ht⟩ = 0

/-- The `M`-layer of a `RadicalCoverData` is normal (instance form, so that the quotient
`Bg ⧸ D.M` carries its group structure in statement positions — the `TameQuotientData`
Lean-detail pattern). -/
instance RadicalCoverData.instNormalM {Bg : Type} [Group Bg] [Finite Bg]
    (D : RadicalCoverData Bg) : D.M.Normal := D.hM

/-- **"The radical edge is nonzero", operationally** (Lemma 8.6, descent clause): the cover
admits **no** descent to `B/T`, i.e. no normal complement to `p⁻¹(T)` missing `z`. -/
def RadicalCoverData.NoDescent {Bg : Type} [Group Bg] [Finite Bg]
    (D : RadicalCoverData Bg) : Prop :=
  ¬∃ N : Subgroup D.C.cover, N.Normal ∧ N.map D.C.p = D.T ∧ D.C.z ∉ N

section HalfTorsor

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

/-- The unrestricted `M`-lifts of a lower map `ρ : Γ → B/M`: continuous homomorphisms
`f : Γ → B` over `ρ`. -/
def MLifts (D : RadicalCoverData Bg) {Γ' : Type} [Group Γ'] [TopologicalSpace Γ']
    (ρ : ContinuousMonoidHom Γ' (Bg ⧸ D.M)) : Type :=
  {f : ContinuousMonoidHom Γ' Bg // ∀ γ : Γ', QuotientGroup.mk (f γ) = ρ γ}

/-- An `M`-lift **satisfies the central relation** when it lifts through the cover. -/
def MLifts.Central (D : RadicalCoverData Bg) {Γ' : Type} [Group Γ'] [TopologicalSpace Γ']
    {ρ : ContinuousMonoidHom Γ' (Bg ⧸ D.M)}
    (f : MLifts D ρ) : Prop :=
  ∃ g : ContinuousMonoidHom Γ' D.C.cover, ∀ γ : Γ', D.C.p (g γ) = f.1 γ

/-- **Lemma 8.6 (half-torsor count), candidate source**: with a nonzero radical edge, for
every lower *epimorphism* `ρ : Γ_A ↠ B/M`, exactly half of the unrestricted `M`-lifts of
`ρ` satisfy the central relation.  (The degree-one duality making the variation functional
(127) nonzero is §5 content for `Γ_A` — B7 enters through 5.15/5.16.)
[P-16 statement; proof = O-half.] -/
theorem lemma_8_6_gammaA (D : RadicalCoverData Bg)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GammaA (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  sorry

/-- **Lemma 8.6 (half-torsor count), local source**: as `lemma_8_6_gammaA`, for `G_ℚ₂`
(degree-one duality = B6).  [P-16 statement; proof = O-half.] -/
theorem lemma_8_6_local (D : RadicalCoverData Bg)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  sorry

end HalfTorsor

/-! ## Proposition 8.9: the closed exact-image recursion  (displays (136)–(142))

Target-side data: the §7 block on `𝒴` with `B = Y/R`, `C = Y/K`, carried as a
`RecursionFrame` (quotient targets pinned by spec fields; the scalar characters
`λ ∈ D_R = (R^∨)^C` indexed by a finite type with a distinguished `0`, nonzero `λ`
carrying their scalar central covers `p_λ : B_λ ↠ B`).  The boxed equations are the
fields of the source-generic `ClosedRecursion`; `prop_8_9` asserts the system for **both
sources with one shared** `(μ, G⁰, phase family)` — which is exactly how the §9 induction
consumes it (the paper pins `μ = |B¹(V)||Z¹(T)|` via 5.15/5.16, `G⁰` as the Gauss sum of
the 7.4 form, and the family as the `Δ_{χ,κ}`-covers of (134); that pinning is the O-half's
construction, a flagged deviation). -/

section Recursion

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- **The §8 recursion frame** on a marked target with a §7 block: the two quotient stages
`B = Y/R`, `C = Y/K` as boundary-framed targets (pinned to `𝒴` by the spec fields), the
connecting epimorphism, the images of `M = K/R` and `T = T₀`, and the scalar character
index `D_R` with its central covers. -/
structure RecursionFrame (T : MarkedTarget H E Y)
    (Blk : SectionSeven.MinimalBlock T.LY) where
  /-- The `B`-stage group (paper `B = Y/R`). -/
  YB : Type
  [groupB : Group YB]
  [finiteB : Finite YB]
  [topoB : TopologicalSpace YB]
  [discB : DiscreteTopology YB]
  /-- The projection `Y ↠ B`. -/
  piB : Y →* YB
  piB_surj : Function.Surjective piB
  ker_piB : piB.ker = Blk.R
  /-- The `B`-stage boundary-framed target. -/
  TB : MarkedTarget H E YB
  TB_head : TB.piY.comp piB = T.piY
  TB_theta : TB.thetaY.comp piB = T.thetaY
  /-- The `C`-stage group (paper `C = Y/K`). -/
  YC : Type
  [groupC : Group YC]
  [finiteC : Finite YC]
  [topoC : TopologicalSpace YC]
  [discC : DiscreteTopology YC]
  /-- The projection `Y ↠ C`. -/
  piC : Y →* YC
  piC_surj : Function.Surjective piC
  ker_piC : piC.ker = Blk.K
  /-- The `C`-stage boundary-framed target. -/
  TC : MarkedTarget H E YC
  TC_head : TC.piY.comp piC = T.piY
  TC_theta : TC.thetaY.comp piC = T.thetaY
  /-- The connecting map `B ↠ C`. -/
  piBC : YB →* YC
  piBC_comp : piBC.comp piB = piC
  /-- The image of `M = K/R` in `B`. -/
  MB : Subgroup YB
  MB_eq : MB = Blk.K.map piB
  /-- The image of `T = T₀ = (K ⊓ S)·R` in `B`. -/
  TBsub : Subgroup YB
  TBsub_eq : TBsub = ((Blk.K ⊓ Blk.S) ⊔ Blk.R).map piB
  /-- The scalar character index `D_R = (R^∨)^C`, with distinguished `0`. -/
  DR : Type
  [fintypeDR : Fintype DR]
  zeroDR : DR
  /-- `D_R` has the size of the set of `λ`-kernels: `Y`-normal subgroups of `R` of relative
  index ≤ 2 (`λ = 0 ↔ R' = R`; `Y`-normality = `C`-invariance, the `lemma_7_1_dual`
  encoding). -/
  card_DR : Nat.card DR = Nat.card {R' : Subgroup Y //
    R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}
  /-- The scalar central cover `p_λ : B_λ ↠ B` of each nonzero `λ` (paper §7.1: the pushout
  `K_λ = K/ker λ`, realized as `Y/ker λ ↠ Y/R`). -/
  scalarCover : (l : DR) → l ≠ zeroDR → CentralCover YB

attribute [instance] RecursionFrame.groupB RecursionFrame.finiteB RecursionFrame.topoB
  RecursionFrame.discB RecursionFrame.groupC RecursionFrame.finiteC RecursionFrame.topoC
  RecursionFrame.discC RecursionFrame.fintypeDR

namespace RecursionFrame

variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable (RF : RecursionFrame T Blk)
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)

/-- `z_R = |Z¹_{Γ,ρ}(R)| = 2^{2·dim R + dim D_R}` (paper, before (136)), in card form:
`|R|² · |D_R|`. -/
noncomputable def zR : ℕ := (Nat.card ↥Blk.R) ^ 2 * Nat.card RF.DR

open scoped Classical in
/-- `m_{Γ,λ}(B)` (paper, before (136)): for `λ = 0`, `e_Γ(B)`; for `λ ≠ 0`, the number of
boundary-framed exact-image maps onto `B` whose `λ`-scalar pushout vanishes — i.e. which
lift through `p_λ` (`liftableCount` at the top stratum). -/
noncomputable def mB (l : RF.DR) : ℕ :=
  if h : l = RF.zeroDR then exactImageCount b F RF.TB
  else Nat.card {f : BoundaryLifts b F RF.TB //
    ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
      ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = f.1.1 γ}

open scoped Classical in
/-- `m_{Γ,λ}(J)` for a proper exact-image stratum `J < B` (the summands of (137), computed
by (138)): boundary-framed exact-image maps onto the `J`-stratum lifting through `p_λ`. -/
noncomputable def mJ (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
    (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)) : ℕ :=
  liftableCount b F RF.TB (RF.scalarCover l h) J hJ

open scoped Classical in
/-- `m_{Γ,λ}(J)`, totalized over all subgroups (`0` when `J` misses the `H`-head — such
strata carry no boundary lifts, so the totalization is faithful). -/
noncomputable def mJOn (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB) : ℕ :=
  if hJ : Function.Surjective (RF.TB.piY.comp J.subtype) then RF.mJ b F l h J hJ else 0

/-- `Z_{Γ,λ}(B/C)` (paper, (137)): all `p_λ`-compatible lifts of boundary-framed
exact-image maps to `C`, **without** imposing generation in `B` — pairs of an exact-image
`ρ` onto the `C`-target and a boundary-compatible continuous lift `g` into `B_λ` over it. -/
noncomputable def zBC (l : RF.DR) (h : l ≠ RF.zeroDR) : ℕ :=
  Nat.card {pr : BoundaryLifts b F RF.TC ×
      ContinuousMonoidHom Γ (RF.scalarCover l h).cover //
    (∀ γ : Γ, RF.piBC ((RF.scalarCover l h).p (pr.2 γ)) = pr.1.1.1 γ) ∧
      IsBoundaryLift b F ((RF.scalarCover l h).pullTarget RF.TB) pr.2}

/-- `n_{Γ,0}(ζ)` for a phase cover `C_ζ ↠ C` ((141)/(142)): boundary-framed exact-image
maps onto the `C`-target that lift through the cover. -/
noncomputable def nPhase (Cζ : CentralCover RF.YC) : ℕ :=
  Nat.card {f : BoundaryLifts b F RF.TC //
    ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = f.1.1 γ}

end RecursionFrame

open scoped Classical in
/-- **The boxed system of Prop 8.9** for one source `(Γ, b)` and shared data
`(μ, G⁰, phase family)`: the displays (136)–(140), with (141)/(142) folded into (140)
through the `n_{Γ,0}`-liftability form of the signed phase sum (flagged deviation, cf. the
(100)-into-(105) precedent), and all divisions multiplied out. -/
structure ClosedRecursion {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : DT → CentralCover RF.YC) : Prop where
  /-- **(136)**, multiplied out: `|D_R| · e_Γ(Y) = z_R · Σ_{λ ∈ D_R} (2 m_{Γ,λ}(B) − e_Γ(B))`. -/
  eq136 : (Nat.card RF.DR : ℤ) * exactImageCount b F T
    = RF.zR * ∑ᶠ l : RF.DR,
        (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB)
  /-- **(137)**, additively: `Z_{Γ,λ}(B/C) = m_{Γ,λ}(B) + Σ_{J < B} m_{Γ,λ}(J)` (the
  exact-image subtraction; strata missing the `H`-head contribute `0` through the
  totalized `mJOn`). -/
  eq137 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (RF.zBC b F l h : ℤ) = RF.mB b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤}, (RF.mJOn b F l h J : ℤ)
  /-- **(138)**: each proper summand of (137) opens into the eight-lift partition of the
  `λ`-cover (Lemma 8.3's (124), instantiated at `p_λ`). -/
  eq138 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J : Subgroup RF.YB)
      (hJ : Function.Surjective (RF.TB.piY.comp J.subtype)),
    8 * RF.mJ b F l h J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup (RF.scalarCover l h).cover |
          J'.map (RF.scalarCover l h).p = J},
          exactImageCountOn b F ((RF.scalarCover l h).pullTarget RF.TB) J'
  /-- **(139)**: when the `λ`-cover has nonzero radical edge (operationally: no descent to
  `B/T`, cf. `RadicalCoverData.NoDescent`), the compatible-lift count is the half-torsor
  value `2^{2 dim M − 1} e_Γ(C)`, i.e. `2 · Z_{Γ,λ}(B/C) = |M|² · e_Γ(C)`. -/
  eq139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC
  /-- **(140)–(142)**, folded: when the `λ`-cover descends (radical edge zero), the
  compatible-lift count is the constrained Gauss value over the shared phase family:
  `2^{r+1} Z_{Γ,λ}(B/C) = μ (2^d e_Γ(C) + G⁰ Σ_{ζ ∈ D_T} (2 n_{Γ,0}(ζ) − e_Γ(C)))`, with
  `2^{r+1} = 2|D_T|` and `2^d = |M|/|T| = |V|`. -/
  eq140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * RF.zBC b F l h
        = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (RF.nPhase b F (phase ζ) : ℤ) - exactImageCount b F RF.TC))

/-- **Proposition 8.9 (closed exact-image recursion)**: for every boundary-framed target
with a §7 simple-head block and every recursion frame on it, there are **shared** data
`(μ, G⁰, D_T, phase)` — the paper pins them via 5.15/5.16, Prop 7.4, and (133)/(134) —
such that the boxed system (136)–(142) holds for **both sources**.  Every count on the
right sides concerns a target with strictly smaller marked 2-kernel, so the system is a
closed deterministic recursion (paper, end of §8).  [P-16 statement; proof = O-half,
axioms ≤ {B6, B7, B9} per App. D.] -/
theorem prop_8_9 (B : BoundaryMaps) {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (F : BoundaryFrame H E) :
    ∃ (μ : ℕ) (G0 : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : DT → CentralCover RF.YC),
      ClosedRecursion RF B.bA F μ G0 DT phase ∧
        ClosedRecursion RF B.bF F μ G0 DT phase := by
  sorry

end Recursion

end SectionEight

end GQ2
