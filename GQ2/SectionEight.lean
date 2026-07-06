import GQ2.BoundaryFrame
import GQ2.RadicalEdgeData
import GQ2.RadicalEdgeLocal
import GQ2.FrameEnrichment
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
  map_one' := by ext; exact map_one f
  map_mul' x y := by ext; exact map_mul f x y
  continuous_toFun := f.continuous_toFun.subtype_mk h

@[simp] lemma cmhCodRestrict_coe (f : ContinuousMonoidHom G₁ G₂) (S : Subgroup G₂)
    (h : ∀ x, f x ∈ S) (x : G₁) : (cmhCodRestrict f S h x : G₂) = f x := rfl

/-- Include a continuous hom into a subgroup back into the ambient group. -/
def cmhInclude (S : Subgroup G₂) (g : ContinuousMonoidHom G₁ ↥S) : ContinuousMonoidHom G₁ G₂ :=
  ⟨(S.subtype).comp g.toMonoidHom, continuous_subtype_val.comp g.continuous_toFun⟩

@[simp] lemma cmhInclude_apply (S : Subgroup G₂) (g : ContinuousMonoidHom G₁ ↥S) (x : G₁) :
    cmhInclude S g x = (g x : G₂) := rfl

/-- **Homs onto a subgroup ≃ homs into the ambient group landing in it.** -/
def cmhSubgroupEquiv (S : Subgroup G₂) :
    ContinuousMonoidHom G₁ ↥S ≃ {f : ContinuousMonoidHom G₁ G₂ // ∀ x, f x ∈ S} where
  toFun g := ⟨cmhInclude S g, fun x => (g x).2⟩
  invFun f := cmhCodRestrict f.1 S f.2
  left_inv g := by ext x; rfl
  right_inv f := by ext x; rfl

end CodRestrict

/-! ## Liftable counts and the totalized stratum count -/

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]

/-- The covering map bundled as a continuous hom (continuous since the cover is discrete). -/
noncomputable def CentralCover.pCont (C : CentralCover Y) : ContinuousMonoidHom C.cover Y :=
  ⟨C.p, continuous_of_discreteTopology⟩

omit [DiscreteTopology Y] in
@[simp] lemma CentralCover.pCont_apply (C : CentralCover Y) (x : C.cover) :
    C.pCont x = C.p x := rfl

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

/-- `z`-powers are central. -/
lemma z_pow_central (n : ℕ) (w : C.cover) : C.z ^ n * w = w * C.z ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_assoc, C.central, ← mul_assoc, ih, mul_assoc]

/-- Elements of `⟨z⟩` are `1` or `z`. -/
lemma eq_one_or_z_of_mem_ker {w : C.cover} (hw : w ∈ C.p.ker) : w = 1 ∨ w = C.z := by
  rw [C.ker_eq, Subgroup.mem_zpowers_iff] at hw
  obtain ⟨k, rfl⟩ := hw
  have hz2 : C.z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]; exact C.z_sq
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left
    rw [show m + m = 2 * m from by ring, zpow_mul, hz2, one_zpow]
  · right
    rw [show 2 * m + 1 = 2 * m + 1 from rfl, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

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
  have hcancel : C.z ^ ((c γ).toAdd).val = C.z ^ ((c' γ).toAdd).val := by
    have hg : g γ * C.z ^ ((c γ).toAdd).val = g γ * C.z ^ ((c' γ).toAdd).val :=
      DFunLike.congr_fun h γ
    exact mul_left_cancel hg
  rw [z_pow_eq_iff] at hcancel
  have : (c γ).toAdd = (c' γ).toAdd := zmod2_eq_of_val_modEq hcancel
  exact Multiplicative.toAdd.injective this

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
  map_one' := by
    show Multiplicative.ofAdd (liftChar C g g' 1) = 1
    rw [show liftChar C g g' 1 = 0 from by unfold liftChar; rw [if_pos (by rw [map_one, map_one])]]
    rfl
  map_mul' γ δ := by
    show Multiplicative.ofAdd (liftChar C g g' (γ * δ))
      = Multiplicative.ofAdd (liftChar C g g' γ) * Multiplicative.ofAdd (liftChar C g g' δ)
    rw [liftChar_add C g g' h, ofAdd_add]
  continuous_toFun := by
    classical
    have h1 : Continuous (fun γ => (g γ, g' γ) : Γ → C.cover × C.cover) :=
      (map_continuous g).prodMk (map_continuous g')
    exact (continuous_of_discreteTopology (f := fun p : C.cover × C.cover =>
      Multiplicative.ofAdd (if p.1 = p.2 then (0 : ZMod 2) else 1))).comp h1

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

/-! ## Lemma 8.2: the common scalar character group

The `Γ_A`-side proof runs entirely over the P-04/P-05 layer: continuous characters of
`Γ_A` are `F₄`-generator values killing `N_A`; killing `N_A` forces `c(τ) = 1`
(`tameRelator_mem_NA`), and conversely `c(τ) = 1` makes `ker c` admissible — because in an
**exponent-2 abelian** quotient the whole `ω₂`-word ledger collapses and the wild relation
(6) follows from `τ = 1` (`wildRel_of_comm2` below, the §8 counterpart of the
`AppendixB` ledger evaluations; with the paper's `h₀` — eq. (3), including the bare `d₀` —
the wild value at `τ ≠ 1` is `τ`, so the relation is *not* unconditional). -/

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

/-- **The wild relation follows from `τ = 1` in an exponent-2 abelian group** (the `ω₂`-ledger
collapse at `τ = 1`: `uᵢ = xᵢ`, `d₀ = 1`, `c₀ = h_c = 1`, `h₀ = x₀² = 1`, and (6) telescopes to
`1`).  For scalar characters the hypothesis is free — the tame relation already forces `τ = 1`
(`tameRel_iff_of_comm2`), so they see no *additional* wild obstruction.  (Without `τ = 1` the
wild value is `τ`: the paper's `h₀` — eq. (3), with the bare `d₀` — evaluates to `1`, not `τ`.) -/
lemma Marking.wildRel_of_comm2 (hcomm : ∀ a b : A, a * b = b * a)
    (h2 : ∀ a : A, a * a = 1) (t : Marking A) (hτ : t.τ = 1) : t.WildRel := by
  have hpow : ∀ a : A, powOmega2 a = a := powOmega2_eq_self_of_sq h2
  have hconj : ∀ x g : A, conjP x g = x := conjP_of_comm hcomm
  have hcommP : ∀ x y : A, commP x y = 1 := commP_of_comm hcomm
  have hu1 : t.u1 = t.x₁ := by rw [Marking.u1, Marking.u, hpow, hτ, mul_one]
  have hd0 : t.d0 = 1 := by
    rw [Marking.d0, Marking.u0, Marking.u, hpow, hτ, mul_one, mul_inv_cancel]
  have hc0 : t.c0 = 1 := by rw [Marking.c0, hcommP]
  have hdg : t.dg = 1 := by rw [Marking.dg, hconj, hd0]
  have hhc : t.hc = 1 := by rw [Marking.hc, hcommP]
  have hh0 : t.h0 = 1 := by
    rw [Marking.h0, hconj, hdg, hd0, hhc]
    simp only [one_pow, mul_one]
    exact h2 t.x₀
  show t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0 = 1
  rw [hh0, hu1, hconj, hc0, one_mul, mul_one, inv_mul_cancel]

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

private lemma comp_quotientMk_ker {G : Type} [Group G] [TopologicalSpace G]
    (N : Subgroup G) [N.Normal]
    (φ : ContinuousMonoidHom (G ⧸ N) (Multiplicative (ZMod 2))) :
    N ≤ ((φ.comp (quotientMk N)).toMonoidHom).ker := fun x hx => by
  rw [MonoidHom.mem_ker]
  show φ (quotientMk N x) = 1
  rw [(quotientMk_eq_one_iff N).mpr hx, map_one]

private lemma quotientLift_comp_eq {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (φ : ContinuousMonoidHom (G ⧸ N) (Multiplicative (ZMod 2))) :
    quotientLift N (φ.comp (quotientMk N)) (comp_quotientMk_ker N φ) = φ := by
  ext y
  obtain ⟨x, rfl⟩ := quotientMk_surjective N y
  rfl

private lemma comp_quotientLift_eq {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (c : {c : ContinuousMonoidHom G (Multiplicative (ZMod 2)) //
      N ≤ c.toMonoidHom.ker}) :
    (quotientLift N c.1 c.2).comp (quotientMk N) = c.1 := by
  ext x
  rfl

/-- Characters of a topological quotient group `G ⧸ N` are characters of `G` killing `N`
(the P-05 `push`/`descend` mechanics, without surjectivity; instantiated at `N_A` for the
`Γ_A`-count and at the relator subgroup for the `Π`-count). -/
noncomputable def charEquiv {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] :
    ContinuousMonoidHom (G ⧸ N) (Multiplicative (ZMod 2))
      ≃ {c : ContinuousMonoidHom G (Multiplicative (ZMod 2)) //
          N ≤ c.toMonoidHom.ker} where
  toFun φ := ⟨φ.comp (quotientMk N), comp_quotientMk_ker N φ⟩
  invFun c := quotientLift N c.1 c.2
  left_inv φ := quotientLift_comp_eq N φ
  right_inv c := Subtype.ext (comp_quotientLift_eq N c)

private lemma homEquiv_symm_hom_of_values {X : Type}
    (c : ContinuousMonoidHom (FreeProfiniteGroup X) (Multiplicative (ZMod 2))) :
    ((FreeProfiniteGroup.homEquiv X
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm
        (fun i => c (FreeProfiniteGroup.of i))).hom = c := by
  have h : (FreeProfiniteGroup.homEquiv X
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm
        (fun i => c (FreeProfiniteGroup.of i))
      = CategoryTheory.ConcreteCategory.ofHom (C := ProfiniteGrp) c := by
    rw [Equiv.symm_apply_eq]
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply]
    rfl
  rw [h]
  rfl

/-- Characters of a free profinite group are their generator values (the universal
property, in `ContinuousMonoidHom` form via the P-05 uniqueness lemma). -/
noncomputable def cmhEquivFun {X : Type} :
    ContinuousMonoidHom (FreeProfiniteGroup X) (Multiplicative (ZMod 2))
      ≃ (X → Multiplicative (ZMod 2)) where
  toFun c i := c (FreeProfiniteGroup.of i)
  invFun v :=
    ((FreeProfiniteGroup.homEquiv X
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
    have hτq : (univMarking.map (QuotientGroup.mk' U.toSubgroup)).τ = 1 := by
      show QuotientGroup.mk' U.toSubgroup univMarking.τ = 1
      exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr hτ)
    have hadm : IsAdmissibleU U := by
      refine ⟨generates_univMarking_map U, ?_,
        Marking.wildRel_of_comm2 hcommq h2q _ hτq, ?_⟩
      · exact (Marking.tameRel_iff_of_comm2 hcommq h2q _).mpr hτq
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
(`ker_char_NA_le_iff` — the tame relator forces it, and conversely `c(τ) = 1` gives both
relations in exponent-2 abelian quotients, `Marking.wildRel_of_comm2`).  That leaves the free
`𝔽₂³` of `σ, x₀, x₁`-values. -/
theorem lemma_8_2_gammaA :
    Nat.card (ContinuousMonoidHom GammaA (Multiplicative (ZMod 2))) = 8 := by
  have e := (charEquiv NA).trans
    ((Equiv.subtypeEquiv cmhEquivFun (fun c => ker_char_NA_le_iff c)).trans vecEquiv)
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact (Nat.card_congr e).trans (by rw [Nat.card_prod, Nat.card_prod, h2])

/-! ### The `Π`-side count and the local source

`𝔽₂`-characters kill the pro-2 kernel (T-05), so they factor through the maximal pro-2
quotient; `BoundaryMaps.ker_pro2F` pins that quotient as `Π`, whose characters are the
free `𝔽₂³` of `σ, x₀, x₁`-values (the `piRelator`-condition is vacuous by the same
exponent-2 ledger collapse). -/

/-- `𝔽₂` is a 2-group. -/
private lemma isPGroup_M2 : IsPGroup 2 (Multiplicative (ZMod 2)) := fun g =>
  ⟨1, by
    have h : ∀ h : Multiplicative (ZMod 2), h * h = 1 := by decide
    rw [show (2 : ℕ) ^ 1 = 2 from rfl, pow_two]
    exact h g⟩

private lemma comm_M2 : ∀ a b : Multiplicative (ZMod 2), a * b = b * a := by decide

private lemma sq_M2 : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide

/-- `𝔽₂` is pro-2 (finite discrete 2-group). -/
private lemma isProP_M2 :
    IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup isPGroup_M2

/-- Every `𝔽₂`-character of `F₃` kills `piRelator` (the exponent-2 ledger collapse:
`x₀^{σ²}·x₀·[x₁,σ] ↦ c(x₀)² = 1`). -/
private lemma char_kills_piRelator
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2))) :
    c piRelator = 1 := by
  have hexp : c piRelator
      = conjP (c (FreeProfiniteGroup.of 1)) (c (FreeProfiniteGroup.of 0) ^ 2)
          * c (FreeProfiniteGroup.of 1)
          * commP (c (FreeProfiniteGroup.of 2)) (c (FreeProfiniteGroup.of 0)) := by
    rw [piRelator, conjP, commP]
    simp only [map_mul, map_inv, map_pow]
    rw [conjP, commP]
  rw [hexp, conjP_of_comm comm_M2, commP_of_comm comm_M2, mul_one, sq_M2]

/-- The relator generates its relator subgroup's kernel condition: a character killing the
relator kills the whole (closed normal) relator subgroup — the `presentationLift` argument. -/
private lemma relatorSubgroup_le_ker
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2))) :
    relatorSubgroup {piRelator} ≤ c.toMonoidHom.ker := by
  have hker : IsClosed (c.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3))) := by
    have hset : (c.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3))) = c ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage c.continuous_toFun isClosed_singleton
  exact Subgroup.topologicalClosure_minimal _
    (Subgroup.normalClosure_le_normal fun r hr => by
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact MonoidHom.mem_ker.mpr (char_kills_piRelator c)) hker

/-- Splitting the three `Π`-generator values. -/
private def vecEquiv₃ : (Fin 3 → Multiplicative (ZMod 2))
    ≃ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) where
  toFun v := (v 0, v 1, v 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

/-- **The `Π`-character count**: `|Hom_cont(Π, 𝔽₂)| = 8` — the presentation has three
generators and its relator has no mod-2 linear part (paper, proof of Lemma 8.2). -/
theorem card_char_piBd :
    Nat.card (ContinuousMonoidHom PiBd (Multiplicative (ZMod 2))) = 8 := by
  -- peel the maximal-pro-2 layer (T-05 universal property; `𝔽₂` is pro-2)
  have e1 : ContinuousMonoidHom PiBd (Multiplicative (ZMod 2))
      ≃ ContinuousMonoidHom (profinitePresentation {piRelator}) (Multiplicative (ZMod 2)) :=
    maxProPHomEquiv isProP_M2
  -- peel the presentation layer (characters of the quotient = characters killing relators)
  have e2 := charEquiv (G := FreeProfiniteGroup (Fin 3)) (relatorSubgroup {piRelator})
  -- the kernel condition is vacuous
  have e3 : {c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2)) //
      relatorSubgroup {piRelator} ≤ c.toMonoidHom.ker}
      ≃ (ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2))) :=
    Equiv.subtypeUnivEquiv relatorSubgroup_le_ker
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  exact (Nat.card_congr (((e1.trans e2).trans e3).trans (cmhEquivFun.trans vecEquiv₃))).trans
    (by rw [Nat.card_prod, Nat.card_prod, h2])

/-- **Lemma 8.2, local source**: `|Hom_cont(G_ℚ₂, 𝔽₂)| = 8` (`= |ℚ₂ˣ/(ℚ₂ˣ)²|`).  **Proved**
via the common marked maximal pro-2 quotient: a `BoundaryMaps` witness pins `pro2F` as *the*
maximal pro-2 quotient map (`ker_pro2F`), every `𝔽₂`-character kills the pro-2 kernel
(T-05 `proPKernel_le_ker`), so precomposition with `pro2F` bijects characters of `Π` with
characters of `G_ℚ₂`, and `card_char_piBd` finishes.  [Statement amendment (F-owner): the
`BoundaryMaps` hypothesis and the `CompactSpace`/`TotallyDisconnectedSpace` instance
hypotheses on `AbsGalQ2` (the `main_presentation` house pattern) — without the bundle the
count is B4/B5-content outside the P-16 axiom budget.] -/
theorem lemma_8_2_local (B : BoundaryMaps)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nat.card (ContinuousMonoidHom AbsGalQ2 (Multiplicative (ZMod 2))) = 8 := by
  -- precomposition with `pro2F` is bijective
  have hbij : Function.Bijective
      (fun φ : ContinuousMonoidHom PiBd (Multiplicative (ZMod 2)) => φ.comp B.pro2F) := by
    constructor
    · intro φ₁ φ₂ h
      ext y
      obtain ⟨x, rfl⟩ := B.pro2F_surjective y
      exact DFunLike.congr_fun h x
    · intro c
      -- `c` kills the pro-2 kernel, which is `ker pro2F`
      have hkerc : B.pro2F.toMonoidHom.ker ≤ c.toMonoidHom.ker := by
        rw [B.ker_pro2F]
        exact proPKernel_le_ker isProP_M2 c
      -- descend `pro2F` to a continuous bijection from the canonical pro-2 quotient …
      have hKle : proPKernel 2 AbsGalQ2 ≤ B.pro2F.toMonoidHom.ker := le_of_eq B.ker_pro2F.symm
      set ψ : ContinuousMonoidHom (AbsGalQ2 ⧸ proPKernel 2 AbsGalQ2) PiBd :=
        quotientLift (proPKernel 2 AbsGalQ2) B.pro2F hKle with hψ
      have hψbij : Function.Bijective ψ := by
        constructor
        · rw [injective_iff_map_eq_one]
          intro x hx
          obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) x
          have hx' : B.pro2F g = 1 := hx
          have hg : g ∈ proPKernel 2 AbsGalQ2 := by
            rw [← B.ker_pro2F]
            exact MonoidHom.mem_ker.mpr hx'
          exact (quotientMk_eq_one_iff _).mpr hg
        · intro y
          obtain ⟨x, hx⟩ := B.pro2F_surjective y
          exact ⟨quotientMk _ x, hx⟩
      -- … hence a topological isomorphism (compact source, T2 target)
      set e := continuousMulEquivOfBijective ψ hψbij with he
      -- factor `c` through the canonical quotient (T-05) and transport along `e`
      set c' : ContinuousMonoidHom (maxProPQuotient 2 AbsGalQ2) (Multiplicative (ZMod 2)) :=
        (maxProPHomEquiv isProP_M2).symm c with hc'
      refine ⟨c'.comp ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous_toFun⟩, ?_⟩
      ext x
      show c' (e.symm (B.pro2F x)) = c x
      have h1 : B.pro2F x = e (quotientMk (proPKernel 2 AbsGalQ2) x) := rfl
      rw [h1, ContinuousMulEquiv.symm_apply_apply]
      have h2 : c'.comp (maxProPMk 2 AbsGalQ2) = c :=
        (maxProPHomEquiv isProP_M2).apply_symm_apply c
      exact DFunLike.congr_fun h2 x
  exact (Nat.card_congr (Equiv.ofBijective _ hbij).symm).trans card_char_piBd

/-! ## Lemma 8.3: the eight-lift partition  (display (124))

The proof assembles two fibrations of the **master set** `R = {g : Γ →ₜ* Ỹ // (p∘g).range = J
∧ boundary-framed}`: by *image* `g ↦ g.range` (a `Nat.card_sigma` over subgroups `J' ≤ Ỹ` with
`p(J') = J`, each fibre `≃ BoundaryLifts(stratum J')` by corestriction) — this is the RHS; and
by *projection* `g ↦ p∘g` (each fibre the torsor `≃ Hom_cont(Γ,𝔽₂) = 8` of `fiberLiftEquiv`) —
this is `8 · u^β`.  Needs `Γ` topologically finitely generated (`hfg`), the
`finite_boundaryLifts` shape, to finitize the counted sets. -/

section Lemma83

variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
  (T : MarkedTarget H E Y) (C : CentralCover Y) (J : Subgroup Y)

/-- The master set of Lemma 8.3: cover lifts whose projection has image exactly `J` and is
boundary-framed for `T`.  The two fibrations of this set (by image `g ↦ g.range` and by
projection `g ↦ p∘g`) give the two sides of (124). -/
abbrev masterLifts : Type :=
  {g : ContinuousMonoidHom Γ C.cover //
    (C.pCont.comp g).toMonoidHom.range = J ∧ IsBoundaryLift b F T (C.pCont.comp g)}

variable {b F T C J}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- A subgroup of the cover projecting onto `J` also projects onto `H` — so its pullback
stratum is well-defined. -/
lemma stratum_surj (hJ : Function.Surjective (T.piY.comp J.subtype))
    {J' : Subgroup C.cover} (hJ' : J'.map C.p = J) :
    Function.Surjective ((C.pullTarget T).piY.comp J'.subtype) := by
  intro h
  obtain ⟨y, hy⟩ := hJ h
  have hyJ' : (y : Y) ∈ J'.map C.p := by rw [hJ']; exact y.2
  obtain ⟨x, hxJ', hxy⟩ := Subgroup.mem_map.mp hyJ'
  exact ⟨⟨x, hxJ'⟩, by
    show T.piY (C.p x) = h
    rw [hxy]; exact hy⟩

end Lemma83

theorem lemma_8_3
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) (C : CentralCover Y)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    8 * liftableCount b F T C J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
          exactImageCountOn b F (C.pullTarget T) J' := by
  -- Scaffolding for the O-finish (all landed above): `masterLifts` (the master set `R`),
  -- `stratum_surj`, the corestriction layer (`cmhCodRestrict`/`cmhInclude`/`cmhSubgroupEquiv`),
  -- `pCont`, and the torsor core (`fiberLiftEquiv` etc.).  Remaining: the two `Nat.card_sigma`
  -- fibrations of `R` (by projection → `8·u^β` via `fiberLiftEquiv`; by image → the RHS via
  -- corestriction).  `hfg` finitizes the counted sets (`finite_continuousMonoidHom`).
  classical
  haveI : Finite (ContinuousMonoidHom Γ C.cover) := finite_continuousMonoidHom hfg C.cover
  haveI : Finite (masterLifts b F T C J) := Subtype.finite
  -- membership: `p∘g` lands in `J` for any master lift.
  have hmemJ : ∀ (g : masterLifts b F T C J) (γ : Γ), C.p (g.1 γ) ∈ J := fun g γ => by
    have hmem : (C.pCont.comp g.1).toMonoidHom γ ∈ (C.pCont.comp g.1).toMonoidHom.range := ⟨γ, rfl⟩
    rw [g.2.1] at hmem; exact hmem
  haveI : Finite (BoundaryLifts b F (T.stratum J hJ)) :=
    finite_boundaryLifts b F (T.stratum J hJ) hfg
  set L := {f : BoundaryLifts b F (T.stratum J hJ) //
    ∃ g : ContinuousMonoidHom Γ C.cover, ∀ γ : Γ, C.p (g γ) = (f.1.1 γ : Y)} with hLdef
  haveI : Finite L := Subtype.finite
  haveI : Fintype L := Fintype.ofFinite L
  -- **Projection fibration**: `projB g = ` the corestriction of `p∘g` to `↥J`.
  set projB : masterLifts b F T C J → L := fun g =>
    ⟨⟨⟨cmhCodRestrict (C.pCont.comp g.1) J (hmemJ g), fun y => by
        have hy : (y : Y) ∈ (C.pCont.comp g.1).toMonoidHom.range := by rw [g.2.1]; exact y.2
        obtain ⟨γ, hγ⟩ := hy
        exact ⟨γ, Subtype.ext hγ⟩⟩, g.2.2⟩, g.1, fun γ => rfl⟩ with hprojBdef
  have hfibB : ∀ f : L, Nat.card {g : masterLifts b F T C J // projB g = f}
      = Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) := by
    intro f
    obtain ⟨g₀, hg₀⟩ := f.2
    refine Nat.card_congr (Equiv.trans ?_ (fiberLiftEquiv C g₀).symm)
    refine
      { toFun := fun g => ⟨g.1.1, fun γ => ?_⟩
        invFun := fun g' => ⟨⟨g'.1, ?_, ?_⟩, ?_⟩
        left_inv := fun g => ?_
        right_inv := fun g' => ?_ }
    · -- `projB g.1 = f` ⇒ `C.p (g.1.1 γ) = ↑(f.1.1.1 γ) = C.p (g₀ γ)`
      have h1 : C.p (g.1.1 γ) = (f.1.1.1 γ : Y) :=
        congrArg (fun w : L => (w.1.1.1 γ : Y)) g.2
      rw [h1, ← hg₀]
    · -- range = J for the included lift `g'`
      show (C.pCont.comp g'.1).toMonoidHom.range = J
      apply le_antisymm
      · rintro _ ⟨γ, rfl⟩
        show C.p (g'.1 γ) ∈ J
        rw [g'.2 γ, hg₀]; exact (f.1.1.1 γ).2
      · intro y hy
        obtain ⟨γ, hγ⟩ := f.1.1.2 ⟨y, hy⟩
        refine ⟨γ, ?_⟩
        show C.p (g'.1 γ) = y
        rw [g'.2 γ, hg₀, hγ]
    · -- boundary-framed for the included lift
      have heq : C.pCont.comp g'.1 = C.pCont.comp g₀ := by ext γ; exact g'.2 γ
      rw [heq]
      intro γ
      show (T.piY (C.p (g₀ γ)), T.thetaY (C.p (g₀ γ))) = F.frameMap (b γ)
      rw [hg₀ γ]
      exact f.1.2 γ
    · -- `projB (include g'.1) = f`, from `∀γ, C.p(g'.1 γ) = ↑(f.1.1.1 γ)`
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      ext γ
      show C.p (g'.1 γ) = (f.1.1.1 γ : Y)
      rw [g'.2 γ, hg₀]
    · rfl
    · rfl
  have hB : Nat.card (masterLifts b F T C J) = 8 * liftableCount b F T C J hJ := by
    calc Nat.card (masterLifts b F T C J)
        = Nat.card (Σ f : L, {g : masterLifts b F T C J // projB g = f}) :=
          (Nat.card_congr (Equiv.sigmaFiberEquiv projB)).symm
      _ = ∑ f : L, Nat.card {g : masterLifts b F T C J // projB g = f} := Nat.card_sigma
      _ = ∑ _f : L, 8 := Finset.sum_congr rfl (fun f _ => (hfibB f).trans hscalar)
      _ = 8 * Nat.card L := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
            smul_eq_mul, mul_comm]
  -- **Image fibration** (→ RHS).
  have hrange : ∀ (g : ContinuousMonoidHom Γ C.cover),
      (C.pCont.comp g).toMonoidHom.range = g.toMonoidHom.range.map C.p := by
    intro g
    rw [MonoidHom.range_eq_map, MonoidHom.range_eq_map, Subgroup.map_map]
    rfl
  haveI : Finite (Subgroup C.cover) :=
    Finite.of_injective (fun H : Subgroup C.cover => (H : Set C.cover)) SetLike.coe_injective
  haveI : Fintype (Subgroup C.cover) := Fintype.ofFinite _
  set imageMap : masterLifts b F T C J → {J' : Subgroup C.cover // J'.map C.p = J} :=
    fun g => ⟨g.1.toMonoidHom.range, by rw [← hrange, g.2.1]⟩ with himapdef
  haveI : Fintype {J' : Subgroup C.cover // J'.map C.p = J} := Fintype.ofFinite _
  have hfibA : ∀ J' : {J' : Subgroup C.cover // J'.map C.p = J},
      Nat.card {g : masterLifts b F T C J // imageMap g = J'}
        = exactImageCountOn b F (C.pullTarget T) J'.1 := by
    intro J'
    have hsurj := stratum_surj hJ J'.2
    rw [exactImageCountOn, dif_pos hsurj, exactImageCount]
    apply Nat.card_congr
    refine
      { toFun := fun g => ?_
        invFun := fun gt => ?_
        left_inv := fun g => ?_
        right_inv := fun gt => ?_ }
    · -- forward: corestrict `g.1.1` to `↥J'.1`
      have hrgK : g.1.1.toMonoidHom.range = J'.1 := congrArg Subtype.val g.2
      have hmemK : ∀ γ, g.1.1 γ ∈ J'.1 := fun γ => hrgK ▸ ⟨γ, rfl⟩
      refine ⟨⟨cmhCodRestrict g.1.1 J'.1 hmemK, ?_⟩, ?_⟩
      · -- surjective onto `↥J'.1`
        rintro ⟨y, hy⟩
        rw [← hrgK] at hy
        obtain ⟨γ, hγ⟩ := hy
        exact ⟨γ, Subtype.ext hγ⟩
      · -- boundary-framed for the stratum
        intro γ
        show ((C.pullTarget T).piY (g.1.1 γ), (C.pullTarget T).thetaY (g.1.1 γ)) = F.frameMap (b γ)
        exact g.1.2.2 γ
    · -- backward: include `gt.1.1` back to `C.cover`
      have hsurj_gt : Function.Surjective ⇑gt.1.1.toMonoidHom := gt.1.2
      have hincl : (cmhInclude J'.1 gt.1.1).toMonoidHom.range = J'.1 := by
        show (J'.1.subtype.comp gt.1.1.toMonoidHom).range = J'.1
        rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr hsurj_gt, ← MonoidHom.range_eq_map J'.1.subtype,
          Subgroup.range_subtype]
      refine ⟨⟨cmhInclude J'.1 gt.1.1, ?_, ?_⟩, ?_⟩
      · rw [hrange, hincl]; exact J'.2
      · intro γ
        show (T.piY (C.p (gt.1.1 γ : C.cover)), T.thetaY (C.p (gt.1.1 γ : C.cover)))
          = F.frameMap (b γ)
        exact gt.2 γ
      · exact Subtype.ext hincl
    · apply Subtype.ext; apply Subtype.ext; ext γ; rfl
    · apply Subtype.ext; apply Subtype.ext; ext γ; rfl
  -- assemble the image fibration and convert the sum shape.
  have hsumeq : ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
      exactImageCountOn b F (C.pullTarget T) J'
      = ∑ J' : {J' : Subgroup C.cover // J'.map C.p = J},
          exactImageCountOn b F (C.pullTarget T) J'.1 := by
    have hset : {J' : Subgroup C.cover | J'.map C.p = J}
        = ↑(Finset.univ.filter (fun J' : Subgroup C.cover => J'.map C.p = J)) := by
      ext J'; simp
    rw [hset, finsum_mem_coe_finset]
    exact Finset.sum_subtype _ (fun J' => by simp) _
  rw [hsumeq, ← hB, ← Nat.card_congr (Equiv.sigmaFiberEquiv imageMap), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun J' _ => hfibA J')
/-! ## Lemma 8.6: radical edge and the half-torsor count

The §8 datum: a central double cover of `B` whose restriction to the elementary abelian
`M ◁ B` is a quadratic form (the square map into `⟨z⟩`) with polar radical `T` and vanishing
on `T`.  The `H¹`-valued edge class of (128) is carried **operationally**: the cover
descends to `B/T` iff `p⁻¹(T)` has a normal complement missing `z` (the paper's own descent
clause), and "edge ≠ 0" is the negation. -/

/- `polarMul`, `RadicalCoverData` (+`instNormalM`, `NoDescent`), `two_mul_card_fiber`,
`MLifts`, and `MLifts.Central` moved to `GQ2/RadicalEdgeData.lean` (P-16a def-layer
relocation, 2026-07-04; see `docs/p16-ticket-split.md`). -/

section HalfTorsor

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

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
(degree-one duality = B6).  **Amended (P-16b, 2026-07-05, documented)** with the standing
§8 side conditions, per the `lemma_8_2_local` (compactness) and `lemma_8_3` (`hfg`
topological finite generation, the B1-shaped input) precedents — they finitize the counted
`MLifts`.  Proof: P-16a's central-obstruction engine + the B6 twist of
`GQ2/RadicalEdgeLocal.lean` (`half_torsor_local`).  Ax: B6, B7. -/
theorem lemma_8_6_local (D : RadicalCoverData Bg)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hfg : ∃ s : Finset AbsGalQ2,
      (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  RadicalEdgeLocal.half_torsor_local D hfg hedge ρ hρ

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
`ρ` onto the `C`-target and a boundary-compatible continuous lift `m` into `B` over it that
is `λ`-compatible (lifts through the scalar cover).

**Corrected in the P-16d pass (2026-07-05, deviation documented)**: the original encoding
took the cover-valued lift `g` itself as the pair datum; since the boundary equation of the
pulled-back target only constrains `p_λ ∘ g`, each `λ`-compatible `B`-lift `m` carries
exactly `#Hom(Γ,𝔽₂)` cover lifts (the `z`-scalar twists), so that encoding overcounts the
paper's `Z_{Γ,λ}(B/C)` by the factor `8` and contradicts (139) as displayed.  The corrected
datum is the `B`-lift `m` with the **existence** of a cover lift — matching `m_{Γ,λ}`'s
`∃`-form and the paper's "compatible lifts … without imposing generation". -/
noncomputable def zBC (l : RF.DR) (h : l ≠ RF.zeroDR) : ℕ :=
  Nat.card {pr : BoundaryLifts b F RF.TC × ContinuousMonoidHom Γ RF.YB //
    (∀ γ : Γ, RF.piBC (pr.2 γ) = pr.1.1.1 γ) ∧
      IsBoundaryLift b F RF.TB pr.2 ∧
      ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
        ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = pr.2 γ}

/-- `n_{Γ,0}(ζ)` for a phase cover `C_ζ ↠ C` ((141)/(142)): boundary-framed exact-image
maps onto the `C`-target that lift through the cover. -/
noncomputable def nPhase (Cζ : CentralCover RF.YC) : ℕ :=
  Nat.card {f : BoundaryLifts b F RF.TC //
    ∃ g : ContinuousMonoidHom Γ Cζ.cover, ∀ γ : Γ, Cζ.p (g γ) = f.1.1 γ}

/-- **The `B`-stage projection of a boundary lift** (P-16d, the (136) fibration map):
composing an exact-image boundary lift onto `Y` with `π_B : Y ↠ B`.  Surjectivity is
inherited (`π_B` epi), continuity is free (`Y` discrete), and the boundary equation
transports along the spec fields `TB_head`/`TB_theta`. -/
noncomputable def liftB (f : BoundaryLifts b F T) : BoundaryLifts b F RF.TB :=
  ⟨⟨⟨RF.piB.comp f.1.1.toMonoidHom, by
      have hc : Continuous (⇑RF.piB ∘ ⇑f.1.1) :=
        (continuous_of_discreteTopology (f := ⇑RF.piB)).comp f.1.1.continuous_toFun
      exact hc⟩,
    RF.piB_surj.comp f.1.2⟩,
   fun γ => by
     show (RF.TB.piY (RF.piB (f.1.1 γ)), RF.TB.thetaY (RF.piB (f.1.1 γ))) = F.frameMap (b γ)
     have h1 : RF.TB.piY (RF.piB (f.1.1 γ)) = T.piY (f.1.1 γ) := by
       rw [show RF.TB.piY (RF.piB (f.1.1 γ)) = (RF.TB.piY.comp RF.piB) (f.1.1 γ) from rfl,
         RF.TB_head]
     have h2 : RF.TB.thetaY (RF.piB (f.1.1 γ)) = T.thetaY (f.1.1 γ) := by
       rw [show RF.TB.thetaY (RF.piB (f.1.1 γ))
           = (RF.TB.thetaY.comp RF.piB) (f.1.1 γ) from rfl, RF.TB_theta]
     rw [h1, h2]
     exact f.2 γ⟩

/-! ### The frame-enrichment layer  (P-16d1)

`RecursionFrame` pins the stages and the scalar covers only as bare group data; the
(139)/(140) analyses use more.  First the **derived layer facts** — normality and
elementarity of `M_B`/`T_B`, forced by `ker π_B = R = Φ(K)` — then the `Enrichment`
structure carrying what the frame does not determine: per nonzero `λ`, the square form of
`p_λ` on `M_B` (§7.4; block-level constructibility = `mForm_of_qbar` in
`GQ2/FrameEnrichment.lean`), and the descended module `V ≅ M_B/T_B` over the `C`-stage
with the form `q̄_λ` and its fixed equivariant factor-set datum (`κ⁰_{q̄_λ}`, Lemma 6.1 —
the relative hypothesis of `lemma_6_21`, consumed by Lemma 8.7/Prop 8.8, P-16d4).
`Enrichment.radData` assembles the per-`λ` Lemma 8.6 datum; `radData_noDescent_iff`
aligns its descent clause with the (139)/(140) case split (P-16d3's hand-off to
`lemma_8_6_local`/`_gammaA`). -/

/-- `M_B ◁ B`: image of the normal `K` under the surjection `π_B`. -/
theorem MB_normal : RF.MB.Normal := by
  rw [RF.MB_eq]
  exact Subgroup.Normal.map Blk.hK RF.piB RF.piB_surj

/-- `M_B` has exponent 2: squares of `K` lie in `Φ(K) = ker π_B`. -/
theorem MB_elem : ∀ m ∈ RF.MB, m * m = 1 := by
  intro m hm
  rw [RF.MB_eq] at hm
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
  rw [← map_mul]
  have hkk : k * k ∈ RF.piB.ker := by
    rw [RF.ker_piB]
    exact sq_mem_frattiniLike hk
  exact MonoidHom.mem_ker.mp hkk

/-- `M_B` is abelian: commutators of `K` lie in `Φ(K) = ker π_B`. -/
theorem MB_comm : ∀ m ∈ RF.MB, ∀ m' ∈ RF.MB, m * m' = m' * m := by
  intro m hm m' hm'
  rw [RF.MB_eq] at hm hm'
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hm
  obtain ⟨k', hk', rfl⟩ := Subgroup.mem_map.mp hm'
  have hc : (k' * k)⁻¹ * (k * k') ∈ RF.piB.ker := by
    rw [RF.ker_piB]
    have he : (k' * k)⁻¹ * (k * k') = k⁻¹ * k'⁻¹ * k⁻¹⁻¹ * k'⁻¹⁻¹ := by group
    rw [he]
    exact comm_mem_frattiniLike (inv_mem hk) (inv_mem hk')
  have h1 := MonoidHom.mem_ker.mp hc
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  rw [← map_mul, ← map_mul]
  exact h1.symm

/-- `T_B` is already the `K ∩ S`-image: the `R`-factor of `T₀ = (K∩S)·R` dies in `B`. -/
theorem TBsub_eq_mapKS : RF.TBsub = (Blk.K ⊓ Blk.S).map RF.piB := by
  have h0 : Blk.R.map RF.piB = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
    have hr' : r ∈ RF.piB.ker := by rw [RF.ker_piB]; exact hr
    exact Subgroup.mem_bot.mpr (MonoidHom.mem_ker.mp hr')
  rw [RF.TBsub_eq, Subgroup.map_sup, h0, sup_bot_eq]

/-- `T_B ◁ B`: image of the normal `K ∩ S` under the surjection `π_B`. -/
theorem TBsub_normal : RF.TBsub.Normal := by
  rw [RF.TBsub_eq_mapKS]
  have h1 : (Blk.K ⊓ Blk.S).Normal :=
    ⟨fun n hn g => Subgroup.mem_inf.mpr
      ⟨Blk.hK.conj_mem n (Subgroup.mem_inf.mp hn).1 g,
       Blk.hS.conj_mem n (Subgroup.mem_inf.mp hn).2 g⟩⟩
  exact Subgroup.Normal.map h1 RF.piB RF.piB_surj

/-- `T_B ≤ M_B` (`(K ∩ S) ⊔ R ≤ K`, via `lemma_7_1_head`). -/
theorem TBsub_le_MB : RF.TBsub ≤ RF.MB := by
  rw [RF.TBsub_eq, RF.MB_eq]
  exact blockT_map_le_blockM_map Blk RF.piB

/-- `ker π_{BC} = M_B`: the connecting map `B ↠ C` has the `M`-layer as kernel. -/
theorem ker_piBC : RF.piBC.ker = RF.MB := by
  rw [RF.MB_eq]
  ext bb
  constructor
  · intro hbb
    obtain ⟨y, rfl⟩ := RF.piB_surj bb
    have hy : RF.piC y = 1 := by
      have h1 : RF.piBC (RF.piB y) = 1 := MonoidHom.mem_ker.mp hbb
      rwa [show RF.piBC (RF.piB y) = RF.piC y from by rw [← RF.piBC_comp]; rfl] at h1
    refine ⟨y, ?_, rfl⟩
    have hy' : y ∈ RF.piC.ker := MonoidHom.mem_ker.mpr hy
    rwa [RF.ker_piC] at hy'
  · rintro ⟨k, hk, rfl⟩
    have h1 : RF.piBC (RF.piB k) = RF.piC k := by rw [← RF.piBC_comp]; rfl
    have h2 : RF.piC k = 1 := by
      have hk' : k ∈ RF.piC.ker := by rw [RF.ker_piC]; exact hk
      exact MonoidHom.mem_ker.mp hk'
    exact MonoidHom.mem_ker.mpr (h1.trans h2)

/-- `π_{BC}` is surjective (it covers the surjection `π_C`). -/
theorem piBC_surj : Function.Surjective RF.piBC := by
  have h : Function.Surjective (RF.piBC.comp RF.piB) := by
    rw [RF.piBC_comp]
    exact RF.piC_surj
  rw [MonoidHom.coe_comp] at h
  exact h.of_comp

/-- **The head factors through `π_{BC}`**: `π^C_Y ∘ π_{BC} = π^B_Y` (the spec fields + `π_B`
epi).  Exported for the D5 boundary-framing argument (P-16d4/d6). -/
theorem headBC : RF.TC.piY.comp RF.piBC = RF.TB.piY := by
  have h1 : (RF.TC.piY.comp RF.piBC).comp RF.piB = RF.TB.piY.comp RF.piB := by
    rw [MonoidHom.comp_assoc, RF.piBC_comp, RF.TC_head, RF.TB_head]
  exact (MonoidHom.cancel_right RF.piB_surj).mp h1

/-- **The decoration factors through `π_{BC}`**: `θ^C_Y ∘ π_{BC} = θ^B_Y`. -/
theorem thetaBC : RF.TC.thetaY.comp RF.piBC = RF.TB.thetaY := by
  have h1 : (RF.TC.thetaY.comp RF.piBC).comp RF.piB = RF.TB.thetaY.comp RF.piB := by
    rw [MonoidHom.comp_assoc, RF.piBC_comp, RF.TC_theta, RF.TB_theta]
  exact (MonoidHom.cancel_right RF.piB_surj).mp h1

/-- **Boundary-framing rides free over `ρ`** (P-16d4, D5): a continuous hom into `B` lying
over a boundary-framed `C`-lift `ρ` is itself boundary-framed — both boundary components
factor through `π_{BC}`.  This is why the `IsBoundaryLift` clause of `zBC`'s pairs is
redundant, and no `θ|_T` hypotheses are needed in the count. -/
theorem isBoundaryLift_of_over (f : ContinuousMonoidHom Γ RF.YB)
    (ρ : BoundaryLifts b F RF.TC) (hover : ∀ γ, RF.piBC (f γ) = ρ.1.1 γ) :
    IsBoundaryLift b F RF.TB f := by
  intro γ
  have h1 : RF.TB.piY (f γ) = RF.TC.piY (ρ.1.1 γ) := by
    rw [← hover, show RF.TC.piY (RF.piBC (f γ)) = (RF.TC.piY.comp RF.piBC) (f γ) from rfl,
      RF.headBC]
  have h2 : RF.TB.thetaY (f γ) = RF.TC.thetaY (ρ.1.1 γ) := by
    rw [← hover, show RF.TC.thetaY (RF.piBC (f γ)) = (RF.TC.thetaY.comp RF.piBC) (f γ) from rfl,
      RF.thetaBC]
  rw [h1, h2]
  exact ρ.2 γ

/-- **The frame enrichment** (P-16d1): the per-`λ` data of the §8 analyses that the bare
frame does not determine.  Square-form block: the form `q_λ` of the scalar cover on `M_B`
(cover square relation, `T_B` in the polar radical, vanishing on `T_B`) — with the derived
layer facts above, exactly a per-`λ` Lemma 8.6 datum (`radData`); §7.4 supplies it for the
concrete block (`mForm_of_qbar`).  Descended block: the module `V ≅ M_B/T_B` over the
`C`-stage with the descended form `q̄_λ` (quadratic, nonsingular, invariant — Prop 7.4's
output) and a **fixed equivariant factor-set datum** for it (Lemma 6.1's `κ⁰_{q̄_λ}` — the
relative hypothesis of `lemma_6_21`, consumed by Lemma 8.7/Prop 8.8). -/
structure Enrichment where
  /-- The square form of the scalar cover `p_λ` on `M_B`. -/
  q : (l : RF.DR) → l ≠ RF.zeroDR → ↥RF.MB → ZMod 2
  /-- The cover square relation: `x̃² = z^{q_λ(x)}` over `M_B`. -/
  hq : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (x : (RF.scalarCover l h).cover)
    (hx : (RF.scalarCover l h).p x ∈ RF.MB),
    x * x = (RF.scalarCover l h).z ^ (q l h ⟨(RF.scalarCover l h).p x, hx⟩).val
  /-- `T_B` lies in the polar radical of `q_λ`. -/
  hrad : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (t : RF.YB) (ht : t ∈ RF.TBsub)
    (m : RF.YB) (hm : m ∈ RF.MB),
    polarMul (q l h) (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩)
      ⟨t, RF.TBsub_le_MB ht⟩ ⟨m, hm⟩ = 0
  /-- `q_λ` vanishes on `T_B`. -/
  hTzero : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (t : RF.YB) (ht : t ∈ RF.TBsub),
    q l h ⟨t, RF.TBsub_le_MB ht⟩ = 0
  /-- The descended module `V ≅ M_B/T_B` (abstract carrier; the concrete frame will take
  Prop 7.4's `P/S`-side model, where `q̄_λ` already lives). -/
  Vmod : Type
  [addV : AddCommGroup Vmod]
  [finV : Finite Vmod]
  /-- The `C`-stage action (conjugation, descended through `ker π_{BC} = M_B`). -/
  [actV : DistribMulAction RF.YC Vmod]
  /-- The descent surjection `M_B ↠ V`. -/
  descend : ↥RF.MB →* Multiplicative Vmod
  descend_surj : Function.Surjective descend
  /-- `ker(descend) = T_B`. -/
  descend_ker : ∀ m : ↥RF.MB, descend m = 1 ↔ (m : RF.YB) ∈ RF.TBsub
  /-- `descend` intertwines `B`-conjugation with the action through `π_{BC}`. -/
  descend_conj : ∀ (bb : RF.YB) (m : ↥RF.MB) (hm : bb * ↑m * bb⁻¹ ∈ RF.MB),
    descend ⟨bb * ↑m * bb⁻¹, hm⟩
      = Multiplicative.ofAdd (RF.piBC bb • Multiplicative.toAdd (descend m))
  /-- The descended form `q̄_λ` on `V`. -/
  qbar : (l : RF.DR) → l ≠ RF.zeroDR → Vmod → ZMod 2
  /-- `q_λ = q̄_λ ∘ descend`. -/
  hqbar : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (m : ↥RF.MB),
    q l h m = qbar l h (Multiplicative.toAdd (descend m))
  /-- `q̄_λ` is quadratic (polar form biadditive). -/
  hquad : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), QuadraticFp2.IsQuadraticFp2 (qbar l h)
  /-- `q̄_λ` is nonsingular on `V` (Prop 7.4's nondegeneracy). -/
  hns : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), QuadraticFp2.Nonsingular (qbar l h)
  /-- `q̄_λ` is `C`-invariant (Prop 7.4's `Y`-invariance, descended). -/
  hinv : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), QuadraticFp2.IsInvariant RF.YC (qbar l h)
  /-- The fixed equivariant factor-set datum for `q̄_λ` (Lemma 6.1's base class). -/
  dat : (l : RF.DR) → l ≠ RF.zeroDR → FactorSet RF.YC Vmod
  /-- … satisfying Lemma 6.1's identities for `q̄_λ`. -/
  hdat : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR), IsEquivariantFactorSet (qbar l h) (dat l h)

attribute [instance] Enrichment.addV Enrichment.finV Enrichment.actV

variable {RF}

/-- The per-`λ` **Lemma 8.6 datum** assembled from the enrichment: cover `p_λ`, layers
`M_B`/`T_B`, with normality and elementarity derived from the frame and the block. -/
def Enrichment.radData (E : RF.Enrichment) (l : RF.DR) (h : l ≠ RF.zeroDR) :
    RadicalCoverData RF.YB where
  C := RF.scalarCover l h
  M := RF.MB
  hM := RF.MB_normal
  T := RF.TBsub
  hT := RF.TBsub_normal
  hTM := RF.TBsub_le_MB
  helem := RF.MB_elem
  hcomm := RF.MB_comm
  q := E.q l h
  hq := E.hq l h
  hrad := E.hrad l h
  hTzero := E.hTzero l h

/-- The descent clause of the assembled datum **is** the (139)/(140) case-split condition:
definitional alignment for the P-16d3 hand-off to `lemma_8_6_local`/`lemma_8_6_gammaA`. -/
theorem Enrichment.radData_noDescent_iff (E : RF.Enrichment) (l : RF.DR)
    (h : l ≠ RF.zeroDR) :
    (E.radData l h).NoDescent ↔
      ¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N :=
  Iff.rfl

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
  /-- **(137)**, additively: `Z_{Γ,λ}(B/C) = m_{Γ,λ}(B) + Σ_{J < B, J ↠ C} m_{Γ,λ}(J)` (the
  exact-image subtraction; strata missing the `H`-head contribute `0` through the
  totalized `mJOn`).  **Index set corrected in the P-16d pass (2026-07-05)**: the paper's
  sum runs over the proper strata **surjecting onto `C`** (`J ↠ C`) — the `C`-level
  component of a `Z`-pair forces the image stratum onto `C`, and proper `C`-missing strata
  can carry nonzero `m_{Γ,λ}(J)`, so the unrestricted sum would overcount. -/
  eq137 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (RF.zBC b F l h : ℤ) = RF.mB b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (RF.mJOn b F l h J : ℤ)
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

open scoped Classical in
/-- **The (137) partition** (P-16d item 2): the `partition137` input of `RecursionInputs`,
derived outright.  A `Z`-pair is determined by its `B`-level lift `m` (the `C`-component is
`π_{BC} ∘ m`); stratifying by the exact image `J = im m` gives the top stratum (`m_B`, at
`J = ⊤`) plus the proper `C`-onto strata (`m_J`, via the corestriction equivalence), while
`C`-missing strata are empty (the pair's `C`-component is onto) and head-missing strata are
empty by the boundary-frame head surjectivity `hhead` — matching `mJOn`'s zero branch. -/
theorem partition137_of {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    (RF.zBC b F l h : ℤ) = RF.mB b F l
      + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
          (RF.mJOn b F l h J : ℤ) := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLifts b F RF.TB) := finite_boundaryLifts b F RF.TB hfg
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Finite (Subgroup RF.YB) :=
    Finite.of_injective (fun J : Subgroup RF.YB => (J : Set RF.YB)) SetLike.coe_injective
  haveI : Fintype (Subgroup RF.YB) := Fintype.ofFinite _
  -- head/theta transport `TC ∘ π_BC = TB` (frame specs + `π_B` epi)
  have hpiBC_surj : Function.Surjective RF.piBC := by
    intro c
    obtain ⟨y, hy⟩ := RF.piC_surj c
    exact ⟨RF.piB y, by rw [show RF.piBC (RF.piB y) = (RF.piBC.comp RF.piB) y from rfl,
      RF.piBC_comp, hy]⟩
  have hheadBC : RF.TC.piY.comp RF.piBC = RF.TB.piY := RF.headBC
  have hthetaBC : RF.TC.thetaY.comp RF.piBC = RF.TB.thetaY := RF.thetaBC
  -- ===== Step 1: eliminate the pair — `Z` is a set of `B`-level lifts =====
  have e1 : RF.zBC b F l h = Nat.card {m : ContinuousMonoidHom Γ RF.YB //
      (IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)) ∧
        ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
          ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = m γ} := by
    refine Nat.card_congr ⟨fun pr => ⟨pr.1.2, ⟨pr.2.2.1, ?_⟩, pr.2.2.2⟩,
      fun m => ⟨(⟨⟨⟨RF.piBC.comp m.1.toMonoidHom, by
          have hc : Continuous (⇑RF.piBC ∘ ⇑m.1) :=
            (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp m.1.continuous_toFun
          exact hc⟩, m.2.1.2⟩,
        fun γ => by
          show (RF.TC.piY (RF.piBC (m.1 γ)), RF.TC.thetaY (RF.piBC (m.1 γ)))
            = F.frameMap (b γ)
          have h1 : RF.TC.piY (RF.piBC (m.1 γ)) = RF.TB.piY (m.1 γ) := by
            rw [show RF.TC.piY (RF.piBC (m.1 γ))
                = (RF.TC.piY.comp RF.piBC) (m.1 γ) from rfl, hheadBC]
          have h2 : RF.TC.thetaY (RF.piBC (m.1 γ)) = RF.TB.thetaY (m.1 γ) := by
            rw [show RF.TC.thetaY (RF.piBC (m.1 γ))
                = (RF.TC.thetaY.comp RF.piBC) (m.1 γ) from rfl, hthetaBC]
          rw [h1, h2]
          exact m.2.1.1 γ⟩, m.1), fun γ => rfl, m.2.1.1, m.2.2⟩,
      fun pr => ?_, fun m => ?_⟩
    · have hfun : ⇑RF.piBC ∘ ⇑pr.1.2 = ⇑pr.1.1.1.1 := funext fun γ => pr.2.1 γ
      rw [hfun]
      exact pr.1.1.1.2
    · obtain ⟨⟨f, m⟩, hcompat, hbd, hg⟩ := pr
      refine Subtype.ext (Prod.ext ?_ rfl)
      refine Subtype.ext (Subtype.ext ?_)
      apply ContinuousMonoidHom.ext
      intro γ
      exact hcompat γ
    · exact Subtype.ext rfl
  set Mset := {m : ContinuousMonoidHom Γ RF.YB //
    (IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)) ∧
      ∃ g : ContinuousMonoidHom Γ (RF.scalarCover l h).cover,
        ∀ γ : Γ, (RF.scalarCover l h).p (g γ) = m γ} with hMsetdef
  haveI : Finite Mset := Subtype.finite
  -- ===== Step 2: stratify by the exact image =====
  have e2 : Nat.card Mset
      = ∑ J : Subgroup RF.YB, Nat.card {m : Mset // m.1.toMonoidHom.range = J} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun m : Mset => m.1.toMonoidHom.range)).symm, Nat.card_sigma]
  -- ===== Step 3: the fibres =====
  -- range of the composite with `π_BC`
  have hrangeBC : ∀ m : Mset, (RF.piBC.comp m.1.toMonoidHom).range
      = m.1.toMonoidHom.range.map RF.piBC := fun m => MonoidHom.range_comp _ _
  -- the top stratum is `m_B`
  have htop : Nat.card {m : Mset // m.1.toMonoidHom.range = ⊤} = RF.mB b F l := by
    rw [RecursionFrame.mB, dif_neg h]
    refine Nat.card_congr ⟨fun m => ⟨⟨⟨m.1.1, fun y => ?_⟩, m.1.2.1.1⟩, m.1.2.2⟩,
      fun f => ⟨⟨f.1.1.1, ⟨f.1.2, hpiBC_surj.comp f.1.1.2⟩, f.2⟩, ?_⟩,
      fun m => Subtype.ext (Subtype.ext rfl),
      fun f => Subtype.ext (Subtype.ext (Subtype.ext rfl))⟩
    · have hy : y ∈ m.1.1.toMonoidHom.range := by rw [m.2]; trivial
      exact hy
    · rw [MonoidHom.range_eq_top]
      exact f.1.1.2
  -- proper `C`-onto head-surjective strata are `m_J`
  have hstr : ∀ (J : Subgroup RF.YB) (hJc : J.map RF.piBC = ⊤)
      (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)),
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = RF.mJ b F l h J hJh := by
    intro J hJc hJh
    rw [RecursionFrame.mJ, liftableCount]
    have hmem : ∀ (m : Mset), m.1.toMonoidHom.range = J → ∀ γ, m.1 γ ∈ J := by
      intro m hm γ
      have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
      rwa [hm] at this
    refine Nat.card_congr ⟨fun m =>
      ⟨⟨⟨cmhCodRestrict m.1.1 J (hmem m.1 m.2), fun j => ?_⟩, fun γ => ?_⟩, ?_⟩,
      fun f => ⟨⟨cmhInclude J f.1.1.1, ⟨fun γ => f.1.2 γ, ?_⟩, ?_⟩, ?_⟩,
      fun m => Subtype.ext (Subtype.ext rfl),
      fun f => Subtype.ext (Subtype.ext (Subtype.ext (by
        apply ContinuousMonoidHom.ext
        intro γ
        exact Subtype.ext rfl)))⟩
    · -- corestriction surjective onto `↥J`
      have hj : (j : RF.YB) ∈ m.1.1.toMonoidHom.range := by rw [m.2]; exact j.2
      obtain ⟨γ, hγ⟩ := hj
      exact ⟨γ, Subtype.ext hγ⟩
    · -- stratum boundary equation (definitional transport)
      exact m.1.2.1.1 γ
    · -- the ∃g condition transports
      obtain ⟨g, hg⟩ := m.1.2.2
      exact ⟨g, fun γ => hg γ⟩
    · -- `C`-surjectivity of the included map, from `J ↠ C`
      intro c
      have hc : c ∈ J.map RF.piBC := by rw [hJc]; trivial
      obtain ⟨y, hyJ, hyc⟩ := Subgroup.mem_map.mp hc
      obtain ⟨γ, hγ⟩ := f.1.1.2 ⟨y, hyJ⟩
      exact ⟨γ, by
        show RF.piBC ((f.1.1.1 γ : RF.YB)) = c
        rw [hγ, hyc]⟩
    · -- the ∃g condition transports back
      obtain ⟨g, hg⟩ := f.2
      exact ⟨g, fun γ => hg γ⟩
    · -- the included map has range exactly `J`
      have h1 : (cmhInclude J f.1.1.1).toMonoidHom.range
          = f.1.1.1.toMonoidHom.range.map J.subtype := MonoidHom.range_comp _ _
      rw [h1, MonoidHom.range_eq_top.mpr f.1.1.2, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
  -- `C`-missing strata are empty
  have hemptyC : ∀ (J : Subgroup RF.YB), J.map RF.piBC ≠ ⊤ →
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = 0 := by
    intro J hJc
    have hE : IsEmpty {m : Mset // m.1.toMonoidHom.range = J} := by
      constructor
      rintro ⟨m, hm⟩
      apply hJc
      rw [← hm, ← MonoidHom.range_comp]
      rw [MonoidHom.range_eq_top]
      intro c
      obtain ⟨γ, hγ⟩ := m.2.1.2 c
      exact ⟨γ, hγ⟩
    exact Nat.card_of_isEmpty
  -- head-missing strata are empty (via `hhead`)
  have hemptyH : ∀ (J : Subgroup RF.YB),
      ¬ Function.Surjective (RF.TB.piY.comp J.subtype) →
      Nat.card {m : Mset // m.1.toMonoidHom.range = J} = 0 := by
    intro J hJh
    have hE : IsEmpty {m : Mset // m.1.toMonoidHom.range = J} := by
      constructor
      rintro ⟨m, hm⟩
      apply hJh
      intro hh
      obtain ⟨γ, hγ⟩ := hhead hh
      have hmemJ : m.1 γ ∈ J := by
        have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
        rwa [hm] at this
      refine ⟨⟨m.1 γ, hmemJ⟩, ?_⟩
      show RF.TB.piY (m.1 γ) = hh
      have hbd := m.2.1.1 γ
      have := congrArg Prod.fst hbd
      simpa [hγ] using this
    exact Nat.card_of_isEmpty
  -- ===== Step 4: assemble =====
  set fib : Subgroup RF.YB → ℕ :=
    fun J => Nat.card {m : Mset // m.1.toMonoidHom.range = J} with hfibdef
  set S : Finset (Subgroup RF.YB) :=
    ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤).filter
      (fun J => J.map RF.piBC = ⊤) with hSdef
  have hsplit : ∑ J : Subgroup RF.YB, fib J
      = fib ⊤ + ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J := by
    rw [add_comm, Finset.sum_erase_add _ _ (Finset.mem_univ ⊤)]
  have hrest : ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J
      = ∑ J ∈ S, fib J := by
    rw [hSdef,
      ← Finset.sum_filter_add_sum_filter_not
        ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤)
        (fun J => J.map RF.piBC = ⊤) fib]
    have hz : ∑ J ∈ ((Finset.univ : Finset (Subgroup RF.YB)).erase ⊤).filter
          (fun J => ¬ J.map RF.piBC = ⊤), fib J = 0 := by
      refine Finset.sum_eq_zero fun J hJ => ?_
      exact hemptyC J (Finset.mem_filter.mp hJ).2
    rw [hz, add_zero]
  have hmatch : ∀ J ∈ S, fib J = RF.mJOn b F l h J := by
    intro J hJ
    rw [hSdef] at hJ
    obtain ⟨hJne, hJc⟩ := Finset.mem_filter.mp hJ
    rw [RecursionFrame.mJOn]
    by_cases hJh : Function.Surjective (RF.TB.piY.comp J.subtype)
    · rw [dif_pos hJh]
      exact hstr J hJc hJh
    · rw [dif_neg hJh]
      exact hemptyH J hJh
  -- convert the RHS finsum to the same Finset sum
  have hsetconv : {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤} = ↑S := by
    rw [hSdef]
    ext J
    simp [Finset.mem_erase, and_comm]
  have hfinsum : ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
        (RF.mJOn b F l h J : ℤ)
      = ∑ J ∈ S, (RF.mJOn b F l h J : ℤ) := by
    rw [hsetconv, finsum_mem_coe_finset]
  -- the `ℕ`-level identity
  have hnat : RF.zBC b F l h = RF.mB b F l + ∑ J ∈ S, RF.mJOn b F l h J := by
    calc RF.zBC b F l h = Nat.card Mset := e1
      _ = ∑ J : Subgroup RF.YB, fib J := e2
      _ = fib ⊤ + ∑ J ∈ (Finset.univ : Finset (Subgroup RF.YB)).erase ⊤, fib J := hsplit
      _ = RF.mB b F l + ∑ J ∈ S, fib J := by
          have htop' : fib ⊤ = RF.mB b F l := htop
          rw [htop', hrest]
      _ = RF.mB b F l + ∑ J ∈ S, RF.mJOn b F l h J := by
          rw [Finset.sum_congr rfl hmatch]
  -- final computation over `ℤ`
  rw [hfinsum, hnat]
  push_cast
  ring

open scoped Classical in
/-- **The source-side input bundle of the Prop 8.9 assembly** (P-16d skeleton).  Each field
is one gated derivation of the boxed recursion, with its intended supplier recorded; the
displays **(137) and (138) are *not* inputs** — `prop_8_9_aux` discharges them from the
proved `partition137_of` and `lemma_8_3`.

* `stageR136` — the final `R`-lifting stage: Fourier inversion (125)/`lemma_8_4` over `D_R`,
  the `z_R` torsor multiplicity (5.15/5.16 numerics at the abelian `R`), and the automatic
  surjectivity of `R`-lifts (`GQ2.eq_top_of_map_frattini_quotient_top`, proved).
* `half139` — the nonzero-edge half count: the `zBC ↔ MLifts` fibration bridge composed with
  the half-torsor Lemma 8.6 (`lemma_8_6_local` **proved** for the `G_ℚ₂` source;
  `lemma_8_6_gammaA` = P-16c, gated on P-13f).
* `phase140` — the zero-edge constrained-Gauss value: the descended `V ⋊ C` splitting
  (`lemma_6_21`, proved), Lemma 8.7's affine `T`-lifting, the completed-square identity
  (135)/Prop 8.8, and `lemma_8_5`, summed over lower exact-image maps. -/
structure RecursionInputs {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : DT → CentralCover RF.YC) : Prop where
  /-- The (136)-stage identity (gated: `lemma_8_4` + `z_R` numerics + Frattini lift
  surjectivity). -/
  stageR136 : (Nat.card RF.DR : ℤ) * exactImageCount b F T
    = RF.zR * ∑ᶠ l : RF.DR,
        (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB)
  /-- The (139) half count (gated: the `zBC` bridge + the source's Lemma 8.6). -/
  half139 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (¬∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * RF.zBC b F l h = (Nat.card ↥RF.MB) ^ 2 * exactImageCount b F RF.TC
  /-- The (140) constrained-Gauss value (gated: 8.5 + 8.7 + (135)/8.8 + 6.21/6.22 chain). -/
  phase140 : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR),
    (∃ N : Subgroup (RF.scalarCover l h).cover, N.Normal ∧
        N.map (RF.scalarCover l h).p = RF.TBsub ∧ (RF.scalarCover l h).z ∉ N) →
      2 * (Nat.card DT : ℤ) * RF.zBC b F l h
        = μ * ((Nat.card ↥RF.MB / Nat.card ↥RF.TBsub : ℕ) * exactImageCount b F RF.TC
            + G0 * ∑ᶠ ζ : DT,
                (2 * (RF.nPhase b F (phase ζ) : ℤ) - exactImageCount b F RF.TC))

open scoped Classical in
/-- **The Prop 8.9 assembly step** (P-16d): given the source-side input bundle, the boxed
system holds — with **(138) discharged from the proved `lemma_8_3`** (the eight-lift
partition, instantiated at each scalar cover `p_λ` over the `B`-stage target).  The
side conditions (`Γ` profinite + t.f.g. `hfg`, `#Hom(Γ,𝔽₂) = 8`) are exactly `lemma_8_3`'s;
both real sources satisfy them (`lemma_8_2` and the boundary-frame data). -/
theorem prop_8_9_aux {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT] (phase : DT → CentralCover RF.YC)
    (inp : RecursionInputs RF b F μ G0 DT phase) :
    ClosedRecursion RF b F μ G0 DT phase where
  eq136 := inp.stageR136
  eq137 := fun l h => partition137_of RF hfg b F hhead l h
  eq138 := fun l h J hJ =>
    lemma_8_3 hfg b F RF.TB (RF.scalarCover l h) hscalar J hJ
  eq139 := inp.half139
  eq140 := inp.phase140

open scoped Classical in
/-- **The (136) stage, combinatorial core** (P-16d item 1): the `stageR136` input of
`RecursionInputs` follows from an **obstruction-module datum** for the `R`-stage.  Given

* an `𝔽₂`-module `W` with an obstruction map `o` on the `B`-stage lifts whose vanishing
  detects liftability to `Y` (`hobs`),
* an identification `e : D_R ≃ W^∨` with `e 0 = 0` matching the scalar-pushout counts
  (`hmB` — "`λ_* o = 0` iff the lift factors through the `λ`-cover"), and
* the constant fibre size `z_R` over liftable points (`hfib` — the `R`-lift torsor count;
  its nonempty-fibre surjectivity onto `Y` is `GQ2.eq_top_of_map_frattini_quotient_top`),

the display (136) follows by the `liftB`-fibration and the Fourier engine `lemma_8_4`.
The three inputs are the analytic residue of the stage: `W`/`o`/`e` come from the concrete
`R`-stage obstruction theory, `hfib` from the 5.15/5.16 `Z¹`-numerics of the source
interface. -/
theorem stageR136_of {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (W : Type) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (o : BoundaryLifts b F RF.TB → W)
    (e : RF.DR ≃ Module.Dual (ZMod 2) W)
    (he0 : e RF.zeroDR = 0)
    (hmB : ∀ (l : RF.DR), l ≠ RF.zeroDR →
      RF.mB b F l = Nat.card {g : BoundaryLifts b F RF.TB // e l (o g) = 0})
    (hobs : ∀ g : BoundaryLifts b F RF.TB,
      o g = 0 ↔ ∃ f : BoundaryLifts b F T, RF.liftB b F f = g)
    (hfib : ∀ g : BoundaryLifts b F RF.TB, o g = 0 →
      Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} = RF.zR) :
    (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = RF.zR * ∑ᶠ l : RF.DR,
          (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
  classical
  haveI : Finite (BoundaryLifts b F T) := finite_boundaryLifts b F T hfg
  haveI : Finite (BoundaryLifts b F RF.TB) := finite_boundaryLifts b F RF.TB hfg
  haveI : Fintype (BoundaryLifts b F RF.TB) := Fintype.ofFinite _
  -- Step 1 (fibration): `e_Γ(Y) = z_R · #{o = 0}`.
  have h1 : exactImageCount b F T
      = RF.zR * Nat.card {g : BoundaryLifts b F RF.TB // o g = 0} := by
    have hsig : exactImageCount b F T
        = ∑ g : BoundaryLifts b F RF.TB,
            Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g} := by
      rw [exactImageCount,
        Nat.card_congr (Equiv.sigmaFiberEquiv (RF.liftB b F)).symm, Nat.card_sigma]
    rw [hsig]
    have hterm : ∀ g : BoundaryLifts b F RF.TB,
        Nat.card {f : BoundaryLifts b F T // RF.liftB b F f = g}
          = if o g = 0 then RF.zR else 0 := by
      intro g
      by_cases hg : o g = 0
      · rw [if_pos hg]
        exact hfib g hg
      · rw [if_neg hg]
        have hempty : IsEmpty {f : BoundaryLifts b F T // RF.liftB b F f = g} := by
          constructor
          rintro ⟨f, hf⟩
          exact hg ((hobs g).mpr ⟨f, hf⟩)
        exact Nat.card_of_isEmpty
    rw [Finset.sum_congr rfl (fun g _ => hterm g), Finset.sum_ite, Finset.sum_const,
      Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  -- Step 2 (Fourier): `lemma_8_4` at the obstruction map.
  have h2 := lemma_8_4 (X := BoundaryLifts b F RF.TB) (W := W) o
  haveI : Finite (Module.Dual (ZMod 2) W) :=
    Finite.of_injective (fun φ : Module.Dual (ZMod 2) W => (φ : W → ZMod 2))
      DFunLike.coe_injective
  haveI : Fintype (Module.Dual (ZMod 2) W) := Fintype.ofFinite _
  -- Step 3 (reindex the character sum along `e`, matching `m_B`).
  have h3 : ∑ᶠ φ : Module.Dual (ZMod 2) W,
        (2 * (Nat.card {g : BoundaryLifts b F RF.TB // φ (o g) = 0} : ℤ)
          - Nat.card (BoundaryLifts b F RF.TB))
      = ∑ᶠ l : RF.DR, (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
      ← Equiv.sum_comp e (fun φ =>
        2 * (Nat.card {g : BoundaryLifts b F RF.TB // φ (o g) = 0} : ℤ)
          - Nat.card (BoundaryLifts b F RF.TB))]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l = RF.zeroDR
    · subst hl
      rw [he0]
      have hall : Nat.card {g : BoundaryLifts b F RF.TB //
          (0 : Module.Dual (ZMod 2) W) (o g) = 0} = Nat.card (BoundaryLifts b F RF.TB) := by
        refine Nat.card_congr (Equiv.subtypeUnivEquiv fun g => ?_)
        simp
      have hmB0 : RF.mB b F RF.zeroDR = exactImageCount b F RF.TB := by
        rw [RecursionFrame.mB, dif_pos rfl]
      rw [hall, hmB0, exactImageCount]
    · rw [hmB l hl]
      rfl
  -- Assemble in `ℤ`.
  have hcardDR : (Nat.card RF.DR : ℤ) = Nat.card (Module.Dual (ZMod 2) W) := by
    exact_mod_cast congrArg (Nat.cast (R := ℤ)) (Nat.card_congr e)
  calc (Nat.card RF.DR : ℤ) * exactImageCount b F T
      = (Nat.card RF.DR : ℤ)
        * (RF.zR * Nat.card {g : BoundaryLifts b F RF.TB // o g = 0}) := by
        rw [h1]; push_cast; ring
    _ = RF.zR * ((Nat.card (Module.Dual (ZMod 2) W) : ℤ)
        * Nat.card {g : BoundaryLifts b F RF.TB // o g = 0}) := by
        rw [← hcardDR]; ring
    _ = RF.zR * ∑ᶠ φ : Module.Dual (ZMod 2) W,
          (2 * (Nat.card {g : BoundaryLifts b F RF.TB // φ (o g) = 0} : ℤ)
            - Nat.card (BoundaryLifts b F RF.TB)) := by
        rw [h2]
    _ = RF.zR * ∑ᶠ l : RF.DR, (2 * (RF.mB b F l : ℤ) - exactImageCount b F RF.TB) := by
        rw [h3]

/-- **Proposition 8.9 (closed exact-image recursion)**: for every boundary-framed target
with a §7 simple-head block and every recursion frame on it, there are **shared** data
`(μ, G⁰, D_T, phase)` — the paper pins them via 5.15/5.16, Prop 7.4, and (133)/(134) —
such that the boxed system (136)–(142) holds for **both sources**.  Every count on the
right sides concerns a target with strictly smaller marked 2-kernel, so the system is a
closed deterministic recursion (paper, end of §8).  [P-16 statement; proof = O-half,
axioms ≤ {B6, B7, B9} per App. D.]

**Amended (P-16d1, 2026-07-05, documented)** with the frame enrichment `En`: the bare
frame's `scalarCover` is an arbitrary central cover, but the paper's (139)/(140) hold under
its §7.4/§6.1 standing data — the square form of `p_λ` on `M_B` with radical `T_B`, and the
fixed equivariant base class `κ⁰_{q̄_λ}` for the descended module (the `lemma_6_21` relative
hypothesis).  Without `En` the statement quantifies over junk covers for which (139) fails.
Deviation ledger: `docs/section8-extraction.md` (P-16d statement corrections). -/
theorem prop_8_9 (B : BoundaryMaps) {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    (En : RF.Enrichment) (F : BoundaryFrame H E) :
    ∃ (μ : ℕ) (G0 : ℤ) (DT : Type) (_ : Fintype DT)
      (phase : DT → CentralCover RF.YC),
      ClosedRecursion RF B.bA F μ G0 DT phase ∧
        ClosedRecursion RF B.bF F μ G0 DT phase := by
  sorry

end Recursion

end SectionEight

end GQ2
