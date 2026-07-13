import GQ2.FoxHeisenberg.Heisenberg

/-!
# Prop 5.8 / 5.10 and the duality package (5.11–5.15)

Split off from `GQ2.FoxHeisenberg`, building on `GQ2.FoxHeisenberg.Heisenberg`.  This file
provides:

* **Prop 5.8 / Prop 5.10**: the traced mixed central coordinate `mixedB t x y = β_t + β_w` and the
  traced Stokes identities that are the Fox–Heisenberg chain map (`section Traced`);
* the **duality package** `IsSelfDual` and the statements of Lemmas 5.11, 5.12, 5.13 and 5.15
  (`section Duality`);
* **Lemma 5.2**, the exact class-two identity of the §5.1 ledger (`section ClassTwo`).

See `GQ2.FoxHeisenberg` for the umbrella module docstring.
-/

namespace GQ2

namespace FoxH

/-! ## Prop 5.8 / Prop 5.10: the traced Stokes identities = the chain map -/

section Traced

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The degree-0 endpoint component `D⁰(a) = (a, a)` of the Fox–Heisenberg chain map
(display (43)). -/
def traceD0 {A : Type*} [AddCommGroup A] : A →+ A × A :=
  AddMonoidHom.mk' (fun a => (a, a)) fun _ _ => rfl

/-- The degree-2 endpoint component `D²(u_t, u_w) = u_t + u_w` (display (45), the scalar
trace). -/
def traceD2 {A : Type*} [AddCommGroup A] : A × A →+ A :=
  AddMonoidHom.mk' (fun p => p.1 + p.2) fun p q => by
    simp only [Prod.fst_add, Prod.snd_add]
    abel

/-! ### The tame relator-word bridge (Lemma 5.7 ⇒ the tame row of Prop 5.8)

`heisMarking`/`liftMarking` evaluate the paper's relators *directly in the target*; `stokesEval`
evaluates the *free* relator word.  They agree because both are the pushforward of the free
marking `⟨g₀,g₁,g₂,g₃⟩` on `Fin 4` along the classifying hom, and `Marking.map_tameValue` is
natural.  Since the tame word carries no `ω₂`, no finiteness is needed — so `bridge_tame` is
unconditional, and feeding it into Lemma 5.7 computes the tame relator's `z`-coordinate at `d⁰a`
in closed form (the tame row of display (41)).

The **wild** row is genuinely harder: `Marking.map_wildValue` needs the source finite, but the
universal source `FreeGroup (Fin 4)` is infinite (and `freeMarking.wildValue`'s `ω₂`-powers are
degenerate there).  The wild bridge therefore needs the target-dependent integer-`ω₂`
representative of the wild word — the separate "wild-row" computation. -/

/-- The four marked values `⟨t.σ, t.τ, t.x₀, t.x₁⟩` as a vector — the lower map of `stokesEval`. -/
def markVec (t : Marking C) : Fin 4 → C := ![t.σ, t.τ, t.x₀, t.x₁]

/-- The free marking `⟨g₀, g₁, g₂, g₃⟩` on `FreeGroup (Fin 4)` (the universal source). -/
def freeMarking : Marking (FreeGroup (Fin 4)) :=
  ⟨FreeGroup.of 0, FreeGroup.of 1, FreeGroup.of 2, FreeGroup.of 3⟩

@[simp] theorem freeMarking_tameValue : freeMarking.tameValue = fgTame := rfl

/-- The wild relator word with the `ω₂`-powers replaced by an explicit integer exponent `e` (the
paper's `ω₂` becomes `(·)^e` for a concrete `e = omega2Exp N`, a multiple of the relevant orders).
Mirrors `Marking.wildValue`'s ledger exactly; only `sigma2`, `u0`, `u1` carry the exponent. -/
def wildValueExp {G : Type*} [Group G] (t : Marking G) (e : ℕ) : G :=
  let sigma2 := t.σ ^ e
  let u0 := (t.x₀ * t.τ) ^ e
  let u1 := (t.x₁ * t.τ) ^ e
  let d0 := u0 * t.x₀⁻¹
  let z0 := conjP t.x₀ sigma2
  let g0 := sigma2 ^ 2
  let dg := conjP d0 g0
  let hc := commP dg d0
  let c0 := commP d0 z0
  let h0 := conjP t.x₀ g0 * t.x₀ * dg * d0 * d0 ^ 2 * hc
  h0 * u1⁻¹ * conjP t.x₁ t.σ * c0

/-- **The wild word's mod-2 exponent vector is `(0, e, 0, e+1)`** (the wild analogue of
`expMod2_fgTame`).  Because `expMod2` lands in the *abelian* `Multiplicative (ZMod 2)`,
conjugations are exponent-invariant and commutators vanish; in `h₀` the two `x₀`-letters and the
two `d₀`-occurrences (`d_g` and the bare `d₀`) cancel and `d₀²` is even, so `ε(h₀) = 0` for
*every* `e` (paper Prop 5.8's proof), leaving `ε(r_w) = ε(u₁⁻¹) + ε(x₁^σ) = (0, e, 0, e+1)`.
At the odd representatives of `ω₂` (`omega2Exp` of any even exponent is odd) this is `(0,1,0,0)`,
matching the tame vector — so condition (40) holds for the `(1,1)` trace and the Stokes
corrections of Lemma 5.7 cancel in Prop 5.8.  (Cf. `docs/erratum-h0-transcription.md`: for the
pre-erratum `h₀` missing the bare `d₀`, the vector was `(0, 0, e+1, e+1)` and they did not.) -/
theorem expMod2_wildValueExp (e : ℕ) :
    (fun i => Multiplicative.toAdd (expMod2 i (wildValueExp freeMarking e)))
      = ![0, (e : ZMod 2), 0, (e : ZMod 2) + 1] := by
  have hconj : ∀ (k : Fin 4) (a b : FreeGroup (Fin 4)), expMod2 k (conjP a b) = expMod2 k a := by
    intro k a b; simp only [conjP, map_mul, map_inv]; rw [mul_right_comm, inv_mul_cancel, one_mul]
  have hcomm : ∀ (k : Fin 4) (a b : FreeGroup (Fin 4)), expMod2 k (commP a b) = 1 := by
    intro k a b; simp only [commP, map_mul, map_inv]
    rw [mul_right_comm (expMod2 k a)⁻¹ (expMod2 k b)⁻¹ (expMod2 k a), inv_mul_cancel, one_mul,
      inv_mul_cancel]
  funext i
  simp only [wildValueExp, freeMarking, map_mul, map_inv, map_pow, hconj, hcomm]
  fin_cases i <;>
    (simp only [expMod2, FreeGroup.lift_apply_of, toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd,
      toAdd_one, Fin.isValue]; ring_nf; generalize (e : ZMod 2) = x; revert x; decide)

/-- `wildValueExp` is natural in group homomorphisms — it uses only `mul`, `inv`, `pow`, `conjP`,
`commP` (no `ω₂`), so no finiteness is needed. -/
theorem wildValueExp_map {G H : Type*} [Group G] [Group H] (φ : G →* H) (t : Marking G) (e : ℕ) :
    φ (wildValueExp t e) = wildValueExp (t.map φ) e := by
  simp only [wildValueExp, Marking.map_σ, Marking.map_τ, Marking.map_x₀, Marking.map_x₁,
    map_mul, map_inv, map_pow, Marking.map_conjP, Marking.map_commP]

/-- For finite `G`, `wildValueExp` at `omega2Exp (Monoid.exponent G)` **is** `Marking.wildValue`:
only `sigma2, u0, u1` carry `ω₂`, and each such element's order divides the exponent, so
`powOmega2_pow_eq` rewrites the three `ω₂`-powers to the explicit `omega2Exp`-power. -/
theorem wildValueExp_eq_wildValue {G : Type*} [Group G] [Finite G] (t : Marking G) :
    t.wildValue = wildValueExp t (omega2Exp (Monoid.exponent G)) := by
  have h : ∀ g : G, powOmega2 g = g ^ omega2Exp (Monoid.exponent G) := fun g =>
    (powOmega2_pow_eq g (Monoid.order_dvd_exponent g) Monoid.exponent_ne_zero_of_finite).symm
  simp only [Marking.wildValue, Marking.h0, Marking.c0, Marking.dg, Marking.hc, Marking.z0,
    Marking.g0, Marking.d0, Marking.u1, Marking.u0, Marking.u, Marking.sigma2, wildValueExp, h]

/-- Divisibility form of `wildValueExp_eq_wildValue`: `wildValueExp t (omega2Exp N) = t.wildValue`
for **any** `N ≠ 0` that is a multiple of the three `ω₂`-subword orders (`σ`, `x₀τ`, `x₁τ`).  Used
to run the bridge at `N = exponent (H(A)⋊C)` on the *lower* groups `C` and `A^∨⋊C` (whose element
orders divide that exponent via the injective section homs). -/
theorem wildValueExp_eq_wildValue_of_dvd {G : Type*} [Group G] {N : ℕ} (hN : N ≠ 0)
    (t : Marking G) (h0 : orderOf t.σ ∣ N) (h1 : orderOf (t.x₀ * t.τ) ∣ N)
    (h2 : orderOf (t.x₁ * t.τ) ∣ N) :
    t.wildValue = wildValueExp t (omega2Exp N) := by
  have hsig : powOmega2 t.σ = t.σ ^ omega2Exp N := (powOmega2_pow_eq t.σ h0 hN).symm
  have hu0 : powOmega2 (t.x₀ * t.τ) = (t.x₀ * t.τ) ^ omega2Exp N := (powOmega2_pow_eq _ h1 hN).symm
  have hu1 : powOmega2 (t.x₁ * t.τ) = (t.x₁ * t.τ) ^ omega2Exp N := (powOmega2_pow_eq _ h2 hN).symm
  simp only [Marking.wildValue, Marking.h0, Marking.c0, Marking.dg, Marking.hc, Marking.z0,
    Marking.g0, Marking.d0, Marking.u1, Marking.u0, Marking.u, Marking.sigma2, wildValueExp,
    hsig, hu0, hu1]

/-- The projection `⟨a,λ,z,g⟩ ↦ ⟨λ, g⟩ : H(A) ⋊ C →* A^∨ ⋊ C` onto the dual lift group. -/
def lgHom : HeisLift A C →* WordLift (ElemDual A) C where
  toFun p := ⟨p.l, p.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `heisMarking t x y` is the free marking pushed through `stokesEval (markVec t) x y`. -/
theorem heisMarking_eq_map (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    heisMarking t x y = freeMarking.map (stokesEval (markVec t) x y) := by
  simp only [heisMarking, freeMarking, Marking.map, markVec, stokesEval, FreeGroup.lift_apply_of,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.tail_cons]

/-- `liftMarking t y` (dual coefficients) is the free marking pushed through `lgHom ∘ stokesEval`. -/
theorem liftMarking_eq_map (t : Marking C) (y : Fin 4 → ElemDual A) :
    liftMarking t y = freeMarking.map (lgHom.comp (stokesEval (markVec t) 0 y)) := by
  simp only [liftMarking, freeMarking, Marking.map, markVec, MonoidHom.comp_apply, lgHom,
    stokesEval, FreeGroup.lift_apply_of, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    MonoidHom.coe_mk, OneHom.coe_mk]

/-- **Tame bridge**: the paper's tame relator value at `heisMarking` equals the free-word
evaluation `stokesEval … fgTame`. -/
theorem bridge_tame (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).tameValue = stokesEval (markVec t) x y fgTame := by
  rw [heisMarking_eq_map, Marking.map_tameValue, freeMarking_tameValue]

/-- The `.l`-coordinate of the `y`-only tame evaluation is `d¹`'s tame row on the dual. -/
theorem stokesEval_tame_l (t : Marking C) (y : Fin 4 → ElemDual A) :
    (stokesEval (markVec t) 0 y fgTame).l = (liftMarking t y).tameValue.u := by
  rw [liftMarking_eq_map, Marking.map_tameValue, freeMarking_tameValue]
  rfl

/-- The lower value of `fgTame` is `t`'s tame relator value; it is `1` under `TameRel`. -/
theorem lift_markVec_tameValue (t : Marking C) :
    FreeGroup.lift (markVec t) fgTame = t.tameValue := by
  rw [← freeMarking_tameValue, ← Marking.map_tameValue]
  congr 1
  simp only [freeMarking, Marking.map, markVec, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.tail_cons]

/-- `d⁰` in `stokesEval`'s form: `d⁰a i = (markVec t i)·a − a`. -/
theorem d0_eq_markVec (t : Marking C) (a : A) : d0 t a = fun i => markVec t i • a - a := by
  funext i
  fin_cases i <;> rfl

/-- **The tame row of Prop 5.8 (41)**: Lemma 5.7 applied to the actual tame relator computes its
mixed central coordinate at the coboundary `d⁰a` — the pairing `⟨a, L^{A^∨}_t(y)⟩` plus the tame
ε-correction `y_τ(τ·a)` (exponent vector `(0,1,0,0)`).  The wild row (and hence full Prop 5.8)
awaits the wild bridge. -/
theorem mixedB_tameRow (t : Marking C) (ht : t.TameRel) (a : A) (y : Fin 4 → ElemDual A) :
    (heisMarking t (d0 t a) y).tameValue.z
      = (d1Fun (A := ElemDual A) t y).1 a + y 1 (t.τ • a) := by
  have hr : FreeGroup.lift (markVec t) fgTame = 1 := by
    rw [lift_markVec_tameValue]; exact (Marking.tameValue_eq_one_iff t).mpr ht
  rw [bridge_tame, d0_eq_markVec, lemma_5_7_left (markVec t) fgTame hr a y]
  congr 1
  · rw [stokesEval_tame_l]; rfl
  · have he : ∀ i, Multiplicative.toAdd (expMod2 i fgTame) = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i :=
      fun i => congrFun expMod2_fgTame i
    simp only [he]
    rw [Fin.sum_univ_four]
    simp [markVec]

/-- **Wild bridge**: the paper's wild relator value at `heisMarking` equals the free-word
evaluation `stokesEval … fgWild`, where `fgWild = wildValueExp freeMarking (omega2Exp (exponent
H(A)⋊C))` is the target-dependent integer-`ω₂` representative of the wild word.  This is the wild
analogue of `bridge_tame`; unlike the tame case it is genuinely target-dependent (the exponent is
`Monoid.exponent (HeisLift A C)`), because `freeMarking.wildValue`'s `ω₂` is degenerate in the
infinite free group.  Feeding this into Lemma 5.7 is what the wild row of Prop 5.8
and the normal-form Lemma 5.13 consume. -/
theorem bridge_wild [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A)
    (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).wildValue
      = stokesEval (markVec t) x y
          (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))) := by
  rw [heisMarking_eq_map, wildValueExp_eq_wildValue, ← wildValueExp_map]

/-! ### The wild row of Prop 5.8

The wild summand `(heisMarking t (d⁰a) y).wildValue.z` is computed exactly like the tame row
(`mixedB_tameRow`), but the free relator word is `fgWild = wildValueExp freeMarking (omega2Exp N)`
with `N = exponent (H(A)⋊C)`, and Lemma 5.7's hypotheses need `wildValueExp _ (omega2Exp N) = _`
on the *lower* groups `C` (for `hr`) and `A^∨⋊C` (for the `.l`-bridge).  Both hold because `C` and
`A^∨⋊C` embed into `H(A)⋊C` by injective section homs, so their element orders divide `N`. -/

/-- The section `g ↦ ⟨0,0,0,g⟩ : C →* H(A) ⋊ C` of the base projection (injective). -/
noncomputable def secHom : C →* HeisLift A C where
  toFun g := ⟨0, 0, 0, g⟩
  map_one' := rfl
  map_mul' g g' := by ext <;> simp

theorem secHom_injective : Function.Injective (secHom (A := A) (C := C)) :=
  fun _ _ h => congrArg HeisLift.g h

/-- The section `⟨λ,g⟩ ↦ ⟨0,λ,0,g⟩ : A^∨ ⋊ C →* H(A) ⋊ C` (injective). -/
noncomputable def secWL : WordLift (ElemDual A) C →* HeisLift A C where
  toFun p := ⟨0, p.u, 0, p.g⟩
  map_one' := rfl
  map_mul' p q := by ext <;> simp

theorem secWL_injective : Function.Injective (secWL (A := A) (C := C)) := by
  intro p q h
  exact WordLift.ext (congrArg HeisLift.l h) (congrArg HeisLift.g h)

/-- Every order in the lower group `C` divides `exponent (H(A) ⋊ C)`. -/
theorem orderOf_dvd_exponent_heis [Finite A] [Finite C] (w : C) :
    orderOf w ∣ Monoid.exponent (HeisLift A C) := by
  rw [← orderOf_injective (secHom (A := A)) secHom_injective w]
  exact Monoid.order_dvd_exponent _

/-- Every order in the dual lift group `A^∨ ⋊ C` divides `exponent (H(A) ⋊ C)`. -/
theorem orderOf_dvd_exponent_heis_wl [Finite A] [Finite C] (w : WordLift (ElemDual A) C) :
    orderOf w ∣ Monoid.exponent (HeisLift A C) := by
  rw [← orderOf_injective (secWL (A := A)) secWL_injective w]
  exact Monoid.order_dvd_exponent _

/-- `2 ∣ exponent (H(A) ⋊ C)`: the central element `z(1) = ⟨0,0,1,1⟩` has order `2`. -/
theorem two_dvd_exponent_heis [Finite A] [Finite C] :
    2 ∣ Monoid.exponent (HeisLift A C) := by
  have hord : orderOf (HeisLift.zc (A := A) (C := C) 1) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← HeisLift.zc_add, show (1 : ZMod 2) + 1 = 0 from by decide]
      exact HeisLift.zc_zero
    · intro h; simpa [HeisLift.zc] using congrArg HeisLift.z h
  rw [← hord]; exact Monoid.order_dvd_exponent _

/-- The `ω₂`-representative at `N = exponent (H(A)⋊C)` is **odd** (its `𝔽₂`-cast is `1`), because
`N` is even.  This is what makes the wild ε-correction reduce to `y_τ(τ·a)`, matching the tame. -/
theorem omega2Exp_exponent_heis_cast [Finite A] [Finite C] :
    (omega2Exp (Monoid.exponent (HeisLift A C)) : ZMod 2) = 1 := by
  have hN : Monoid.exponent (HeisLift A C) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hv : (Monoid.exponent (HeisLift A C)).factorization 2 ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hN two_dvd_exponent_heis).ne'
  have h2 : omega2Exp (Monoid.exponent (HeisLift A C)) ≡ 1 [MOD 2] :=
    (omega2Exp_modEq_one hN hv).of_dvd (dvd_pow_self 2 hv)
  simpa using (ZMod.natCast_eq_natCast_iff _ _ _).mpr h2

/-- The wild `hr`: `fgWild` has trivial lower value, from `WildRel` (via the paper's `ω₂`-ledger
evaluated at the target exponent). -/
theorem lift_markVec_wildValueExp_eq_one [Finite A] [Finite C] (t : Marking C) (hw : t.WildRel) :
    FreeGroup.lift (markVec t)
        (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))) = 1 := by
  have hfm : freeMarking.map (FreeGroup.lift (markVec t)) = t := by
    simp only [freeMarking, Marking.map, markVec, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons]
  rw [wildValueExp_map, hfm,
    ← wildValueExp_eq_wildValue_of_dvd Monoid.exponent_ne_zero_of_finite t
      (orderOf_dvd_exponent_heis t.σ) (orderOf_dvd_exponent_heis (t.x₀ * t.τ))
      (orderOf_dvd_exponent_heis (t.x₁ * t.τ))]
  exact (Marking.wildValue_eq_one_iff t).mpr hw

/-- The wild `.l`-bridge: the `.l`-coordinate of the `y`-only wild evaluation is `d¹`'s wild row
on the dual (the analogue of `stokesEval_tame_l`). -/
theorem stokesEval_wild_l [Finite A] [Finite C] (t : Marking C) (y : Fin 4 → ElemDual A) :
    (stokesEval (markVec t) 0 y
        (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C))))).l
      = (liftMarking t y).wildValue.u := by
  have hlg : lgHom (stokesEval (markVec t) 0 y
      (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
      = (liftMarking t y).wildValue := by
    rw [wildValueExp_map, wildValueExp_map]
    have hmap : (freeMarking.map (stokesEval (markVec t) 0 y)).map lgHom = liftMarking t y := by
      rw [liftMarking_eq_map]; rfl
    rw [hmap, ← wildValueExp_eq_wildValue_of_dvd Monoid.exponent_ne_zero_of_finite (liftMarking t y)
      (orderOf_dvd_exponent_heis_wl _) (orderOf_dvd_exponent_heis_wl _)
      (orderOf_dvd_exponent_heis_wl _)]
  exact congrArg WordLift.u hlg

/-- **The wild row of Prop 5.8 (41)**: the wild summand at the coboundary `d⁰a` equals the pairing
`⟨a, L^{A^∨}_w(y)⟩` plus the ε-correction `y_τ(τ·a)` — the *same* correction as the tame row (the
wild ε-vector `(0, e, 0, e+1)` reduces to `(0,1,0,0)` at the odd `ω₂`-representative). -/
theorem mixedB_wildRow [Finite A] [Finite C] (t : Marking C) (hw : t.WildRel) (a : A)
    (y : Fin 4 → ElemDual A) :
    (heisMarking t (d0 t a) y).wildValue.z
      = (d1Fun (A := ElemDual A) t y).2 a + y 1 (t.τ • a) := by
  rw [bridge_wild, d0_eq_markVec,
    lemma_5_7_left (markVec t) _ (lift_markVec_wildValueExp_eq_one t hw) a y]
  congr 1
  · rw [stokesEval_wild_l]; rfl
  · have hvec : ∀ i, Multiplicative.toAdd
        (expMod2 i (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
        = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i := by
      intro i
      rw [congrFun (expMod2_wildValueExp _) i]
      have hc := omega2Exp_exponent_heis_cast (A := A) (C := C)
      fin_cases i <;> simp only [hc] <;> decide
    simp only [hvec]
    rw [Fin.sum_univ_four]
    simp [markVec]

/-- **Prop 5.8, display (41)** (= chain identity (47) of Prop 5.10 under the canonical
identifications): `B_{ρ,A}(d⁰a, y) = ⟨a, L^{A^∨}_t(y) + L^{A^∨}_w(y)⟩`, where the dual
first relation differentials are `d1Fun` on `A^∨`.

*Status*: sorried (P-13), provable **as stated** (paper p. 17).  Proof plan: the tame summand is
`mixedB_tameRow` — `⟨a, L^{A^∨}_t(y)⟩ + y_τ(τ·a)` (tame ε-vector `(0,1,0,0)`, `expMod2_fgTame`);
the wild summand comes from `bridge_wild` + `lemma_5_7_left` with ε-vector
`(0, e, 0, e+1) = (0,1,0,0)` at the odd `ω₂`-representative (`expMod2_wildValueExp`), i.e.
`⟨a, L^{A^∨}_w(y)⟩ + y_τ(τ·a)`; the two `y_τ(τ·a)` corrections cancel (char 2), which is exactly
condition (40) for the `(1,1)` trace.  (An earlier apparent inconsistency here was a repo-side
`h₀` transcription bug, resolved — see `docs/erratum-h0-transcription.md`.) -/
theorem prop_5_8_left [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a : A) (y : Fin 4 → ElemDual A) :
    mixedB t (d0 t a) y
      = ((d1Fun (A := ElemDual A) t y).1 + (d1Fun (A := ElemDual A) t y).2) a := by
  show (heisMarking t (d0 t a) y).tameValue.z + (heisMarking t (d0 t a) y).wildValue.z = _
  rw [mixedB_tameRow t ht a y, mixedB_wildRow t hw a y, ElemDual.add_apply,
    add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

/-! ### The dual (right) row of Prop 5.8

Mirror of the left row with the `A`-coordinate projection `agHom : H(A)⋊C →* A⋊C` in place of the
dual `lgHom`, and the section `secWA : A⋊C ↪ H(A)⋊C` for the exponent divisibilities.  Lemma 5.7's
*right* form supplies the pairing `⟨L^A_r(x), λ⟩` and the ε-correction `Σᵢ εᵢ(r)·λ(xᵢ)`. -/

/-- The projection `⟨a,λ,z,g⟩ ↦ ⟨a, g⟩ : H(A) ⋊ C →* A ⋊ C` onto the `A`-lift group. -/
def agHom : HeisLift A C →* WordLift A C where
  toFun p := ⟨p.a, p.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The section `⟨u,g⟩ ↦ ⟨u,0,0,g⟩ : A ⋊ C →* H(A) ⋊ C` (injective). -/
noncomputable def secWA : WordLift A C →* HeisLift A C where
  toFun p := ⟨p.u, 0, 0, p.g⟩
  map_one' := rfl
  map_mul' p q := by ext <;> simp

theorem secWA_injective : Function.Injective (secWA (A := A) (C := C)) := by
  intro p q h
  exact WordLift.ext (congrArg HeisLift.a h) (congrArg HeisLift.g h)

theorem orderOf_dvd_exponent_heis_wa [Finite A] [Finite C] (w : WordLift A C) :
    orderOf w ∣ Monoid.exponent (HeisLift A C) := by
  rw [← orderOf_injective (secWA (A := A)) secWA_injective w]
  exact Monoid.order_dvd_exponent _

/-- `liftMarking t x` (over `A`) is the free marking pushed through `agHom ∘ stokesEval`. -/
theorem liftMarking_eq_map_a (t : Marking C) (x : Fin 4 → A) :
    liftMarking t x = freeMarking.map (agHom.comp (stokesEval (markVec t) x 0)) := by
  simp only [liftMarking, freeMarking, Marking.map, markVec, MonoidHom.comp_apply, agHom,
    stokesEval, FreeGroup.lift_apply_of, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
    MonoidHom.coe_mk, OneHom.coe_mk]

/-- The `.a`-coordinate of the `x`-only tame evaluation is `d¹`'s tame row on `A`. -/
theorem stokesEval_tame_a (t : Marking C) (x : Fin 4 → A) :
    (stokesEval (markVec t) x 0 fgTame).a = (liftMarking t x).tameValue.u := by
  rw [liftMarking_eq_map_a, Marking.map_tameValue, freeMarking_tameValue]
  rfl

/-- The `.a`-coordinate of the `x`-only wild evaluation is `d¹`'s wild row on `A`. -/
theorem stokesEval_wild_a [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A) :
    (stokesEval (markVec t) x 0
        (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C))))).a
      = (liftMarking t x).wildValue.u := by
  have hag : agHom (stokesEval (markVec t) x 0
      (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
      = (liftMarking t x).wildValue := by
    rw [wildValueExp_map, wildValueExp_map]
    have hmap : (freeMarking.map (stokesEval (markVec t) x 0)).map agHom = liftMarking t x := by
      rw [liftMarking_eq_map_a]; rfl
    rw [hmap, ← wildValueExp_eq_wildValue_of_dvd Monoid.exponent_ne_zero_of_finite (liftMarking t x)
      (orderOf_dvd_exponent_heis_wa _) (orderOf_dvd_exponent_heis_wa _)
      (orderOf_dvd_exponent_heis_wa _)]
  exact congrArg WordLift.u hag

/-- **The tame row of Prop 5.8 (42)** (dual form): `⟨L^A_t(x), λ⟩ + λ(x_τ)`. -/
theorem mixedB_tameRow_right (t : Marking C) (ht : t.TameRel) (x : Fin 4 → A) (lam : ElemDual A) :
    (heisMarking t x (d0 (A := ElemDual A) t lam)).tameValue.z
      = lam ((d1Fun t x).1) + lam (x 1) := by
  have hr : FreeGroup.lift (markVec t) fgTame = 1 := by
    rw [lift_markVec_tameValue]; exact (Marking.tameValue_eq_one_iff t).mpr ht
  rw [bridge_tame, d0_eq_markVec, lemma_5_7_right (markVec t) fgTame hr x lam]
  congr 1
  · rw [stokesEval_tame_a]; rfl
  · have he : ∀ i, Multiplicative.toAdd (expMod2 i fgTame) = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i :=
      fun i => congrFun expMod2_fgTame i
    simp only [he]
    rw [Fin.sum_univ_four]
    simp

/-- **The wild row of Prop 5.8 (42)** (dual form): `⟨L^A_w(x), λ⟩ + λ(x_τ)` — same correction as
the tame row. -/
theorem mixedB_wildRow_right [Finite A] [Finite C] (t : Marking C) (hw : t.WildRel)
    (x : Fin 4 → A) (lam : ElemDual A) :
    (heisMarking t x (d0 (A := ElemDual A) t lam)).wildValue.z
      = lam ((d1Fun t x).2) + lam (x 1) := by
  rw [bridge_wild, d0_eq_markVec,
    lemma_5_7_right (markVec t) _ (lift_markVec_wildValueExp_eq_one t hw) x lam]
  congr 1
  · rw [stokesEval_wild_a]; rfl
  · have hvec : ∀ i, Multiplicative.toAdd
        (expMod2 i (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
        = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i := by
      intro i
      rw [congrFun (expMod2_wildValueExp _) i]
      have hc := omega2Exp_exponent_heis_cast (A := A) (C := C)
      fin_cases i <;> simp only [hc] <;> decide
    simp only [hvec]
    rw [Fin.sum_univ_four]
    simp

/-- **Prop 5.8, display (42)** (= chain identity (48)): `B_{ρ,A}(x, d⁰λ) = ⟨L_t(x)+L_w(x), λ⟩`.
Proved as stated: `mixedB = tameRow + wildRow`, and the two `λ(x_τ)` corrections cancel (char 2). -/
theorem prop_5_8_right [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (x : Fin 4 → A) (lam : ElemDual A) :
    mixedB t x (d0 (A := ElemDual A) t lam)
      = lam ((d1Fun t x).1 + (d1Fun t x).2) := by
  show (heisMarking t x (d0 (A := ElemDual A) t lam)).tameValue.z
      + (heisMarking t x (d0 (A := ElemDual A) t lam)).wildValue.z = _
  rw [mixedB_tameRow_right t ht x lam, mixedB_wildRow_right t hw x lam, map_add,
    add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

/-- **Lemma 5.6 (strict coefficient naturality)**, in the traced form Prop 5.10 uses: for an
equivariant `f : A → A'`, `B_{A'}(f∗x, y') = B_A(x, f^∨ y')`.

Proof (the paper's "evaluate in the mixed Heisenberg group"): the two markings live in
`H(A') ⋊ C` and `H(A) ⋊ C`, related by `f` on the `A`-slot and `f^∨` on the dual slot.  They both
sit inside the **mixed subgroup** `S ≤ H(A') ⋊ C × H(A) ⋊ C` cut out by "`f`-related `a`/`λ`,
equal `z`, equal `g`" — a subgroup precisely because `f` is `C`-equivariant.  The two projections
`π₁, π₂ : S →* …` carry the mixed marking to the two sides (`Marking.map_tameValue`/`map_wildValue`,
the latter needing `S` finite for the `ω₂`-powers), and `S`'s defining `z`-equation makes the two
relator `z`-coordinates agree — which is exactly the claim.

(Requires `A`, `A'`, `C` finite, the paper's finite setting: `map_wildValue`'s `ω₂` push needs the
source group finite.) -/
theorem lemma_5_6 {A' : Type*} [AddCommGroup A'] [DistribMulAction C A'] [Finite A] [Finite A']
    [Finite C] (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a) (t : Marking C)
    (x : Fin 4 → A) (y' : Fin 4 → ElemDual A') :
    mixedB t (fun i => f (x i)) y'
      = mixedB t x (fun i => ((y' i : A' →+ ZMod 2).comp f : ElemDual A)) := by
  -- The dual (contragredient) `f^∨ : A'^∨ →+ A^∨`, `λ ↦ λ ∘ f`, bundled so results stay `ElemDual`.
  let fStar : ElemDual A' →+ ElemDual A :=
    { toFun := fun lam => lam.comp f
      map_zero' := AddMonoidHom.zero_comp f
      map_add' := fun a b => AddMonoidHom.add_comp a b f }
  have fStar_apply : ∀ (lam : ElemDual A') (a : A), fStar lam a = lam (f a) := fun _ _ => rfl
  -- Dual `f`-equivariance: `f^∨ (g • λ) = g • f^∨ λ`.
  have hcomp : ∀ (g : C) (lam : ElemDual A'), fStar (g • lam) = g • fStar lam := by
    intro g lam; ext a; simp only [fStar_apply, ElemDual.smul_apply, hf]
  -- The mixed subgroup of `H(A') ⋊ C × H(A) ⋊ C`.
  let S : Subgroup (HeisLift A' C × HeisLift A C) :=
    { carrier := {pq | pq.1.a = f pq.2.a ∧ pq.2.l = fStar pq.1.l ∧ pq.1.z = pq.2.z ∧
        pq.1.g = pq.2.g}
      one_mem' := ⟨by simp, by simp, rfl, rfl⟩
      mul_mem' := fun {P Q} hP hQ =>
        ⟨by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_a, map_add, hf, hP.1, hQ.1,
            hP.2.2.2],
          by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_l, map_add, hcomp,
            hP.2.1, hQ.2.1, hP.2.2.2],
          by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_z, hP.2.2.1,
            hQ.2.2.1, hP.2.1, hP.2.2.2, hQ.1, fStar_apply, hf],
          by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_g, hP.2.2.2, hQ.2.2.2]⟩
      inv_mem' := fun {P} hP =>
        ⟨by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_a, map_neg, hf, hP.1, hP.2.2.2],
          by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_l, map_neg, hcomp,
            hP.2.1, hP.2.2.2],
          by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_z, hP.2.2.1, hP.2.1, hP.1,
            fStar_apply],
          by simp only [Prod.fst_inv, Prod.snd_inv, HeisLift.inv_g, hP.2.2.2]⟩ }
  -- The two projections and the mixed marking.
  let π₁ : ↥S →* HeisLift A' C := (MonoidHom.fst (HeisLift A' C) (HeisLift A C)).comp S.subtype
  let π₂ : ↥S →* HeisLift A C := (MonoidHom.snd (HeisLift A' C) (HeisLift A C)).comp S.subtype
  let M : Marking ↥S :=
    ⟨⟨(⟨f (x 0), y' 0, 0, t.σ⟩, ⟨x 0, (y' 0).comp f, 0, t.σ⟩), ⟨rfl, rfl, rfl, rfl⟩⟩,
      ⟨(⟨f (x 1), y' 1, 0, t.τ⟩, ⟨x 1, (y' 1).comp f, 0, t.τ⟩), ⟨rfl, rfl, rfl, rfl⟩⟩,
      ⟨(⟨f (x 2), y' 2, 0, t.x₀⟩, ⟨x 2, (y' 2).comp f, 0, t.x₀⟩), ⟨rfl, rfl, rfl, rfl⟩⟩,
      ⟨(⟨f (x 3), y' 3, 0, t.x₁⟩, ⟨x 3, (y' 3).comp f, 0, t.x₁⟩), ⟨rfl, rfl, rfl, rfl⟩⟩⟩
  have hπ₁ : M.map π₁ = heisMarking t (fun i => f (x i)) y' := rfl
  have hπ₂ : M.map π₂ = heisMarking t x (fun i => ((y' i).comp f : ElemDual A)) := rfl
  -- On `S`, the two projections have equal `z`-coordinate (the defining `z`-equation).
  have key : ∀ w : ↥S, (π₁ w).z = (π₂ w).z := fun w => w.2.2.2.1
  simp only [mixedB, ← hπ₁, ← hπ₂, Marking.map_tameValue, Marking.map_wildValue,
    key M.tameValue, key M.wildValue]

end Traced

/-! ## The duality package: `IsSelfDual`, 5.11, 5.12, 5.13, 5.15 -/

section Duality

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The `C`-fixed points of a module (the invariants `M^C`, as a `Set` — `Nat.card` needs no
subgroup structure). -/
def fixedPts (C : Type*) [Group C] (M : Type*) [AddCommGroup M] [DistribMulAction C M] :
    Set M :=
  {m | ∀ g : C, g • m = m}

/-- **The Prop 5.15 conclusion, packaged** (candidate side, at a marking `t` and module `A`):
the display-(56) numerics and a perfect degree-one pairing descending the traced mixed
coordinate `B_{ρ,A}`.  "Perfect" is encoded as two-sided nondegeneracy (equivalent for finite
elementary groups given the card clauses).  Lemma 5.11 is two-out-of-three for this
predicate. -/
def IsSelfDual (t : Marking C) (A : Type*) [AddCommGroup A] [DistribMulAction C A] [Finite A] :
    Prop :=
  (Nat.card (H2w (A := A) t) = Nat.card (fixedPts C (ElemDual A))) ∧
  (Nat.card (Z1w (A := A) t) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))) ∧
  ∃ P : H1w (A := A) t → H1w (A := ElemDual A) t → ZMod 2,
    (∀ (x : Z1w (A := A) t) (y : Z1w (A := ElemDual A) t),
        P (h1wMk t x) (h1wMk t y) = mixedB t x.val y.val) ∧
    (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
    (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)

/- **Lemma 5.11 (exact cone dévissage) — PROVED, relocated to `GQ2/Devissage.lean` (P-13e).**
Same fully qualified name `GQ2.FoxH.lemma_5_11`, with one hypothesis added relative to the P-12
statement: `hgen : t.Generates`.  Generation identifies `ker d⁰` with the `C`-fixed points
(`H0w_eq_fixedPts`), which the word-complex dévissage needs to reach the `fixedPts`-phrased
`IsSelfDual`; admissible markings always have it.  It lives there because the proof needs the
Devissage machinery and imports run `FoxHeisenberg → Devissage`.  The generation-free
word-internal form is `selfdualW_two_of_three` (two-out-of-three for `IsSelfDualW`). -/

/-- Simplicity of a `𝔽₂[C]`-module, subgroup form: nonzero, and the only `C`-stable additive
subgroups are `⊥` and `⊤` (no `Module` instances, per the repo convention). -/
def IsSimpleModTwo (C : Type*) [Group C] (V : Type*) [AddCommGroup V]
    [DistribMulAction C V] : Prop :=
  Nontrivial V ∧
    ∀ W : AddSubgroup V, (∀ (g : C) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤

omit [Finite C] in
/-- **Lemma 5.12 (simple characteristic-two modules are tame)**: a normal 2-subgroup `L ◁ C`
acts trivially on every simple `𝔽₂[C]`-module.  Proof: the `L`-fixed subspace is nonzero (the
`p`-group congruence `#V ≡ #Vᴸ (mod 2)` with `#V` even) and `C`-stable (`L` normal), so
simplicity forces it to be all of `V`.  (Proved for P-13.  The Heisenberg word-evaluation core is
now complete — `d1Fun_add`, `d1Fun_comp_d0`, Lemma 5.6, Lemma 5.7 both forms, and the tame row of
Prop 5.8 — so the remaining §5 sorries concentrate in the *wild row* (Prop 5.8/Lemma 5.13, needing
the target-dependent integer-`ω₂` representative of the wild word) and the mapping-cone dévissage
Lemma 5.11.) -/
theorem lemma_5_12 {V : Type*} [AddCommGroup V] [DistribMulAction C V] [Finite V]
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (L : Subgroup C) (hnormal : L.Normal) (hL : IsPGroup 2 L) :
    ∀ g ∈ L, ∀ v : V, g • v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial V := hsimple.1
  -- The additive subgroup of `L`-fixed vectors.
  let W : AddSubgroup V :=
    { carrier := {v | ∀ g ∈ L, g • v = v}
      zero_mem' := fun g _ => smul_zero g
      add_mem' := fun {a b} ha hb g hg => by rw [smul_add, ha g hg, hb g hg]
      neg_mem' := fun {a} ha g hg => by rw [smul_neg, ha g hg] }
  have hmemW : ∀ {v : V}, v ∈ W ↔ ∀ g ∈ L, g • v = v := Iff.rfl
  -- `W` is `C`-stable, since `L` is normal.
  have hstable : ∀ (c : C) (w : V), w ∈ W → c • w ∈ W := by
    intro c w hw g hg
    have hgc : c⁻¹ * g * c ∈ L := by simpa using hnormal.conj_mem g hg c⁻¹
    have hrw : g * c = c * (c⁻¹ * g * c) := by group
    rw [← mul_smul, hrw, mul_smul, hmemW.mp hw _ hgc]
  -- The `↥L`-fixed points coincide with `W` as sets.
  have hset : (MulAction.fixedPoints ↥L V : Set V) = (W : Set V) := by
    ext v
    refine ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  -- `|V|` is even: a nonzero `𝔽₂`-space has an order-2 element.
  have h2 : 2 ∣ Nat.card V := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hord : addOrderOf v = 2 := addOrderOf_eq_prime (by rw [two_nsmul]; exact hV₂ v) hv
    exact hord ▸ addOrderOf_dvd_natCard v
  -- Hence some nonzero vector is `L`-fixed: `W ≠ ⊥`.
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hmod := hL.card_modEq_card_fixedPoints (p := 2) V
    have hsub : Subsingleton ↥(MulAction.fixedPoints ↥L V) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have haW : a ∈ W := by rw [← SetLike.mem_coe, ← hset]; exact ha
      have hbW : b ∈ W := by rw [← SetLike.mem_coe, ← hset]; exact hb
      rw [hbot, AddSubgroup.mem_bot] at haW hbW
      exact Subtype.ext (haW.trans hbW.symm)
    have h0fp : (0 : V) ∈ MulAction.fixedPoints ↥L V := by
      have : (0 : V) ∈ (W : Set V) := W.zero_mem
      rwa [← hset] at this
    have hfp1 : Nat.card ↥(MulAction.fixedPoints ↥L V) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨0, h0fp⟩⟩⟩
    rw [hfp1] at hmod
    have h0 : Nat.card V ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr h2
    exact absurd (h0.symm.trans hmod) (by decide)
  -- Simplicity forces `W = ⊤`, i.e. `L` acts trivially.
  rcases hsimple.2 W hstable with h | h
  · exact absurd h hWne
  · intro g hg v
    exact (h ▸ AddSubgroup.mem_top v : v ∈ W) g hg

end Duality

/-! ## Lemma 5.2: the exact class-two identity (§5.1 ledger)

The auxiliary word `h₀ = (x₀^{g₀})·x₀·d_g·d₀·d₀²·[d_g,d₀]` (`Marking.h0`) has the class-two shape
`h_ϕ(X,D) = ϕ(X)·X·ϕ(D)·D·D²·[ϕ(D),D]` with `ϕ = (·)^{g₀}` (conjugation by `g₀`), `X = x₀`,
`D = d₀`.  Paper Lemma 5.2 collapses it to `ϕ(X)·X·D⁻¹·ϕ(D)` (display (32)) in any group in which
`[ϕ(D),D]` is central of order ≤ 2 and `D⁴ = 1` — the class-two setting of the coefficient
Heisenberg/extraspecial groups.  This is the algebraic heart of the `h₀`-shadow (Lemma 5.3) and the
mixed Hessian (Lemma 5.14): `h₀` may replace `x₀²` in every first-order, cup, and central ledger. -/

section ClassTwo

variable {G : Type*} [Group G]

/-- **Lemma 5.2, core cancellation.**  If the commutator `k = [A,B]` (`commP` convention
`A⁻¹B⁻¹AB`) is central and satisfies `k² = 1`, and `B⁴ = 1`, then `A·B·B²·[A,B] = B⁻¹·A`.
This is display (32) after cancelling the common prefix `ϕ(X)·X` (with `A = ϕ(D)`, `B = D`).

The proof is the paper's: from `A·B = B·A·k` (`hcomm`), `k` central and `k² = 1` give that `A`
commutes with `B²`, and `B³ = B⁻¹`; then `A·B·B²·k = B·A·B² = B³·A = B⁻¹·A`.  The associativity
bookkeeping is discharged by right-normalising with `simp only [mul_assoc, …]`, feeding the
commutator relation in the right-associated form `A·(B·x) = B·(A·(k·x))` so it fires under the
normal form. -/
theorem classTwoCore (A B : G)
    (hcentral : ∀ z : G, commP A B * z = z * commP A B)
    (hk2 : commP A B * commP A B = 1) (hB4 : B ^ 4 = 1) :
    A * B * B ^ 2 * commP A B = B⁻¹ * A := by
  set k := commP A B with hk
  have hcomm : A * B = B * A * k := by rw [hk, commP]; group
  have hkB : k * B = B * k := hcentral B
  have hcomm' : ∀ x : G, A * (B * x) = B * (A * (k * x)) := fun x => by
    rw [← mul_assoc, hcomm, mul_assoc, mul_assoc]
  have hkB' : ∀ x : G, k * (B * x) = B * (k * x) := fun x => by rw [← mul_assoc, hkB, mul_assoc]
  have hBBBB : B * B * B * B = 1 := by
    rw [show B * B * B * B = B ^ 4 from by rw [← pow_two, ← pow_succ, ← pow_succ]]; exact hB4
  have hB3 : B * B * B = B⁻¹ := mul_eq_one_iff_eq_inv.mp hBBBB
  rw [pow_two]
  simp only [mul_assoc, hcomm', hkB, hkB', hk2, mul_one]
  rw [← hB3]
  simp only [mul_assoc]

/-- **Lemma 5.2, display (32)**: `h_ϕ(X,D) = ϕ(X)·X·ϕ(D)·D·D²·[ϕ(D),D] = ϕ(X)·X·D⁻¹·ϕ(D)`,
whenever `[ϕ(D),D]` is central of order ≤ 2 and `D⁴ = 1`.  (`ϕ` need not be a homomorphism for the
identity; the paper's `ϕ` is a `Z`-fixing automorphism, which is what makes the hypotheses hold for
the actual `h₀`.) -/
theorem classTwoIdentity (φ : G → G) (X D : G)
    (hcentral : ∀ z : G, commP (φ D) D * z = z * commP (φ D) D)
    (hk2 : commP (φ D) D * commP (φ D) D = 1) (hD4 : D ^ 4 = 1) :
    φ X * X * φ D * D * D ^ 2 * commP (φ D) D = φ X * X * D⁻¹ * φ D := by
  calc φ X * X * φ D * D * D ^ 2 * commP (φ D) D
      = φ X * X * (φ D * D * D ^ 2 * commP (φ D) D) := by simp only [mul_assoc]
    _ = φ X * X * (D⁻¹ * φ D) := by rw [classTwoCore (φ D) D hcentral hk2 hD4]
    _ = φ X * X * D⁻¹ * φ D := by simp only [mul_assoc]

/-- **Lemma 5.2(ii)**: when `ϕ = id`, `h_ϕ(X,D) = X²` for every `D` (`[D,D] = 1`).  Used in the
split (`P = 1`) branch of the `h₀`-shadow, where `g₀ = σ₂²` acts trivially. -/
theorem classTwoIdentity_id (X D : G) (hD4 : D ^ 4 = 1) :
    X * X * D * D * D ^ 2 * commP D D = X ^ 2 := by
  have hc0 : commP D D = 1 := by rw [commP]; group
  have hcc : ∀ z : G, commP D D * z = z * commP D D := by intro z; rw [hc0, one_mul, mul_one]
  have hk2 : commP D D * commP D D = 1 := by rw [hc0, mul_one]
  calc X * X * D * D * D ^ 2 * commP D D
      = X * X * (D * D * D ^ 2 * commP D D) := by simp only [mul_assoc]
    _ = X * X * (D⁻¹ * D) := by rw [classTwoCore D D hcc hk2 hD4]
    _ = X ^ 2 := by rw [inv_mul_cancel, mul_one, pow_two]

end ClassTwo

end FoxH

end GQ2
