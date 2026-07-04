import GQ2.Subdirect
import GQ2.CupProduct
import GQ2.Statement

/-!
# §5 statements: the two source-specific lifting theories  (ticket P-12)

The paper's §5 sets up, for a finite *lower target* `C` and an elementary `𝔽₂[C]`-module `A`,
the two cochain theories that the §9 induction compares: the **finite word complex** (30) on the
candidate side, and continuous Galois cohomology on the local side.  This file provides the
definition layer (the complex, the Heisenberg groups, the mixed central coordinate) and the
**sorried statements** of Lemmas/Propositions 5.6, 5.7, 5.8, 5.11, 5.12, 5.13, 5.15, 5.16 with a
proved 5.17-numerics wiring corollary.  Proof ticket: P-13 (axioms B6, B7 enter only there, in
5.16).

## The §5 objects and their encodings

* **Coefficients.**  `A` is an "elementary `𝔽₂[C]`-module": `[AddCommGroup A]` +
  `[DistribMulAction C A]` + the hypothesis `hA₂ : ∀ a : A, a + a = 0` (+ `[Finite A]` where the
  paper says finite).  No `Module 𝔽₂` instances (T-02/T-09 pattern); "dim"-statements are stated
  in `Nat.card` form (e.g. `2^{2 dim A + dim (A^∨)^C}` becomes `#A² · #(A^∨)^C`).
* **The lower map.**  The complex depends on `ρ : Γ ↠ C` only through the four marked values
  `ρ(σ), ρ(τ), ρ(x₀), ρ(x₁)`, i.e. through the pushed marking `univMarking.map ρ` — so the
  whole candidate-side theory is parametrized by a `t : Marking C` (`GQ2/Words.lean`), keeping
  §5 purely finite.  The relations enter as hypotheses `t.TameRel`, `t.WildRel` where the paper
  assumes `ρ` kills the relators.
* **Relator values.**  `Marking.tameValue = τ^σ (τ²)⁻¹` and `Marking.wildValue = h₀u₁⁻¹x₁^σc₀`
  (relations (5)/(6) as *elements*; `= 1 ↔ TameRel/WildRel` proved).  The `ω₂`-powers are
  `powOmega2` — by T-06's headline these compute the profinite `ω₂` in every finite group, and
  by `powOmega2_pow_eq` any integer representative modulo the relevant exponent agrees: that is
  exactly **Lemma 5.1** (finite-exponent independence), which is therefore *absorbed by the
  encoding* and not re-stated.
* **`A ⋊ C`** (`WordLift A C`): own structure with the paper's lift convention
  `(u, g)(v, h) = (u + g•v, gh)` (Lemma 5.5's proof display) — definitional, no
  `Multiplicative`-wrapped `SemidirectProduct` (avoids the T-09 wrapper traps).
* **The word complex (30)/(31).**  `d0 t : A →+ (Fin 4 → A)` is (31) (indices `0,1,2,3` =
  `σ,τ,x₀,x₁`, matching `univMarking`); `d1Fun t x` is the pair of `A`-coordinates of the two
  relator values at the lifted marking `liftMarking t x` — the paper's "coefficient of `A` in
  the evaluated tame and wild relators", verbatim.  **Additivity of `d1Fun` is the paper's
  "finite Fox rules" and is a sorried obligation** (`d1Fun_add`, P-13, via the ledger of
  Lemma 5.4); the bundled `d1 t` is built on it, and `Z1w/H0w/H1w/H2w` follow the `ContCoh`
  shape (`H1 = Z1 ⧸ B1.addSubgroupOf Z1` — total definitions, no chain condition needed; the
  chain identity `d¹∘d⁰ = 0` under the relations is the separate sorried `d1Fun_comp_d0`).
  The **proved** stress test `d1Fun_tame` computes the tame row in closed form — the general
  form of display (34), validating the convention stack (lift order, `conjP`, the `(u,g)(v,h)`
  rule) end-to-end.
* **`𝔽₂`-duals** (`ElemDual A := A →+ ZMod 2`): T-14's `MuDual` def-synonym recipe (own
  `FunLike`, contragredient action `(g•λ)(a) = λ(g⁻¹•a)`; a plain `abbrev` would collide with
  Mathlib's codomain-action instance).
* **`H(A) ⋊ C`** (`HeisLift A C`, §5.2): own structure on `A × A^∨ × 𝔽₂ × C` with the paper's
  multiplication `(a,λ,z)(a',λ',z') = (a+a', λ+λ', z+z'+λ(a'))` twisted by the diagonal
  `C`-action — again definitional.  `mixedB t x y` is the traced mixed central coordinate
  `B_{ρ,A} = β_t + β_w` of Prop 5.8 (the **sum** of the two words' `z`-coordinates, not the
  `z`-coordinate of their product).
* **Stokes** (Lemma 5.7): stated in the paper's general form — ordinary free group
  `FreeGroup (Fin n)` (Mathlib's, not profinite), evaluation `stokesEval` via `FreeGroup.lift`,
  mod-2 exponents `expMod2` via the lift to `Multiplicative (ZMod 2)`.  The tame relator's
  exponent vector `(0,1,0,0)` (Prop 5.8's proof) is **proved** here for the free-group tame
  word (`expMod2_fgTame`); the wild word's vector is P-13 content (it needs the integer-`ω₂`
  representative words).
* **Duality statements.**  5.15/5.16 are stated in `Nat.card` + pairing form; "perfect" is
  encoded as two-sided nondegeneracy (equivalent to perfectness for finite elementary groups,
  given the card clauses).  On the candidate side the descended `H¹×H¹`-pairing is carried
  *inside* the statement (`∃ P, descends mixedB ∧ nondegenerate`) — no descent-backed
  definitions, so the definition layer stays sorry-free.  On the local side the pairing is the
  *already-descended* T-04 cup product with the evaluation pairing `dualEval`, T-14's
  `TateDuality` phrasing; the target-line certification is the clause `#H²(𝔽₂-trivial) = 2`.
  `IsSelfDual` packages the 5.15 conclusion; **Lemma 5.11** (dévissage) is stated as
  two-out-of-three for `IsSelfDual` along a short exact sequence of coefficient modules — the
  mapping cone `K(A)` of (49) is its *proof* device (P-13), not statement content (flagged
  deviation).
* **Prop 5.10** (the Fox–Heisenberg chain map) is *not* packaged as a `HomologicalComplex`
  map: its degree-(0,2) components are the trivial `traceD0`/`traceD2` below, and its two
  chain identities (47)/(48) are — after unfolding the canonical identifications — exactly
  Prop 5.8's (41)/(42) with `L = d1Fun` on `A` resp. `A^∨`.  Statement content = 5.8 + 5.6;
  deviation flagged.

## Deferred (flagged deviations)

* **Corollary 5.17's adjoint-boundary identity (58)** needs connecting maps
  `∂ : H¹(V) → H²(T)` in *both* theories (snake maps for the word complex, coefficient-SES
  connecting maps for `ContCoh`) — infrastructure that does not exist yet and whose shape
  should be fixed by its consumer (§9.2/9.3).  P-12 ships the *numerics* half
  (`cor_5_17_card`, proved from 5.15+5.16); the (58)-half is deferred to P-13 with the §9
  designer (P-17) as tiebreaker on the encoding.  Recorded on the board.
* Lemmas 5.2/5.3/5.4/5.14 (class-two identity, `h₀`-shadow, ledger, Hessian) are proof-layer
  calculations for P-13; Remark 5.9's `GL₂(𝔽₂)` regression test is P-13's designated test
  case.  Lemma 5.1 is absorbed (see above).

Conventions: `x ^ g = g⁻¹xg` (`conjP`), `[x,y] = x⁻¹y⁻¹xy` (`commP`), marking order
`(σ, τ, x₀, x₁)` = indices `0,1,2,3`.
-/

namespace GQ2

/-! ## Relations (5)/(6) as elements of any marked group -/

/-- The **tame relator value** `τ^σ · (τ²)⁻¹` at a marking (relation (5) as an element). -/
def Marking.tameValue {G : Type*} [Group G] (t : Marking G) : G :=
  conjP t.τ t.σ * (t.τ ^ 2)⁻¹

/-- The tame relator dies iff the tame relation holds. -/
@[simp] theorem Marking.tameValue_eq_one_iff {G : Type*} [Group G] (t : Marking G) :
    t.tameValue = 1 ↔ t.TameRel :=
  mul_inv_eq_one

/-- The **wild relator value** `h₀ · u₁⁻¹ · x₁^σ · c₀` at a marking (relation (6) as an
element; the `ω₂`-powers are `powOmega2`). -/
noncomputable def Marking.wildValue {G : Type*} [Group G] (t : Marking G) : G :=
  t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0

/-- The wild relator dies iff the wild relation holds. -/
@[simp] theorem Marking.wildValue_eq_one_iff {G : Type*} [Group G] (t : Marking G) :
    t.wildValue = 1 ↔ t.WildRel :=
  Iff.rfl

/-- **Naturality of the tame relator value** under a group homomorphism.  (No `ω₂`-power occurs
in the tame word, so no finiteness is needed.) -/
theorem Marking.map_tameValue {G H : Type*} [Group G] [Group H] (φ : G →* H) (t : Marking G) :
    (t.map φ).tameValue = φ t.tameValue := by
  simp only [tameValue, Marking.map_σ, Marking.map_τ, map_mul, map_inv, map_pow,
    Marking.map_conjP]

/-- **Naturality of the wild relator value** under a group homomorphism.  The `ω₂`-powers in the
wild word push through `φ` via `powOmega2_map`, which needs the source group finite. -/
theorem Marking.map_wildValue {G H : Type*} [Group G] [Group H] [Finite G] (φ : G →* H)
    (t : Marking G) : (t.map φ).wildValue = φ t.wildValue := by
  simp only [wildValue, Marking.map_h0, Marking.map_u1, Marking.map_x₁, Marking.map_σ,
    Marking.map_c0, map_mul, map_inv, Marking.map_conjP]

namespace FoxH

/-! ## The lift group `A ⋊ C`  (paper convention `(u,g)(v,h) = (u + g•v, gh)`) -/

/-- The lift group `A ⋊ C` of §5: pairs `(u, g)` with the multiplication of Lemma 5.5's proof,
`(u, g)(v, h) = (u + g•v, gh)`. -/
@[ext] structure WordLift (A C : Type*) where
  /-- The `A`-offset of the lift. -/
  u : A
  /-- The base value in `C`. -/
  g : C

namespace WordLift

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

instance : One (WordLift A C) := ⟨⟨0, 1⟩⟩
instance : Mul (WordLift A C) := ⟨fun p q => ⟨p.u + p.g • q.u, p.g * q.g⟩⟩
instance : Inv (WordLift A C) := ⟨fun p => ⟨-(p.g⁻¹ • p.u), p.g⁻¹⟩⟩

omit [DistribMulAction C A] in
@[simp] theorem one_u : (1 : WordLift A C).u = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_g : (1 : WordLift A C).g = 1 := rfl

@[simp] theorem mul_u (p q : WordLift A C) : (p * q).u = p.u + p.g • q.u := rfl
@[simp] theorem mul_g (p q : WordLift A C) : (p * q).g = p.g * q.g := rfl
@[simp] theorem inv_u (p : WordLift A C) : p⁻¹.u = -(p.g⁻¹ • p.u) := rfl
@[simp] theorem inv_g (p : WordLift A C) : p⁻¹.g = p.g⁻¹ := rfl

instance : Group (WordLift A C) where
  mul_assoc p q r := by
    ext
    · simp only [mul_u, mul_g, smul_add, mul_smul, add_assoc]
    · simp only [mul_g, mul_assoc]
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by ext <;> simp

/-- `WordLift A C ≃ A × C` (the underlying data), for the finiteness instance. -/
def equivProd : WordLift A C ≃ A × C where
  toFun p := (p.u, p.g)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite A] [Finite C] : Finite (WordLift A C) := Finite.of_equiv _ equivProd.symm

variable {A' : Type*} [AddCommGroup A'] [DistribMulAction C A']

/-- **Coefficient functoriality**: a `C`-equivariant `f : A →+ A'` induces a group homomorphism
`WordLift A C →* WordLift A' C` (the identity on the base `C`). -/
def map (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a) :
    WordLift A C →* WordLift A' C where
  toFun p := ⟨f p.u, p.g⟩
  map_one' := by ext <;> simp
  map_mul' p q := by
    ext
    · show f (p.u + p.g • q.u) = f p.u + p.g • f q.u
      rw [map_add, hf]
    · rfl

@[simp] theorem map_u (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a)
    (p : WordLift A C) : (map f hf p).u = f p.u := rfl

@[simp] theorem map_g (f : A →+ A') (hf : ∀ (g : C) (a : A), f (g • a) = g • f a)
    (p : WordLift A C) : (map f hf p).g = p.g := rfl

/-- The base embedding `C →* WordLift A C`, `g ↦ (0, g)` (the offset-zero lift). -/
def baseEmbed : C →* WordLift A C where
  toFun g := ⟨0, g⟩
  map_one' := rfl
  map_mul' g h := by ext <;> simp

@[simp] theorem baseEmbed_apply (g : C) : (baseEmbed (A := A) g) = ⟨0, g⟩ := rfl

/-- Conjugating a base generator `(0, g)` by `(v, 1)` produces the coboundary offset
`(g • v − v, g)` — the shape of `d⁰`. -/
theorem conj_baseEmbed (v : A) (g : C) :
    (⟨v, 1⟩ : WordLift A C)⁻¹ * ⟨0, g⟩ * ⟨v, 1⟩ = ⟨g • v - v, g⟩ := by
  ext
  · simp only [mul_u, mul_g, inv_u, inv_g, inv_one, one_smul, smul_zero, one_mul, add_zero]
    abel
  · simp only [mul_g, inv_g, inv_one, one_mul, mul_one]

/-- The base coordinate of a power is the power of the base (`.g` is multiplicative). -/
@[simp] theorem pow_g (p : WordLift A C) (n : ℕ) : (p ^ n).g = p.g ^ n := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, pow_succ, mul_g, ih]

/-- **The norm-of-power (geometric sum) formula** — the source of the paper's "norm projector"
`P = 1 + T + ⋯ + Tᵉ⁻¹` in the finite Fox rules (Lemma 5.4/5.5).  The `A`-offset of `pⁿ` is the
partial norm `(1 + g + ⋯ + gⁿ⁻¹) • u` of the offset `u` under the base action `g`. -/
theorem pow_u (p : WordLift A C) (n : ℕ) :
    (p ^ n).u = ∑ i ∈ Finset.range n, p.g ^ i • p.u := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, mul_u, ih, pow_g, Finset.sum_range_succ]

/-- **Norm collapse under a trivially-acting base** — the engine that flattens every `ω₂`-power in
the wild row once the wild inertia acts trivially.  If the base `p.g` acts trivially on the char-2
module `A`, the `A`-offset of the 2-primary part `p^{ω₂}` (`powOmega2`) is just `p.u`.

The `ω₂`-exponent `e = omega2Exp (orderOf p)` is *odd* exactly when `orderOf p` is even, which is
exactly when `p.u ≠ 0` (then `addOrderOf p.u = 2 ∣ orderOf p`); for odd `e` and a 2-torsion `p.u`,
`e • p.u = p.u`.  When `p.u = 0` both sides vanish, so the identity is uniform. -/
theorem powOmega2_u_of_trivial [Finite A] [Finite C] (hA₂ : ∀ a : A, a + a = 0)
    (p : WordLift A C) (hg : ∀ a : A, p.g • a = a) : (powOmega2 p).u = p.u := by
  have hpow : ∀ k : ℕ, (p ^ k).u = k • p.u := by
    intro k
    rw [pow_u]
    have hc : ∀ i, p.g ^ i • p.u = p.u := by
      intro i; induction i with
      | zero => simp
      | succ j ih => rw [pow_succ, mul_smul, hg, ih]
    simp only [hc, Finset.sum_const, Finset.card_range]
  rw [powOmega2, hpow]
  by_cases hpu : p.u = 0
  · simp [hpu]
  · have h2 : addOrderOf p.u = 2 := addOrderOf_eq_prime (by rw [two_nsmul]; exact hA₂ p.u) hpu
    have hN0 : orderOf p ≠ 0 := (orderOf_pos p).ne'
    have hdvd : (2 : ℕ) ∣ orderOf p := by
      have hz : (orderOf p) • p.u = 0 := by rw [← hpow (orderOf p), pow_orderOf_eq_one]; rfl
      rw [← h2]; exact addOrderOf_dvd_of_nsmul_eq_zero hz
    have hv : (orderOf p).factorization 2 ≠ 0 :=
      (Nat.Prime.factorization_pos_of_dvd Nat.prime_two hN0 hdvd).ne'
    have hodd : Odd (omega2Exp (orderOf p)) := by
      have h : omega2Exp (orderOf p) % 2 = 1 % 2 :=
        (omega2Exp_modEq_one hN0 hv).of_dvd (dvd_pow_self 2 hv)
      rw [Nat.odd_iff]; omega
    obtain ⟨m, hm⟩ := hodd
    rw [hm, add_nsmul, mul_nsmul, two_nsmul, hA₂, nsmul_zero, zero_add, one_nsmul]

end WordLift

/-! ## The word complex (30)/(31) -/

section WordComplex

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The lifted marking `((ρσ, a), (ρτ, b), (ρx₀, c), (ρx₁, d))` over `t` with offsets `x`. -/
def liftMarking (t : Marking C) (x : Fin 4 → A) : Marking (WordLift A C) :=
  ⟨⟨x 0, t.σ⟩, ⟨x 1, t.τ⟩, ⟨x 2, t.x₀⟩, ⟨x 3, t.x₁⟩⟩

/-- **`d⁰`** (display (31)): simultaneous infinitesimal conjugation,
`v ↦ ((S−1)v, (T−1)v, (X₀−1)v, (X₁−1)v)`. -/
def d0 (t : Marking C) : A →+ (Fin 4 → A) :=
  AddMonoidHom.mk' (fun v => ![t.σ • v - v, t.τ • v - v, t.x₀ • v - v, t.x₁ • v - v]) <| by
    intro v w
    funext i
    fin_cases i <;> · simp [smul_add]; abel

/-- **`d¹`, function level** (display (30)): the pair of `A`-coordinates of the evaluated tame
and wild relators at the lifted marking — "the coefficient of `A` in the evaluated relators". -/
noncomputable def d1Fun (t : Marking C) (x : Fin 4 → A) : A × A :=
  ((liftMarking t x).tameValue.u, (liftMarking t x).wildValue.u)

/-- **`d¹` is additive in the lift variables** — the paper's "finite Fox rules" linearity
(§5.1/§5.2, displays (36)–(37)).  Proof by *functoriality*: evaluate the relators over the
coefficient module `A × A`, then push the value through the three `C`-equivariant maps
`fst, snd, fst + snd : A × A →+ A` (`Marking.map_tameValue`/`map_wildValue` +
`WordLift.map`); the `u`-coordinates give `d1Fun` at `x`, `y`, and `x + y` respectively.

(Requires `A`, `C` finite: the wild relator's `ω₂`-powers only push through coefficient maps in
finite groups — `powOmega2_map`.  This is the paper's finite-word setting.) -/
theorem d1Fun_add [Finite A] [Finite C] (t : Marking C) (x y : Fin 4 → A) :
    d1Fun t (x + y) = d1Fun t x + d1Fun t y := by
  -- Coefficient maps `A × A →+ A`, all `C`-equivariant since the action is diagonal.
  have hfst : ∀ (g : C) (a : A × A),
      (AddMonoidHom.fst A A) (g • a) = g • (AddMonoidHom.fst A A) a := fun _ _ => rfl
  have hsnd : ∀ (g : C) (a : A × A),
      (AddMonoidHom.snd A A) (g • a) = g • (AddMonoidHom.snd A A) a := fun _ _ => rfl
  have hsum : ∀ (g : C) (a : A × A), (AddMonoidHom.fst A A + AddMonoidHom.snd A A) (g • a)
      = g • (AddMonoidHom.fst A A + AddMonoidHom.snd A A) a := by
    intro g a
    show (g • a).1 + (g • a).2 = g • (a.1 + a.2)
    rw [Prod.smul_fst, Prod.smul_snd, smul_add]
  set φ1 := WordLift.map (C := C) (AddMonoidHom.fst A A) hfst with hφ1
  set φ2 := WordLift.map (C := C) (AddMonoidHom.snd A A) hsnd with hφ2
  set φs := WordLift.map (C := C) (AddMonoidHom.fst A A + AddMonoidHom.snd A A) hsum with hφs
  -- The paired lift over `A × A` recovers the single-variable lifts after pushing through the maps.
  have hL1 : (liftMarking t (fun i => (x i, y i))).map φ1 = liftMarking t x := rfl
  have hL2 : (liftMarking t (fun i => (x i, y i))).map φ2 = liftMarking t y := rfl
  have hLs : (liftMarking t (fun i => (x i, y i))).map φs = liftMarking t (x + y) := rfl
  -- Both relator coordinates read off the paired value via `fst`, `snd`, `fst + snd`.
  refine Prod.ext ?_ ?_
  · show (liftMarking t (x + y)).tameValue.u
        = (liftMarking t x).tameValue.u + (liftMarking t y).tameValue.u
    rw [← hL1, ← hL2, ← hLs, Marking.map_tameValue, Marking.map_tameValue, Marking.map_tameValue,
      hφ1, hφ2, hφs, WordLift.map_u, WordLift.map_u, WordLift.map_u]
    rfl
  · show (liftMarking t (x + y)).wildValue.u
        = (liftMarking t x).wildValue.u + (liftMarking t y).wildValue.u
    rw [← hL1, ← hL2, ← hLs, Marking.map_wildValue, Marking.map_wildValue, Marking.map_wildValue,
      hφ1, hφ2, hφs, WordLift.map_u, WordLift.map_u, WordLift.map_u]
    rfl

/-- **`d¹`** (display (30)), bundled on `d1Fun_add` (finite coefficients, per `d1Fun_add`). -/
noncomputable def d1 [Finite A] [Finite C] (t : Marking C) : (Fin 4 → A) →+ A × A :=
  AddMonoidHom.mk' (d1Fun t) (d1Fun_add t)

/-- **(30) is a complex**: `d¹ ∘ d⁰ = 0` when the marking satisfies the two relations.
Proof: `liftMarking t (d0 t v)` is `t` pushed through `g ↦ ⟨g•v − v, g⟩ = ⟨v,1⟩⁻¹⟨0,g⟩⟨v,1⟩`
(conjugation of the base embedding), so its relator values are conjugates of `t`'s — which are
`1` by the relations — hence have zero `A`-coordinate. -/
theorem d1Fun_comp_d0 [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (v : A) : d1Fun t (d0 t v) = 0 := by
  -- Conjugation by `⟨v,1⟩`, an inner automorphism, composed with the base embedding.
  let φ : WordLift A C →* WordLift A C :=
    { toFun := fun x => (⟨v, 1⟩ : WordLift A C)⁻¹ * x * ⟨v, 1⟩
      map_one' := by group
      map_mul' := fun a b => by group }
  let ψ : C →* WordLift A C := φ.comp WordLift.baseEmbed
  have hψ : ∀ g : C, ψ g = ⟨g • v - v, g⟩ := fun g => WordLift.conj_baseEmbed v g
  -- The coboundary lift is `t` pushed through `ψ`.
  have hkey : liftMarking t (d0 t v) = t.map ψ := by
    simp only [liftMarking, Marking.map, hψ, Marking.mk.injEq]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> exact WordLift.ext (by simp [d0]) rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (d0 t v)).tameValue.u = (0 : A × A).1
    rw [hkey, Marking.map_tameValue, (Marking.tameValue_eq_one_iff t).mpr ht, map_one]
    rfl
  · show (liftMarking t (d0 t v)).wildValue.u = (0 : A × A).2
    rw [hkey, Marking.map_wildValue, (Marking.wildValue_eq_one_iff t).mpr hw, map_one]
    rfl

/-- `H⁰_{A,ρ}(A) = ker d⁰` (the `t`-invariants). -/
def H0w (t : Marking C) : AddSubgroup A := (d0 (A := A) t).ker

/-- `Z¹_{A,ρ}(A) = ker d¹` (display (30)'s degree-one kernel). -/
noncomputable def Z1w [Finite A] [Finite C] (t : Marking C) : AddSubgroup (Fin 4 → A) :=
  (d1 (A := A) t).ker

/-- `B¹_{A,ρ}(A) = im d⁰`. -/
def B1w (t : Marking C) : AddSubgroup (Fin 4 → A) := (d0 (A := A) t).range

/-- `H¹_{A,ρ}(A)` (as in `GQ2/Cohomology.lean`: the `addSubgroupOf`-quotient is total — the
chain inclusion `B¹ ≤ Z¹` is `d1Fun_comp_d0`, needed only for lemmas). -/
noncomputable def H1w [Finite A] [Finite C] (t : Marking C) : Type _ :=
  Z1w (A := A) t ⧸ (B1w (A := A) t).addSubgroupOf (Z1w (A := A) t)

noncomputable instance [Finite A] [Finite C] (t : Marking C) : AddCommGroup (H1w (A := A) t) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- The class of a degree-one cocycle in `H¹_{A,ρ}`. -/
noncomputable def h1wMk [Finite A] [Finite C] (t : Marking C) (x : Z1w (A := A) t) :
    H1w (A := A) t :=
  QuotientAddGroup.mk x

/-- `H²_{A,ρ}(A) = A² ⧸ im d¹`. -/
noncomputable def H2w [Finite A] [Finite C] (t : Marking C) : Type _ :=
  (A × A) ⧸ (d1 (A := A) t).range

noncomputable instance [Finite A] [Finite C] (t : Marking C) : AddCommGroup (H2w (A := A) t) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

/-- **The tame row of `d¹`, in closed form** — the general (pre-`𝔽₂`) form of display (34),
`D(τ^σ τ⁻²)(a, b) = S⁻¹(T−1)a + S⁻¹b − (1+T)b`, valid at a marking satisfying the tame
relation.  This is the P-12 stress test: it pins the lift convention, the `conjP` direction,
and the (30)-encoding against the paper's own computation (Lemma 5.5's proof). -/
theorem d1Fun_tame (t : Marking C) (ht : t.TameRel) (x : Fin 4 → A) :
    (d1Fun t x).1
      = t.σ⁻¹ • (t.τ • x 0) - t.σ⁻¹ • x 0 + t.σ⁻¹ • x 1 - (x 1 + t.τ • x 1) := by
  have hel : t.σ⁻¹ * t.τ * t.σ = t.τ * t.τ := by
    have h := ht
    rw [Marking.TameRel, conjP, pow_two] at h
    exact h
  simp only [d1Fun, Marking.tameValue, liftMarking, conjP, pow_two, WordLift.mul_u,
    WordLift.mul_g, WordLift.inv_u, WordLift.inv_g]
  rw [hel]
  rw [smul_neg, smul_inv_smul, mul_smul]
  abel

end WordComplex

/-! ## The `𝔽₂`-dual  (T-14's def-synonym recipe) -/

/-- The `𝔽₂`-dual `A^∨ = Hom(A, 𝔽₂)`, as a def-synonym (a plain abbrev would pick up
Mathlib's codomain-action instances — the T-14 diamond). -/
def ElemDual (A : Type*) [AddCommGroup A] : Type _ := A →+ ZMod 2

namespace ElemDual

variable {A : Type*} [AddCommGroup A]

noncomputable instance : AddCommGroup (ElemDual A) :=
  inferInstanceAs (AddCommGroup (A →+ ZMod 2))

instance : FunLike (ElemDual A) A (ZMod 2) :=
  inferInstanceAs (FunLike (A →+ ZMod 2) A (ZMod 2))

instance : AddMonoidHomClass (ElemDual A) A (ZMod 2) :=
  inferInstanceAs (AddMonoidHomClass (A →+ ZMod 2) A (ZMod 2))

instance [Finite A] : Finite (ElemDual A) :=
  Finite.of_injective (fun f : ElemDual A => (⇑f : A → ZMod 2)) DFunLike.coe_injective

@[ext] theorem ext {lam mu : ElemDual A} (h : ∀ a, lam a = mu a) : lam = mu :=
  DFunLike.ext _ _ h

@[simp] theorem zero_apply (a : A) : (0 : ElemDual A) a = 0 := rfl
@[simp] theorem add_apply (lam mu : ElemDual A) (a : A) : (lam + mu) a = lam a + mu a := rfl
@[simp] theorem neg_apply (lam : ElemDual A) (a : A) : (-lam) a = -(lam a) := rfl
@[simp] theorem sub_apply (lam mu : ElemDual A) (a : A) : (lam - mu) a = lam a - mu a := rfl

section Action

variable {C : Type*} [Group C] [DistribMulAction C A]

/-- The contragredient action `(g•λ)(a) = λ(g⁻¹•a)`. -/
noncomputable instance : DistribMulAction C (ElemDual A) where
  smul g lam :=
    ((lam : A →+ ZMod 2).comp (DistribSMul.toAddMonoidHom A (g⁻¹ : C)) : A →+ ZMod 2)
  one_smul lam := by
    ext a
    show lam ((1 : C)⁻¹ • a) = lam a
    rw [inv_one, one_smul]
  mul_smul g h lam := by
    ext a
    show lam ((g * h)⁻¹ • a) = lam (h⁻¹ • g⁻¹ • a)
    rw [mul_inv_rev, mul_smul]
  smul_zero g := by ext a; rfl
  smul_add g lam mu := by ext a; rfl

@[simp] theorem smul_apply (g : C) (lam : ElemDual A) (a : A) : (g • lam) a = lam (g⁻¹ • a) :=
  rfl

end Action

end ElemDual

/-- The evaluation pairing `A →+ A^∨ →+ 𝔽₂`, `(a, λ) ↦ λ(a)` (bundled for the T-04 cup
products; equivariant into the trivial module by contragredience). -/
noncomputable def dualEval (A : Type*) [AddCommGroup A] : A →+ ElemDual A →+ ZMod 2 :=
  AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun lam : ElemDual A => lam a) fun _ _ => rfl)
    fun a b => by ext lam; exact lam.map_add a b

@[simp] theorem dualEval_apply {A : Type*} [AddCommGroup A] (a : A) (lam : ElemDual A) :
    dualEval A a lam = lam a := rfl

/-! ## The Heisenberg lift group `H(A) ⋊ C`  (§5.2) -/

/-- `H(A) ⋊ C`: quadruples `(a, λ, z, g)` with the §5.2 multiplication
`(a,λ,z)(a',λ',z') = (a+a', λ+λ', z+z'+λ(a'))` twisted by the diagonal `C`-action.  The
central coordinate `z` is the carrier of the mixed derivatives. -/
@[ext] structure HeisLift (A C : Type*) [AddCommGroup A] where
  /-- The `A`-coordinate (the first derivative `D_u`). -/
  a : A
  /-- The dual coordinate (`D^∨_u`). -/
  l : ElemDual A
  /-- The central coordinate (`β_u`). -/
  z : ZMod 2
  /-- The base value in `C`. -/
  g : C

namespace HeisLift

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

noncomputable instance : One (HeisLift A C) := ⟨⟨0, 0, 0, 1⟩⟩
noncomputable instance : Mul (HeisLift A C) :=
  ⟨fun p q => ⟨p.a + p.g • q.a, p.l + p.g • q.l, p.z + q.z + p.l (p.g • q.a), p.g * q.g⟩⟩
noncomputable instance : Inv (HeisLift A C) :=
  ⟨fun p => ⟨-(p.g⁻¹ • p.a), -(p.g⁻¹ • p.l), p.z + p.l p.a, p.g⁻¹⟩⟩

omit [DistribMulAction C A] in
@[simp] theorem one_a : (1 : HeisLift A C).a = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_l : (1 : HeisLift A C).l = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_z : (1 : HeisLift A C).z = 0 := rfl

omit [DistribMulAction C A] in
@[simp] theorem one_g : (1 : HeisLift A C).g = 1 := rfl

@[simp] theorem mul_a (p q : HeisLift A C) : (p * q).a = p.a + p.g • q.a := rfl
@[simp] theorem mul_l (p q : HeisLift A C) : (p * q).l = p.l + p.g • q.l := rfl
@[simp] theorem mul_z (p q : HeisLift A C) : (p * q).z = p.z + q.z + p.l (p.g • q.a) := rfl
@[simp] theorem mul_g (p q : HeisLift A C) : (p * q).g = p.g * q.g := rfl
@[simp] theorem inv_a (p : HeisLift A C) : p⁻¹.a = -(p.g⁻¹ • p.a) := rfl
@[simp] theorem inv_l (p : HeisLift A C) : p⁻¹.l = -(p.g⁻¹ • p.l) := rfl
@[simp] theorem inv_z (p : HeisLift A C) : p⁻¹.z = p.z + p.l p.a := rfl
@[simp] theorem inv_g (p : HeisLift A C) : p⁻¹.g = p.g⁻¹ := rfl

noncomputable instance : Group (HeisLift A C) where
  mul_assoc p q r := by
    ext
    · simp only [mul_a, mul_g, smul_add, mul_smul, add_assoc]
    · simp only [mul_l, mul_g, smul_add, mul_smul, add_assoc]
    · simp only [mul_z, mul_a, mul_l, mul_g, ElemDual.add_apply, ElemDual.smul_apply,
        map_add, smul_add, mul_smul, inv_smul_smul]
      ring
    · simp only [mul_g, mul_assoc]
  one_mul p := by ext <;> simp
  mul_one p := by ext <;> simp
  inv_mul_cancel p := by
    ext
    · simp
    · simp only [mul_l, inv_l, inv_g, one_l, neg_add_cancel]
    · simp only [mul_z, inv_z, inv_l, inv_g, one_z, ElemDual.neg_apply,
        ElemDual.smul_apply, inv_inv, smul_inv_smul]
      linear_combination CharTwo.add_self_eq_zero p.z
    · simp

/-- `H(A) ⋊ C` is finite when `A` and `C` are (all four coordinates range over finite types). -/
instance [Finite A] [Finite C] : Finite (HeisLift A C) :=
  Finite.of_injective (fun p : HeisLift A C => (p.a, p.l, p.z, p.g)) fun p q h => by
    obtain ⟨pa, pl, pz, pg⟩ := p; obtain ⟨qa, ql, qz, qg⟩ := q; simpa using h

/-- The base projection `HeisLift A C →* C`. -/
def gHom : HeisLift A C →* C where
  toFun := HeisLift.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem gHom_apply (p : HeisLift A C) : gHom p = p.g := rfl

/-- The central element `⟨0, 0, w, 1⟩` (the paper's `z(w)`).  It is genuinely central. -/
noncomputable def zc (w : ZMod 2) : HeisLift A C := ⟨0, 0, w, 1⟩

@[simp] theorem zc_z (w : ZMod 2) : (zc (A := A) (C := C) w).z = w := rfl

@[simp] theorem zc_zero : zc (A := A) (C := C) (0 : ZMod 2) = 1 := rfl

theorem mul_zc (p : HeisLift A C) (w : ZMod 2) : p * zc w = ⟨p.a, p.l, p.z + w, p.g⟩ := by
  ext <;> simp [zc, mul_a, mul_l, mul_z, mul_g]

@[simp] theorem mul_zc_z (p : HeisLift A C) (w : ZMod 2) : (p * zc w).z = p.z + w := by
  rw [mul_zc]

/-- `zc` is additive in its argument: `z(u+v) = z(u)·z(v)`. -/
theorem zc_add (u v : ZMod 2) : zc (A := A) (C := C) (u + v) = zc u * zc v := by
  ext <;> simp [zc, mul_a, mul_l, mul_z, mul_g, ElemDual.zero_apply]

/-- `zc w` is central in `H(A) ⋊ C`. -/
theorem zc_comm (w : ZMod 2) (q : HeisLift A C) : zc w * q = q * zc w := by
  ext <;> simp [zc, mul_a, mul_l, mul_z, mul_g, ElemDual.zero_apply, one_smul, smul_zero, add_comm]

/-- The central factor `z(·)` as a homomorphism `Multiplicative (ZMod 2) →* H(A) ⋊ C`. -/
noncomputable def zcHom : Multiplicative (ZMod 2) →* HeisLift A C where
  toFun w := zc (Multiplicative.toAdd w)
  map_one' := rfl
  map_mul' _ _ := zc_add _ _

@[simp] theorem zcHom_apply (w : Multiplicative (ZMod 2)) :
    zcHom (A := A) (C := C) w = zc (Multiplicative.toAdd w) := rfl

/-- The image of `zcHom` is central. -/
theorem zcHom_comm (v : Multiplicative (ZMod 2)) (q : HeisLift A C) :
    zcHom v * q = q * zcHom v := zc_comm _ _

/-- **The conjugation computation** `p_a⁻¹ · ⟨0,λ,0,g⟩ · p_a = ⟨g·a − a, λ, λ(g·a), g⟩`, where
`p_a = ⟨a,0,0,1⟩`.  This is the algebraic heart of Lemma 5.7's left form: conjugating a
`g=1`-slot generator by the `A`-translation `p_a` shifts its `A`-coordinate by the coboundary
`g·a − a` and drops the central defect `λ(g·a)`. -/
theorem conj_gen (a : A) (lam : ElemDual A) (g : C) :
    (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ * ⟨0, lam, 0, g⟩ * ⟨a, 0, 0, 1⟩
      = ⟨g • a - a, lam, lam (g • a), g⟩ := by
  have hinv : (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ = ⟨-a, 0, 0, 1⟩ := by
    ext <;> simp [inv_a, inv_l, inv_z, inv_g, ElemDual.zero_apply]
  rw [hinv]
  ext
  · simp only [mul_a, mul_g, smul_zero, one_mul, add_zero]; abel
  · simp [mul_l, mul_g, one_smul, smul_zero, one_mul, add_zero]
  · simp [mul_z, mul_l, mul_g, one_smul, smul_zero, one_mul, add_zero, zero_add,
      ElemDual.zero_apply]
  · simp [mul_g, one_mul, mul_one]

/-- **The dual conjugation computation** `q_λ⁻¹ · ⟨a,0,0,g⟩ · q_λ = ⟨a, g·λ − λ, −λ(a), g⟩`, where
`q_λ = ⟨0,λ,0,1⟩`.  This is the algebraic heart of Lemma 5.7's right form: conjugating a
`g=1`-slot generator by the dual translation `q_λ` shifts its dual coordinate by the coboundary
`g·λ − λ` and records the central defect `−λ(a)`. -/
theorem conj_gen_r (a : A) (lam : ElemDual A) (g : C) :
    (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ * ⟨a, 0, 0, g⟩ * ⟨0, lam, 0, 1⟩
      = ⟨a, g • lam - lam, -(lam a), g⟩ := by
  have hinv : (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ = ⟨0, -lam, 0, 1⟩ := by
    ext <;> simp [inv_a, inv_l, inv_z, inv_g, map_zero]
  rw [hinv]
  ext
  · simp [mul_a, mul_g, one_smul, smul_zero, one_mul, add_zero, zero_add]
  · simp only [mul_l, mul_g, smul_zero, one_mul, add_zero]; abel
  · simp [mul_z, mul_l, mul_g, one_smul, smul_zero, one_mul, add_zero, zero_add,
      map_zero, ElemDual.neg_apply]
  · simp [mul_g, one_mul, mul_one]

/-- **The Heisenberg commutator central coordinate (symplectic `B`-form)**, in the `g = 1` fiber
`H(A) = A × A^∨ × 𝔽₂`.  For `p, q` with trivial base value, the central coordinate of the
commutator `[p,q] = p⁻¹q⁻¹pq` is the alternating pairing `p.l(q.a) + q.l(p.a)` (the sign is
absorbed in char 2).  This is the extraspecial/Heisenberg central kernel `B` of Lemma 5.14: it
supplies the `[d₀,z₀]` mixed contribution `λ(U⁻¹c) + (U^∨λ)(c) = λ((U⁻¹+U)c)`. -/
theorem commP_z_fiber (p q : HeisLift A C) (hp : p.g = 1) (hq : q.g = 1) :
    (commP p q).z = p.l (q.a) + q.l (p.a) := by
  simp only [commP, mul_z, mul_a, mul_l, mul_g, inv_z, inv_a, inv_l, inv_g, hp, hq,
    inv_one, one_smul, one_mul, mul_one, map_neg, map_add, smul_zero, add_zero, zero_add,
    ElemDual.add_apply, ElemDual.neg_apply]
  -- What remains is a linear identity over `ZMod 2` in the six atomic central values;
  -- generalise them and decide the `2⁶` cases.
  generalize p.z = a1; generalize q.z = a2; generalize p.l p.a = a3
  generalize q.l q.a = a4; generalize p.l q.a = a5; generalize q.l p.a = a6
  revert a1 a2 a3 a4 a5 a6; decide

end HeisLift

section Mixed

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The Heisenberg-lifted marking over `t` with offsets `x` and dual offsets `y`. -/
noncomputable def heisMarking (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    Marking (HeisLift A C) :=
  ⟨⟨x 0, y 0, 0, t.σ⟩, ⟨x 1, y 1, 0, t.τ⟩, ⟨x 2, y 2, 0, t.x₀⟩, ⟨x 3, y 3, 0, t.x₁⟩⟩

/-- **`B_{ρ,A}`** (Prop 5.8): the *traced* mixed central coordinate — the sum of the central
coordinates of the two evaluated relators (not the central coordinate of their product). -/
noncomputable def mixedB (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) : ZMod 2 :=
  ((heisMarking t x y).tameValue).z + ((heisMarking t x y).wildValue).z

end Mixed

/-! ## Lemma 5.7: the finite-word Stokes formula (general form) -/

section Stokes

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A] {n : ℕ}

/-- Evaluation of an ordinary free-group word after the substitution
`gᵢ ↦ (xᵢ, yᵢ, 0; cᵢ) ∈ H(A) ⋊ C`  (Lemma 5.7). -/
noncomputable def stokesEval (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A) :
    FreeGroup (Fin n) →* HeisLift A C :=
  FreeGroup.lift fun i => ⟨x i, y i, 0, c i⟩

/-- The mod-2 total exponent `ε_i(r)` of the `i`-th generator in an ordinary word. -/
def expMod2 {n : ℕ} (i : Fin n) : FreeGroup (Fin n) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun j => Multiplicative.ofAdd (if j = i then 1 else 0)

/-- The base coordinate of a Stokes evaluation is the underlying word value in `C`. -/
@[simp] theorem stokesEval_g (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A)
    (r : FreeGroup (Fin n)) : (stokesEval c x y r).g = FreeGroup.lift c r := by
  have h : (HeisLift.gHom).comp (stokesEval c x y) = FreeGroup.lift c :=
    FreeGroup.ext_hom _ _ fun i => rfl
  exact DFunLike.congr_fun h r

/-- With zero `A`-offsets, the `A`- and central coordinates of a Stokes evaluation vanish (the
elements `⟨0, λ, 0, g⟩` form a subgroup on which the central defect is inert). -/
theorem stokesEval_zero (c : Fin n → C) (y : Fin n → ElemDual A) (r : FreeGroup (Fin n)) :
    (stokesEval c 0 y r).a = 0 ∧ (stokesEval c 0 y r).z = 0 := by
  refine FreeGroup.induction_on r ⟨rfl, rfl⟩ (fun i => ⟨by simp [stokesEval], by simp [stokesEval]⟩)
    (fun i ih => ?_) (fun x₁ x₂ ih₁ ih₂ => ?_)
  · rw [map_inv]
    exact ⟨by rw [HeisLift.inv_a, ih.1, smul_zero, neg_zero],
      by rw [HeisLift.inv_z, ih.2, ih.1, map_zero, add_zero]⟩
  · rw [map_mul]
    exact ⟨by rw [HeisLift.mul_a, ih₁.1, ih₂.1, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih₁.2, ih₂.2, ih₂.1, smul_zero, map_zero, add_zero, add_zero]⟩

/-! ### The conjugation model of the coboundary evaluation (Lemma 5.7, left form)

The generic coboundary substitution `x = d⁰a` factors, one generator at a time, as
`⟨cᵢa−a, yᵢ, 0, cᵢ⟩ = p_a⁻¹ · ⟨0, yᵢ, 0, cᵢ⟩ · p_a · z(yᵢ(cᵢa))`  (with `p_a = ⟨a,0,0,1⟩`).
Because `z(·)` is central, the per-generator central factors telescope into a single
`z(Σᵢ εᵢ(r)·yᵢ(cᵢa))`, and the conjugation commutes with word evaluation.  This makes
`stokesEval c (d⁰a) y = conjPa a ∘ stokesEval c 0 y  ·  z ∘ epsWord` an identity of homomorphisms,
which we prove by `FreeGroup.ext_hom` and then read off the `z`-coordinate. -/

/-- Conjugation `q ↦ p_a⁻¹ · q · p_a` by the `A`-translation `p_a = ⟨a,0,0,1⟩`, as a group hom. -/
noncomputable def conjPa (a : A) : HeisLift A C →* HeisLift A C where
  toFun q := (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨a, 0, 0, 1⟩
  map_one' := by group
  map_mul' q q' := by group

@[simp] theorem conjPa_apply (a : A) (q : HeisLift A C) :
    conjPa a q = (⟨a, 0, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨a, 0, 0, 1⟩ := rfl

/-- The `z`-coordinate of `p_a⁻¹ · q · p_a` when `q` sits in the `g`-slice (`q.a = 0`, `q.z = 0`):
conjugation records the central defect `q.l (q.g · a)`. -/
theorem conjPa_z (a : A) (q : HeisLift A C) (ha : q.a = 0) (hz : q.z = 0) :
    (conjPa a q).z = q.l (q.g • a) := by
  obtain ⟨qa, ql, qz, qg⟩ := q
  subst ha; subst hz
  rw [conjPa_apply, HeisLift.conj_gen]

/-- The **central exponent word** `r ↦ ∏ᵢ z(εᵢ(r)·fᵢ)` for a mod-2 coefficient vector `f`,
packaged as a hom to `Multiplicative (ZMod 2)` so that `z ∘ freeExp f` is the telescoped
central factor of a Stokes evaluation. -/
noncomputable def freeExp (f : Fin n → ZMod 2) : FreeGroup (Fin n) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift fun i => Multiplicative.ofAdd (f i)

/-- The additive value of `freeExp f` is the ε-counting sum `Σᵢ εᵢ(r)·fᵢ` (mod 2): each generator
`i` contributes `fᵢ` once per occurrence, so mod 2 exactly `εᵢ(r)` times. -/
theorem freeExp_toAdd (f : Fin n → ZMod 2) (r : FreeGroup (Fin n)) :
    Multiplicative.toAdd (freeExp f r) = ∑ i, Multiplicative.toAdd (expMod2 i r) * f i := by
  refine FreeGroup.induction_on r ?_ ?_ ?_ ?_
  · simp [freeExp, expMod2]
  · intro k
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)]
    · simp [freeExp, expMod2, FreeGroup.lift_apply_of]
    · intro i _ hik
      simp [expMod2, FreeGroup.lift_apply_of, if_neg (Ne.symm hik)]
  · intro k ih
    simp only [map_inv, toAdd_inv, CharTwo.neg_eq]
    exact ih
  · intro x1 x2 ih1 ih2
    simp only [map_mul, toAdd_mul, add_mul, Finset.sum_add_distrib, ih1, ih2]

/-- The **central ε-word** of the left form: `r ↦ ∏ᵢ z(εᵢ(r)·yᵢ(cᵢa))`. -/
noncomputable def epsWord (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) :
    FreeGroup (Fin n) →* Multiplicative (ZMod 2) :=
  freeExp (fun i => y i (c i • a))

/-- `epsWord`'s additive value is the ε-counting sum `Σᵢ εᵢ(r)·yᵢ(cᵢa)` (mod 2). -/
theorem epsWord_toAdd (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) (r : FreeGroup (Fin n)) :
    Multiplicative.toAdd (epsWord c a y r)
      = ∑ i, Multiplicative.toAdd (expMod2 i r) * (y i (c i • a)) :=
  freeExp_toAdd _ r

/-- The RHS conjugation model of `stokesEval c (d⁰a) y`: conjugate the `y`-only evaluation by
`p_a` and multiply by the telescoped central factor. -/
noncomputable def stokesRhs (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) :
    FreeGroup (Fin n) →* HeisLift A C where
  toFun w := conjPa a (stokesEval c 0 y w) * HeisLift.zcHom (epsWord c a y w)
  map_one' := by simp
  map_mul' w w' := by
    simp only [map_mul]
    set A1 := conjPa a (stokesEval c 0 y w) with hA1
    set A2 := conjPa a (stokesEval c 0 y w') with hA2
    set B1 : HeisLift A C := HeisLift.zcHom (epsWord c a y w) with hB1
    set B2 : HeisLift A C := HeisLift.zcHom (epsWord c a y w') with hB2
    have hc : B1 * A2 = A2 * B1 := HeisLift.zcHom_comm (epsWord c a y w) A2
    rw [mul_assoc A1 A2 (B1 * B2), ← mul_assoc A2 B1 B2, ← hc, mul_assoc B1 A2 B2,
      ← mul_assoc A1 B1 (A2 * B2)]

/-- **The Lemma 5.7 factorization** (identity of homomorphisms): `stokesEval` at the coboundary
`d⁰a` equals `conjPa a` of the `y`-only evaluation, corrected by the central ε-word. -/
theorem stokesEval_eq_rhs (c : Fin n → C) (a : A) (y : Fin n → ElemDual A) :
    stokesEval c (fun i => c i • a - a) y = stokesRhs c a y := by
  refine FreeGroup.ext_hom _ _ (fun i => ?_)
  have hE : stokesEval c (fun i => c i • a - a) y (FreeGroup.of i) = ⟨c i • a - a, y i, 0, c i⟩ := by
    simp [stokesEval, FreeGroup.lift_apply_of]
  have hE0 : stokesEval c 0 y (FreeGroup.of i) = ⟨0, y i, 0, c i⟩ := by
    simp [stokesEval, FreeGroup.lift_apply_of]
  have heps : epsWord c a y (FreeGroup.of i) = Multiplicative.ofAdd (y i (c i • a)) := by
    simp [epsWord, freeExp, FreeGroup.lift_apply_of]
  show stokesEval c (fun i => c i • a - a) y (FreeGroup.of i)
      = conjPa a (stokesEval c 0 y (FreeGroup.of i)) * HeisLift.zcHom (epsWord c a y (FreeGroup.of i))
  rw [hE, hE0, heps, conjPa_apply, HeisLift.conj_gen, HeisLift.zcHom_apply, toAdd_ofAdd,
    HeisLift.mul_zc, CharTwo.add_self_eq_zero]

/-- **Lemma 5.7, display (38)**: for a word `r` with trivial lower value, evaluating at the
generic coboundary `x = d⁰a = ((cᵢ−1)a)ᵢ` gives
`β_r(d⁰a, y) = ⟨a, L^{A^∨}_r(y)⟩ + Σᵢ εᵢ(r)·yᵢ(cᵢa)`. -/
theorem lemma_5_7_left (c : Fin n → C) (r : FreeGroup (Fin n))
    (hr : FreeGroup.lift c r = 1) (a : A) (y : Fin n → ElemDual A) :
    (stokesEval c (fun i => c i • a - a) y r).z
      = (stokesEval c 0 y r).l a
        + ∑ i, (Multiplicative.toAdd (expMod2 i r)) * (y i (c i • a)) := by
  rw [stokesEval_eq_rhs c a y]
  show (conjPa a (stokesEval c 0 y r) * HeisLift.zcHom (epsWord c a y r)).z = _
  rw [HeisLift.zcHom_apply, HeisLift.mul_zc_z, epsWord_toAdd]
  have hg : (stokesEval c 0 y r).g = 1 := by rw [stokesEval_g]; exact hr
  rw [conjPa_z a _ (stokesEval_zero c y r).1 (stokesEval_zero c y r).2, hg, one_smul]

/-! ### The dual conjugation model (Lemma 5.7, right form)

The dual coboundary substitution `y = d⁰λ` factors, one generator at a time, as
`⟨xᵢ, cᵢλ−λ, 0, cᵢ⟩ = q_λ⁻¹ · ⟨xᵢ, 0, 0, cᵢ⟩ · q_λ · z(λ(xᵢ))`  (with `q_λ = ⟨0,λ,0,1⟩`),
mirroring the left form with the roles of the `A`- and dual coordinates exchanged. -/

/-- Conjugation `q ↦ q_λ⁻¹ · q · q_λ` by the dual translation `q_λ = ⟨0,λ,0,1⟩`. -/
noncomputable def conjQlam (lam : ElemDual A) : HeisLift A C →* HeisLift A C where
  toFun q := (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨0, lam, 0, 1⟩
  map_one' := by group
  map_mul' q q' := by group

@[simp] theorem conjQlam_apply (lam : ElemDual A) (q : HeisLift A C) :
    conjQlam lam q = (⟨0, lam, 0, 1⟩ : HeisLift A C)⁻¹ * q * ⟨0, lam, 0, 1⟩ := rfl

/-- The `z`-coordinate of `q_λ⁻¹ · q · q_λ` when `q` sits in the `g`-slice (`q.l = 0`, `q.z = 0`):
conjugation records the central defect `λ(q.a)` (the sign is absorbed mod 2). -/
theorem conjQlam_z (lam : ElemDual A) (q : HeisLift A C) (hl : q.l = 0) (hz : q.z = 0) :
    (conjQlam lam q).z = lam q.a := by
  obtain ⟨qa, ql, qz, qg⟩ := q
  subst hl; subst hz
  rw [conjQlam_apply, HeisLift.conj_gen_r]
  exact CharTwo.neg_eq _

/-- With zero dual offsets, the dual- and central coordinates of a Stokes evaluation vanish. -/
theorem stokesEval_zero_r (c : Fin n → C) (x : Fin n → A) (r : FreeGroup (Fin n)) :
    (stokesEval c x 0 r).l = 0 ∧ (stokesEval c x 0 r).z = 0 := by
  refine FreeGroup.induction_on r ⟨rfl, rfl⟩ (fun i => ⟨by simp [stokesEval], by simp [stokesEval]⟩)
    (fun i ih => ?_) (fun x₁ x₂ ih₁ ih₂ => ?_)
  · rw [map_inv]
    exact ⟨by rw [HeisLift.inv_l, ih.1, smul_zero, neg_zero],
      by rw [HeisLift.inv_z, ih.2, ih.1, ElemDual.zero_apply, add_zero]⟩
  · rw [map_mul]
    exact ⟨by rw [HeisLift.mul_l, ih₁.1, ih₂.1, smul_zero, add_zero],
      by rw [HeisLift.mul_z, ih₁.2, ih₂.2, ih₁.1, ElemDual.zero_apply, add_zero, add_zero]⟩

/-- The RHS conjugation model of `stokesEval c x (d⁰λ)` (dual form). -/
noncomputable def stokesRhsR (c : Fin n → C) (lam : ElemDual A) (x : Fin n → A) :
    FreeGroup (Fin n) →* HeisLift A C where
  toFun w := conjQlam lam (stokesEval c x 0 w) * HeisLift.zcHom (freeExp (fun i => lam (x i)) w)
  map_one' := by simp
  map_mul' w w' := by
    simp only [map_mul]
    set A1 := conjQlam lam (stokesEval c x 0 w) with hA1
    set A2 := conjQlam lam (stokesEval c x 0 w') with hA2
    set B1 : HeisLift A C := HeisLift.zcHom (freeExp (fun i => lam (x i)) w) with hB1
    set B2 : HeisLift A C := HeisLift.zcHom (freeExp (fun i => lam (x i)) w') with hB2
    have hc : B1 * A2 = A2 * B1 := HeisLift.zcHom_comm (freeExp (fun i => lam (x i)) w) A2
    rw [mul_assoc A1 A2 (B1 * B2), ← mul_assoc A2 B1 B2, ← hc, mul_assoc B1 A2 B2,
      ← mul_assoc A1 B1 (A2 * B2)]

/-- **The Lemma 5.7 factorization** (dual form): `stokesEval` at the dual coboundary `d⁰λ` equals
`conjQlam lam` of the `x`-only evaluation, corrected by the central ε-word. -/
theorem stokesEval_eq_rhsR (c : Fin n → C) (lam : ElemDual A) (x : Fin n → A) :
    stokesEval c x (fun i => c i • lam - lam) = stokesRhsR c lam x := by
  refine FreeGroup.ext_hom _ _ (fun i => ?_)
  have hE : stokesEval c x (fun i => c i • lam - lam) (FreeGroup.of i)
      = ⟨x i, c i • lam - lam, 0, c i⟩ := by simp [stokesEval, FreeGroup.lift_apply_of]
  have hE0 : stokesEval c x 0 (FreeGroup.of i) = ⟨x i, 0, 0, c i⟩ := by
    simp [stokesEval, FreeGroup.lift_apply_of]
  have heps : freeExp (fun i => lam (x i)) (FreeGroup.of i) = Multiplicative.ofAdd (lam (x i)) := by
    simp [freeExp, FreeGroup.lift_apply_of]
  show stokesEval c x (fun i => c i • lam - lam) (FreeGroup.of i)
      = conjQlam lam (stokesEval c x 0 (FreeGroup.of i))
        * HeisLift.zcHom (freeExp (fun i => lam (x i)) (FreeGroup.of i))
  rw [hE, hE0, heps, conjQlam_apply, HeisLift.conj_gen_r, HeisLift.zcHom_apply, toAdd_ofAdd,
    HeisLift.mul_zc, neg_add_cancel]

/-- **Lemma 5.7, display (39)**: the dual-variable form,
`β_r(x, d⁰λ) = ⟨L^A_r(x), λ⟩ + Σᵢ εᵢ(r)·λ(xᵢ)`.  (The lower-value hypothesis `hr` is recorded for
symmetry with the left form; the dual central defect is `g`-independent, so it is not needed here.) -/
theorem lemma_5_7_right (c : Fin n → C) (r : FreeGroup (Fin n))
    (_hr : FreeGroup.lift c r = 1) (x : Fin n → A) (lam : ElemDual A) :
    (stokesEval c x (fun i => c i • lam - lam) r).z
      = lam ((stokesEval c x 0 r).a)
        + ∑ i, (Multiplicative.toAdd (expMod2 i r)) * (lam (x i)) := by
  rw [stokesEval_eq_rhsR c lam x]
  show (conjQlam lam (stokesEval c x 0 r)
    * HeisLift.zcHom (freeExp (fun i => lam (x i)) r)).z = _
  rw [HeisLift.zcHom_apply, HeisLift.mul_zc_z, freeExp_toAdd,
    conjQlam_z lam _ (stokesEval_zero_r c x r).1 (stokesEval_zero_r c x r).2]

/-- The free-group tame word `τ^σ · (τ²)⁻¹` on four letters (for the exponent stress test). -/
def fgTame : FreeGroup (Fin 4) :=
  conjP (FreeGroup.of 1) (FreeGroup.of 0) * (FreeGroup.of 1 ^ 2)⁻¹

/-- **Stress test** (Prop 5.8's proof, exponent claim): the tame word's mod-2 exponent vector
is `(0, 1, 0, 0)` — odd total `τ`-exponent, even everything else. -/
theorem expMod2_fgTame :
    (fun i => Multiplicative.toAdd (expMod2 i fgTame)) = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;>
  · simp only [fgTame, expMod2, conjP, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of]
    decide

end Stokes

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
  have hN : Monoid.exponent G ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have hsig : powOmega2 t.σ = t.σ ^ omega2Exp (Monoid.exponent G) :=
    (powOmega2_pow_eq t.σ (Monoid.order_dvd_exponent t.σ) hN).symm
  have hu0 : powOmega2 (t.x₀ * t.τ) = (t.x₀ * t.τ) ^ omega2Exp (Monoid.exponent G) :=
    (powOmega2_pow_eq _ (Monoid.order_dvd_exponent _) hN).symm
  have hu1 : powOmega2 (t.x₁ * t.τ) = (t.x₁ * t.τ) ^ omega2Exp (Monoid.exponent G) :=
    (powOmega2_pow_eq _ (Monoid.order_dvd_exponent _) hN).symm
  simp only [Marking.wildValue, Marking.h0, Marking.c0, Marking.dg, Marking.hc, Marking.z0,
    Marking.g0, Marking.d0, Marking.u1, Marking.u0, Marking.u, Marking.sigma2, wildValueExp,
    hsig, hu0, hu1]

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
  map_mul' g g' := by
    ext <;> simp [HeisLift.mul_a, HeisLift.mul_l, HeisLift.mul_z, HeisLift.mul_g,
      ElemDual.zero_apply]

theorem secHom_injective : Function.Injective (secHom (A := A) (C := C)) :=
  fun _ _ h => congrArg HeisLift.g h

/-- The section `⟨λ,g⟩ ↦ ⟨0,λ,0,g⟩ : A^∨ ⋊ C →* H(A) ⋊ C` (injective). -/
noncomputable def secWL : WordLift (ElemDual A) C →* HeisLift A C where
  toFun p := ⟨0, p.u, 0, p.g⟩
  map_one' := rfl
  map_mul' p q := by
    ext <;> simp [HeisLift.mul_a, HeisLift.mul_l, HeisLift.mul_z, HeisLift.mul_g,
      WordLift.mul_u, WordLift.mul_g, ElemDual.zero_apply]

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
theorem hr_wild [Finite A] [Finite C] (t : Marking C) (hw : t.WildRel) :
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
    lemma_5_7_left (markVec t) _ (hr_wild t hw) a y]
  congr 1
  · rw [stokesEval_wild_l]; rfl
  · have hvec : ∀ i, Multiplicative.toAdd
        (expMod2 i (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
        = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i := by
      intro i
      rw [congrFun (expMod2_wildValueExp _) i]
      have hc := omega2Exp_exponent_heis_cast (A := A) (C := C)
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, hc] <;> decide
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
  map_mul' p q := by
    ext <;> simp [HeisLift.mul_a, HeisLift.mul_l, HeisLift.mul_z, HeisLift.mul_g,
      WordLift.mul_u, WordLift.mul_g, ElemDual.zero_apply]

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
  rw [bridge_wild, d0_eq_markVec, lemma_5_7_right (markVec t) _ (hr_wild t hw) x lam]
  congr 1
  · rw [stokesEval_wild_a]; rfl
  · have hvec : ∀ i, Multiplicative.toAdd
        (expMod2 i (wildValueExp freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
        = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i := by
      intro i
      rw [congrFun (expMod2_wildValueExp _) i]
      have hc := omega2Exp_exponent_heis_cast (A := A) (C := C)
      fin_cases i <;>
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons, hc] <;> decide
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
        ⟨by simp only [Prod.fst_mul, Prod.snd_mul, HeisLift.mul_a, map_add, hf, hP.1, hQ.1, hP.2.2.2],
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

/-- **Lemma 5.11 (exact cone dévissage)**, stated as its consequence: along a short exact
sequence of finite elementary `𝔽₂[C]`-modules, self-duality satisfies two-out-of-three.  The
mapping cone `K(A)` of display (49) and the degreewise sequence (50) are the *proof* device
(P-13); acyclicity of `K(·)` is equivalent to the `IsSelfDual` package.

*Status*: sorried (P-13). -/
theorem lemma_5_11 {A' A'' : Type*} [AddCommGroup A'] [DistribMulAction C A']
    [AddCommGroup A''] [DistribMulAction C A''] [Finite A'] [Finite A] [Finite A'']
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hA₂ : ∀ a : A, a + a = 0)
    (f : A' →+ A) (g : A →+ A'')
    (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a)
    (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : f.range = g.ker) :
    (IsSelfDual t A' ∧ IsSelfDual t A'' → IsSelfDual t A) ∧
    (IsSelfDual t A' ∧ IsSelfDual t A → IsSelfDual t A'') ∧
    (IsSelfDual t A ∧ IsSelfDual t A'' → IsSelfDual t A') := by
  sorry

/-- Simplicity of a `𝔽₂[C]`-module, subgroup form: nonzero, and the only `C`-stable additive
subgroups are `⊥` and `⊤` (no `Module` instances, per the repo convention). -/
def IsSimpleModTwo (C : Type*) [Group C] (V : Type*) [AddCommGroup V]
    [DistribMulAction C V] : Prop :=
  Nontrivial V ∧
    ∀ W : AddSubgroup V, (∀ (g : C) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤

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
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial V := hsimple.1
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

section NormalForms

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- The degree-one tuple supported on the `x₀`-slot (display (53)'s normal form). -/
def x0Supported (c : V) : Fin 4 → V := ![0, 0, c, 0]

/-- **The marked wild generators act trivially on a simple module** — the admissibility input the
normal-form and pairing lemmas below need.  This is the paper's Lemma 5.12 ("simple char-2 modules
are tame") applied to the normal 2-subgroup `L = ⟨⟨x₀, x₁⟩⟩`: `L` is normal (a normal closure) and
a 2-group (the `Pro2Core` clause `hcore`), and contains `x₀, x₁`. -/
theorem wild_acts_trivially (t : Marking C) [Finite V]
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) (hcore : t.Pro2Core) :
    (∀ v : V, t.x₀ • v = v) ∧ (∀ v : V, t.x₁ • v = v) := by
  have htriv := lemma_5_12 hV₂ hsimple (Subgroup.normalClosure {t.x₀, t.x₁})
    Subgroup.normalClosure_normal hcore
  exact ⟨htriv t.x₀ (Subgroup.subset_normalClosure (by simp)),
    htriv t.x₁ (Subgroup.subset_normalClosure (by simp))⟩

omit [Finite C] in
/-- **The tame row in the split case, closed form** (unconditional — needs only `T = 1` and char
2, no wild-core input): `L_t(x) = S⁻¹·x₁`.  This is the `x 1 = 0` half of `lemma_5_13_split`'s
`Z¹` description, and holds verbatim from the general tame row `d1Fun_tame` with `T = 1`. -/
theorem d1Fun_tame_split (t : Marking C) (ht : t.TameRel) (htau : ∀ v : V, t.τ • v = v)
    (hV₂ : ∀ v : V, v + v = 0) (x : Fin 4 → V) :
    (d1Fun t x).1 = t.σ⁻¹ • x 1 := by
  rw [d1Fun_tame t ht x, htau (x 0), htau (x 1), sub_self, zero_add, hV₂ (x 1), sub_zero]

omit [Finite C] in
/-- **The `B¹` coboundary shape when the wild generators act trivially** (the paper's `B¹` in
Lemma 5.13(i), with the trivial wild action made an explicit hypothesis — however it is obtained:
directly, or via the proved `lemma_5_12` from `Pro2Core`; see
`docs/p13-normal-form-hypothesis-gap.md`).  Under `T = 1` and `x₀, x₁` acting trivially, every
coboundary `d⁰v` is supported on the `σ`-slot: `B¹ = {((S−1)v, 0, 0, 0)}`. -/
theorem b1w_split_shape (t : Marking C)
    (htau : ∀ v : V, t.τ • v = v) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (y : Fin 4 → V) :
    y ∈ B1w (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0] := by
  simp only [B1w, AddMonoidHom.mem_range]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v, funext fun i => ?_⟩
    fin_cases i <;>
      simp only [d0, AddMonoidHom.mk'_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        htau, hx0, hx1, sub_self]
  · rintro ⟨v, rfl⟩
    refine ⟨v, funext fun i => ?_⟩
    fin_cases i <;>
      simp only [d0, AddMonoidHom.mk'_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.tail_cons,
        htau, hx0, hx1, sub_self]

omit [Finite C] in
/-- On classes supported away from the `σ, τ` slots (`x 0 = x 1 = 0`, `y 0 = y 1 = 0`), the tame
relator value lies in the base slice `secHom '' C` (all its `σ, τ` inputs do), so its central
coordinate vanishes.  Hence the `mixedB` pairing on the `x₀`-supported normal forms is carried
entirely by the wild relator — the split/ramified Hessian is a pure wild-relator computation. -/
theorem heisMarking_tameValue_z_eq_zero (t : Marking C) (x : Fin 4 → V)
    (y : Fin 4 → ElemDual V) (hx0 : x 0 = 0) (hx1 : x 1 = 0) (hy0 : y 0 = 0) (hy1 : y 1 = 0) :
    (heisMarking t x y).tameValue.z = 0 := by
  have hσ : (heisMarking t x y).σ = secHom (A := V) t.σ := by
    simp only [heisMarking, secHom, hx0, hy0, MonoidHom.coe_mk, OneHom.coe_mk]
  have hτ : (heisMarking t x y).τ = secHom (A := V) t.τ := by
    simp only [heisMarking, secHom, hx1, hy1, MonoidHom.coe_mk, OneHom.coe_mk]
  have key : (heisMarking t x y).tameValue = secHom (A := V) t.tameValue := by
    simp only [Marking.tameValue, hσ, hτ, conjP, map_mul, map_inv, map_pow]
  rw [key]
  simp only [secHom, MonoidHom.coe_mk, OneHom.coe_mk]

/-- **Lemma 5.13, split case (i), cocycle shape**: if `T = 1` (trivial `τ`-action on a
nontrivial simple module), `Z¹ = {(a, 0, c, 0)}` and `B¹ = {((S−1)v, 0, 0, 0)}`.

Hypotheses (per `docs/p13-normal-form-hypothesis-gap.md`): `hcore` supplies trivial wild action
(`wild_acts_trivially`); `hσ` (σ acts nontrivially) excludes the trivial module `𝔽₂`, for which
`1 + S⁻¹ = 0` and the `x 3 = 0` clause fails — that module is handled separately in `prop_5_15`.

`hU` is the σ-tameness (`σ₂ = U` acts trivially).  In the split case it is *derivable* — with
`τ, x₀, x₁` acting trivially the `C`-action factors through the cyclic `⟨σ̄⟩`, so a simple `V` is a
simple `𝔽₂[⟨σ⟩]`-module, on which `σ` acts with odd order (roots of unity in char 2) ⇒ `σ₂ = 1` on
`V`.  That derivation needs `t.Generates` and the simple-cyclic-module rep theory; it is factored
out as a hypothesis here so the normal-form proof is pure finite-Fox calculus.  See
`docs/p13-normal-form-hypothesis-gap.md` §7.

*Status*: sorried (P-13; `B¹` half is `b1w_split_shape`, tame row is `d1Fun_tame_split`; the `x 3`
clause needs the wild row (Lemma 5.5) + invertibility of `1 + S⁻¹` from `hσ` and simplicity). -/
theorem lemma_5_13_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (hσ : ∃ v : V, t.σ • v ≠ v) :
    (∀ x : Fin 4 → V, x ∈ Z1w (A := V) t ↔ x 1 = 0 ∧ x 3 = 0) ∧
    (∀ y : Fin 4 → V, y ∈ B1w (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0]) := by
  sorry

/-- **Lemma 5.13, ramified case (ii), unique normal form**: if `V^T = 0`, every degree-one
class has a unique representative supported on `x₀` (display (53)).

Hypothesis `hcore` supplies trivial wild action (`wild_acts_trivially`); the ramified condition
`V^T = 0` (`htau`) gives `1 + T` invertible, so no separate nontriviality clause is needed.

*Status*: sorried (P-13; needs the wild row (Lemma 5.5) forcing `d = 0`, then the coboundary /
tame-row reduction). -/
theorem lemma_5_13_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v → v = 0) :
    ∀ x ∈ Z1w (A := V) t, ∃! c : V, x - x0Supported c ∈ B1w (A := V) t := by
  sorry

/-- **Lemma 5.13, pairing display (54), split case**: on `x₀`-supported representatives the
degree-one pairing is `(c, λ) ↦ λ(c)` when `T = 1`.

*Status*: sorried (P-13; via the mixed Hessian ledger, Lemma 5.14 — `h₀ ↦ λ(c)` via
`classTwoIdentity` [needs `g₀ = σ₂²` trivial, i.e. `hU`], and the `[d₀,z₀]` term vanishes since
`P + 1 = 0` in char 2 for `T = 1`).  `hsimple`/`hcore` give the trivial wild action
(`wild_acts_trivially`); `hU` is the σ-tameness (derivable in split; see `lemma_5_13_split`). -/
theorem lemma_5_13_pairing_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V] (hcore : t.Pro2Core)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) (c : V) (lam : ElemDual V) :
    mixedB t (x0Supported c) (x0Supported (V := ElemDual V) lam) = lam c := by
  sorry

/-- **Lemma 5.13, pairing display (54), ramified case**: when `V^T = 0` the pairing on
`x₀`-supported representatives is `(c, λ) ↦ λ((1 + U + U⁻¹)c)` for `U = S₂^ω`
(`Marking.sigma2`).

*Status*: sorried (P-13; Hessian ledger Lemma 5.14 — `h₀ ↦ λ(c)` plus the `[d₀,z₀]` symplectic
term `λ((U + U⁻¹)c)` via `HeisLift.commP_z_fiber`).  `hsimple`/`hcore` give the trivial wild
action (`wild_acts_trivially`). -/
theorem lemma_5_13_pairing_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V] (hcore : t.Pro2Core)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (c : V)
    (lam : ElemDual V) :
    mixedB t (x0Supported c) (x0Supported (V := ElemDual V) lam)
      = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c) := by
  sorry

end NormalForms

section MainDuality

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **Prop 5.15 (candidate deformation duality)**: the Fox–Heisenberg chain map is a
quasi-isomorphism for every finite elementary module — packaged: the display-(56) numerics
hold and the descended `B`-pairing is perfect.

Hypothesis `hcore` (the `Pro2Core` admissibility clause) supplies trivial wild action on every
simple subquotient via `wild_acts_trivially`; it is a property of the marking `t` alone, so it
covers the whole composition series.

*Status*: sorried (P-13; route: 5.12 + 5.13 for simples — including the trivial module, where
the traced form is the scalar cup–Bockstein table (25) — then 5.11 dévissage along a
composition series). -/
theorem prop_5_15 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) (hcore : t.Pro2Core) :
    IsSelfDual t A := by
  sorry

open ContCoh in
/-- **Prop 5.16 (local lifting duality)**: for a finite elementary module with `G_ℚ₂`-action
factoring through `ρ : G_ℚ₂ ↠ C`, the display-(57) numerics hold and the T-04 evaluation-cup
pairings are perfect in all three degree pairs (T-14 phrasing; the clause `#H²(𝔽₂) = 2`
certifies the target line).  The two-actions setup follows T-02's compatible-pair pattern:
separate `C`- and `G_ℚ₂`-actions related pointwise through `ρ` — no double instance on one
type.

*Status*: sorried (P-13 — **this is where axioms B6 and B7 enter**, per the App. D row; the
statement itself is axiom-free). -/
theorem prop_5_16 [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 AbsGalQ2 A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 AbsGalQ2 A) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 AbsGalQ2 (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 AbsGalQ2 A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H0 AbsGalQ2 A => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 AbsGalQ2 A => cup20 (dualEval A) hpair c) := by
  sorry

/-- **Corollary 5.17, numerics half** (proved wiring): the obstruction-space and
unobstructed-lift-multiplicity cardinalities agree for the two sources.  (The
adjoint-boundary identity (58) is deferred: it needs connecting-map infrastructure in both
theories — see the module docstring.) -/
theorem cor_5_17_card [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hcore : t.Pro2Core)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Nat.card (Z1w (A := A) t) = Nat.card (ContCoh.Z1 AbsGalQ2 A) ∧
    Nat.card (H2w (A := A) t) = Nat.card (ContCoh.H2 AbsGalQ2 A) := by
  obtain ⟨hc2, hc1, -⟩ := prop_5_15 t ht hw (A := A) hA₂ hcore
  obtain ⟨hl2, hl1, -⟩ := prop_5_16 ρ hρ (A := A) hcomp hA₂ hcompD htriv hpair
  exact ⟨hc1.trans hl1.symm, hc2.trans hl2.symm⟩

end MainDuality

end FoxH

end GQ2
