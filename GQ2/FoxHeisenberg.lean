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

/-- If the base `p.g` acts trivially, so does the base of the 2-primary part `p^{ω₂}` (any power of
a trivially-acting element acts trivially).  Companion to `powOmega2_u_of_trivial` for the
`.g`-action, used to push offsets through the collapsed ω₂-powers in the wild row. -/
theorem powOmega2_g_smul_of_trivial (p : WordLift A C) (hg : ∀ a : A, p.g • a = a) (a : A) :
    (powOmega2 p).g • a = a := by
  rw [powOmega2, pow_g]
  have hk : ∀ k : ℕ, p.g ^ k • a = a := by
    intro k
    induction k with
    | zero => rw [pow_zero, one_smul]
    | succ j ih => rw [pow_succ, mul_smul, hg, ih]
  exact hk _

/-- An offset-zero element stays offset-zero under the 2-primary part (its powers do). -/
theorem powOmega2_u_zero (p : WordLift A C) (hpu : p.u = 0) : (powOmega2 p).u = 0 := by
  rw [powOmega2, pow_u, hpu]; simp

/-- **The `P = 0` ledger, general form**: a partial norm `∑_{i<K} σⁱ • u` vanishes whenever
`σ` acts *fixed-point-freely* on `A` (`A^σ = 0`) and `σᴷ` fixes `u`.  The sum `S` is
`σ`-invariant — `σ·S = S + σᴷu − u = S` (telescope) — so `S ∈ A^σ = 0`.  (No char-2 needed.) -/
theorem sum_pow_smul_eq_zero {σ : C} (hfpf : ∀ a : A, σ • a = a → a = 0) {K : ℕ} {u : A}
    (hK : σ ^ K • u = u) : ∑ i ∈ Finset.range K, σ ^ i • u = 0 := by
  set S := ∑ i ∈ Finset.range K, σ ^ i • u with hS
  have e1 : ∑ i ∈ Finset.range (K + 1), σ ^ i • u = S + u := by
    rw [Finset.sum_range_succ, hK]
  have e2 : ∑ i ∈ Finset.range (K + 1), σ ^ i • u = σ • S + u := by
    rw [Finset.sum_range_succ', pow_zero, one_smul, hS, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [pow_succ', mul_smul])
  exact hfpf S (add_right_cancel (e1.symm.trans e2)).symm

/-- **The `P = 0` ledger** (ramified norm collapse, Lemma 5.13(ii)): when the base `σ` acts
*fixed-point-freely* on `A` (`A^σ = 0`), the norm projector `P = 1 + σ + ⋯ + σ^{n−1}`
(`n = orderOf σ`) annihilates every element.  The ramified analogue of `powOmega2_u_of_trivial`:
in the split case `σ` acts trivially and the ω₂-power collapses to its offset; here `σ` is
non-trivial (`A^T = 0`), so the geometric sum vanishes instead. -/
theorem norm_eq_zero_of_fixedPointFree [Finite C] (σ : C) (hfpf : ∀ a : A, σ • a = a → a = 0)
    (a : A) : ∑ i ∈ Finset.range (orderOf σ), σ ^ i • a = 0 :=
  sum_pow_smul_eq_zero hfpf (by rw [pow_orderOf_eq_one, one_smul])

/-- **The ω₂-collapse for a fixed-point-free odd-order base** (the ramified wild-row engine): if
the base `p.g` acts fixed-point-freely on `A` and its 2-primary part `powOmega2 p.g` acts
trivially (i.e. `p.g` acts with *odd* order), then the ω₂-power's offset vanishes,
`(powOmega2 p).u = 0`.  Proof: `(powOmega2 p).u = ∑_{i<ω₂Exp(ord p)} p.gⁱ • p.u` (`pow_u`);
its length `ω₂Exp(ord p)` is a multiple of the odd action-period, so
`(p.g)^{ω₂Exp(ord p)} = powOmega2 p.g` (finite-exponent independence `powOmega2_pow_eq`) fixes
`p.u`, and `sum_pow_smul_eq_zero` applies.  This is the ramified twin of
`powOmega2_u_of_trivial`, consuming the `hTodd` hypothesis of `lemma_5_13_ramified`. -/
theorem powOmega2_u_of_oddFixedPointFree [Finite A] [Finite C] (p : WordLift A C)
    (hfpf : ∀ a : A, p.g • a = a → a = 0) (hodd : ∀ a : A, powOmega2 p.g • a = a) :
    (powOmega2 p).u = 0 := by
  rw [powOmega2, pow_u]
  refine sum_pow_smul_eq_zero hfpf ?_
  have hdvd : orderOf p.g ∣ orderOf p := by
    apply orderOf_dvd_of_pow_eq_one; rw [← pow_g, pow_orderOf_eq_one]; rfl
  rw [powOmega2_pow_eq p.g hdvd (orderOf_pos p).ne']
  exact hodd p.u

/-- **Trivial left factor is `ω₂`-transparent**: if `g` acts trivially on `A`, then `powOmega2 (g·h)`
acts the same as `powOmega2 h`.  (`ω₂` is natural through `MulAction.toPermHom C A`
(`powOmega2_map`), and a trivially-acting `g` maps to `1`.)  Lets the ramified aux-word bases
`x₁·τ`, `x₀·τ` inherit `hTodd`'s odd-order condition from `τ` alone. -/
theorem powOmega2_smul_of_trivial_mul [Finite C] (g h : C) (hg : ∀ a : A, g • a = a)
    (hh : ∀ a : A, powOmega2 h • a = a) (a : A) : powOmega2 (g * h) • a = a := by
  have hperm : MulAction.toPermHom C A g = 1 := by ext w; simpa using hg w
  have hnat := powOmega2_map (MulAction.toPermHom C A) (g * h)
  rw [map_mul, hperm, one_mul, ← powOmega2_map] at hnat
  simpa using (congrArg (fun e => e a) hnat).trans (hh a)

/-! ### `.u` as an additive homomorphism on the trivially-based subgroup

At a tame lower map every wild aux word evaluates to an element whose base `g` acts trivially on the
coefficient module.  On that subgroup `(p*q).u = p.u + q.u` and `p⁻¹.u = -p.u`, so `.u` is a group
hom into `(A, +)`.  Consequently conjugates keep the offset (`conjP p g).u = p.u`) and commutators
have zero offset (`commP p q).u = 0`) — the mechanised form of the paper's "the wild factors
`h₀, [d₀,z₀]` have zero first derivative". -/

theorem inv_g_trivial (p : WordLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) : p⁻¹.g • a = a := by
  rw [inv_g, inv_smul_eq_iff]; exact (hp a).symm

theorem mul_g_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (p * q).g • a = a := by rw [mul_g, mul_smul, hq, hp]

theorem mul_u_of_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).u = p.u + q.u := by rw [mul_u, hp]

theorem inv_u_of_trivial (p : WordLift A C) (hp : ∀ a : A, p.g • a = a) : p⁻¹.u = -p.u := by
  rw [inv_u, show p.g⁻¹ • p.u = p.u by rw [inv_smul_eq_iff]; exact (hp p.u).symm]

theorem conjP_u_of_trivial (p g : WordLift A C) (hp : ∀ a : A, p.g • a = a)
    (hg : ∀ a : A, g.g • a = a) : (conjP p g).u = p.u := by
  rw [conjP, mul_u_of_trivial _ g (mul_g_trivial _ _ (inv_g_trivial g hg) hp),
    mul_u_of_trivial _ p (inv_g_trivial g hg), inv_u_of_trivial g hg]
  abel

/-- General conjugation offset with only the *conjugated* word's base trivial: the conjugator's
prefix survives as `g.g⁻¹ • ·`.  (The `x₂`-cancellation in the ramified `h₀`-row then happens in
`g₀`-conjugate *pairs* — `hU` is not needed.) -/
theorem conjP_u_of_base_trivial (p g : WordLift A C) (hp : ∀ a : A, p.g • a = a) :
    (conjP p g).u = g.g⁻¹ • p.u := by
  rw [conjP, mul_u, mul_u, inv_u, mul_g, inv_g, mul_smul, hp g.u]
  abel

theorem commP_u_of_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a)
    (hq : ∀ a : A, q.g • a = a) : (commP p q).u = 0 := by
  have hpi := inv_g_trivial p hp
  have hqi := inv_g_trivial q hq
  rw [commP, mul_u_of_trivial _ q (mul_g_trivial _ _ (mul_g_trivial _ _ hpi hqi) hp),
    mul_u_of_trivial _ p (mul_g_trivial _ _ hpi hqi), mul_u_of_trivial _ q⁻¹ hpi,
    inv_u_of_trivial p hp, inv_u_of_trivial q hq]
  abel

/-- A conjugate of a trivially-based element is trivially-based (for any conjugator). -/
theorem conjP_g_trivial (p g : WordLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) :
    (conjP p g).g • a = a := by
  rw [conjP, mul_g, mul_g, inv_g, mul_smul, mul_smul, hp, ← mul_smul, inv_mul_cancel, one_smul]

/-- A commutator of two trivially-based elements is trivially-based. -/
theorem commP_g_trivial (p q : WordLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (commP p q).g • a = a := by
  rw [commP]
  exact mul_g_trivial _ _ (mul_g_trivial _ _ (mul_g_trivial _ _ (inv_g_trivial p hp)
    (inv_g_trivial q hq)) hp) hq a

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

/-! ### The trivially-based toolkit for the mixed Hessian (Lemma 5.14)

Mirror of the `WordLift` toolkit for the central coordinate.  On elements whose base `g` acts
trivially on the module, `.a` and `.l` are additive homs and `.z` follows the Heisenberg cocycle
`(p*q).z = p.z + q.z + p.l(q.a)`.  This drives the `h₀ ↦ λ(c)` / `[d₀,z₀] ↦ 0` central ledger. -/

/-- A `C`-element acting trivially on the module acts trivially on its `𝔽₂`-dual (contragredient). -/
theorem smul_elemdual_trivial (g : C) (hg : ∀ a : A, g • a = a) (lam : ElemDual A) :
    g • lam = lam := by
  have hgi : ∀ a : A, g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hg a).symm
  ext a
  show (g • lam) a = lam a
  rw [ElemDual.smul_apply, hgi]

theorem mul_g_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (p * q).g • a = a := by rw [mul_g, mul_smul, hq, hp]

theorem inv_g_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) : p⁻¹.g • a = a := by
  rw [inv_g, inv_smul_eq_iff]; exact (hp a).symm

theorem conjP_g_trivial (p g : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (a : A) :
    (conjP p g).g • a = a := by
  rw [conjP, mul_g, mul_g, inv_g, mul_smul, mul_smul, hp, ← mul_smul, inv_mul_cancel, one_smul]

theorem commP_g_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) (hq : ∀ a : A, q.g • a = a)
    (a : A) : (commP p q).g • a = a := by
  rw [commP]
  exact mul_g_trivial _ _ (mul_g_trivial _ _ (mul_g_trivial _ _ (inv_g_trivial p hp)
    (inv_g_trivial q hq)) hp) hq a

theorem mul_a_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).a = p.a + q.a := by rw [mul_a, hp]

theorem mul_l_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).l = p.l + q.l := by rw [mul_l, smul_elemdual_trivial _ hp]

theorem mul_z_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    (p * q).z = p.z + q.z + p.l q.a := by rw [mul_z, hp]

theorem inv_a_of_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) : p⁻¹.a = -p.a := by
  rw [inv_a, show p.g⁻¹ • p.a = p.a by rw [inv_smul_eq_iff]; exact (hp p.a).symm]

theorem inv_l_of_trivial (p : HeisLift A C) (hp : ∀ a : A, p.g • a = a) : p⁻¹.l = -p.l := by
  have hgi : ∀ a : A, p.g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hp a).symm
  rw [inv_l, smul_elemdual_trivial _ hgi]

/-! Conjugation by a **g-slice** element `g` (`g.a = 0`, `g.l = 0`, `g.z = 0`) with trivially-acting
base preserves all three Heisenberg coordinates — it only conjugates the base.  This is `φ = conj by
g₀` in the `h₀`-shadow (`g₀ = σ₂²` lands in the base slice on the x₀-supported rep). -/

theorem conjP_a_of_gslice (p g : HeisLift A C) (hga : g.a = 0) (hgt : ∀ a : A, g.g • a = a) :
    (conjP p g).a = p.a := by
  have hgi : ∀ a : A, g.g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hgt a).symm
  simp only [conjP, mul_a, mul_g, inv_a, inv_g, hga, smul_zero, neg_zero, add_zero, zero_add, hgi]

theorem conjP_l_of_gslice (p g : HeisLift A C) (hgl : g.l = 0) (hgt : ∀ a : A, g.g • a = a) :
    (conjP p g).l = p.l := by
  have hgi : ∀ a : A, g.g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hgt a).symm
  simp only [conjP, mul_l, mul_g, inv_l, inv_g, hgl, smul_zero, neg_zero, add_zero, zero_add,
    smul_elemdual_trivial _ hgi]

theorem conjP_z_of_gslice (p g : HeisLift A C) (hga : g.a = 0) (hgl : g.l = 0) (hgz : g.z = 0)
    (hgt : ∀ a : A, g.g • a = a) : (conjP p g).z = p.z := by
  have hgi : ∀ a : A, g.g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hgt a).symm
  simp only [conjP, mul_z, mul_a, mul_l, mul_g, inv_z, inv_a, inv_l, inv_g, hga, hgl, hgz,
    smul_zero, neg_zero, map_zero, add_zero, zero_add, ElemDual.zero_apply, ElemDual.neg_apply,
    smul_elemdual_trivial _ hgi]

/-- Conjugation by a **base-slice** element `g` (`g.a = 0`), whose base may act *nontrivially*:
`(conjP p g).a = g.g⁻¹ • p.a`.  Generalises `conjP_a_of_gslice` (drops the base-triviality; used in
the ramified Hessian where `g₀ = σ₂²` acts by `U²`). -/
theorem conjP_a_of_slice (p g : HeisLift A C) (hga : g.a = 0) :
    (conjP p g).a = g.g⁻¹ • p.a := by
  simp only [conjP, mul_a, mul_g, inv_a, inv_g, hga, smul_zero, neg_zero, add_zero, zero_add]

/-- Conjugation by a base-slice element `g` (`g.l = 0`): `(conjP p g).l = g.g⁻¹ • p.l` (dual). -/
theorem conjP_l_of_slice (p g : HeisLift A C) (hgl : g.l = 0) :
    (conjP p g).l = g.g⁻¹ • p.l := by
  simp only [conjP, mul_l, mul_g, inv_l, inv_g, hgl, smul_zero, neg_zero, add_zero, zero_add]

/-- Conjugation by a base-slice element `g` (`a = l = z = 0`) fixes the central coordinate, even
when the base `g.g` acts nontrivially: `(conjP p g).z = p.z`. -/
theorem conjP_z_of_slice (p g : HeisLift A C) (hga : g.a = 0) (hgl : g.l = 0) (hgz : g.z = 0) :
    (conjP p g).z = p.z := by
  simp only [conjP, mul_z, mul_l, mul_g, inv_z, inv_l, inv_g, hga, hgl, hgz,
    smul_zero, neg_zero, map_zero, add_zero, zero_add, ElemDual.zero_apply]

/-- The commutator symplectic `B`-form for **trivially-based** elements (not just the `g = 1`
fiber): `[p,q].z = p.l(q.a) + q.l(p.a)`.  Gives `c₀ = [d₀,z₀] ↦ 0` once `d₀.a = d₀.l = 0`. -/
theorem commP_z_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hq : ∀ a : A, q.g • a = a) : (commP p q).z = p.l (q.a) + q.l (p.a) := by
  have hpi : ∀ a : A, p.g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hp a).symm
  have hqi : ∀ a : A, q.g⁻¹ • a = a := fun a => by rw [inv_smul_eq_iff]; exact (hq a).symm
  simp only [commP, mul_z, mul_a, mul_l, mul_g, inv_z, inv_a, inv_l, inv_g, mul_smul, hp, hq,
    hpi, hqi, smul_elemdual_trivial _ hp, smul_elemdual_trivial _ hq, smul_elemdual_trivial _ hpi,
    smul_elemdual_trivial _ hqi, map_neg, map_add, smul_zero, add_zero, zero_add,
    ElemDual.add_apply, ElemDual.neg_apply]
  generalize p.z = a1; generalize q.z = a2; generalize p.l p.a = a3
  generalize q.l q.a = a4; generalize p.l q.a = a5; generalize q.l p.a = a6
  revert a1 a2 a3 a4 a5 a6; decide

/-- The `A`-coordinate of a commutator of trivially-based elements vanishes (`.a` is additive). -/
theorem commP_a_of_trivial (p q : HeisLift A C) (hp : ∀ a : A, p.g • a = a)
    (hq : ∀ a : A, q.g • a = a) : (commP p q).a = 0 := by
  have hpi := inv_g_trivial p hp
  have hqi := inv_g_trivial q hq
  rw [commP, mul_a_of_trivial _ q (mul_g_trivial _ _ (mul_g_trivial _ _ hpi hqi) hp),
    mul_a_of_trivial _ p (mul_g_trivial _ _ hpi hqi), mul_a_of_trivial _ q⁻¹ hpi,
    inv_a_of_trivial p hp, inv_a_of_trivial q hq]
  abel

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

/-! ## Lemma 5.4/5.5: the finite Fox derivatives of the wild aux words (tame case)

At a tame lower map (the wild inertia `x₀, x₁` and, in the split case, `σ₂` acting trivially), the
`ω₂`-powers in the auxiliary words collapse to their offsets via `WordLift.powOmega2_u_of_trivial`,
so the first Fox derivatives `D(·)` become plain `𝔽₂`-combinations of the lift offsets `x`.  These
mirror the paper's Lemma 5.4 ledger `D(uᵢ) = P(Dxᵢ + Dτ)`, `D(d₀) = Pb + (P+1)c` at `P = 1`. -/

section WildRow

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-- **`D(u₀) = x₂ + x₁`** (tame case): with `x₀, τ` acting trivially the `ω₂`-power in
`u₀ = (x₀τ)^{ω₂}` collapses (odd exponent, char 2), leaving the plain product offset. -/
theorem liftMarking_u0_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).u0.u = x 2 + x 1 := by
  have hbase : ∀ v : V, ((liftMarking t x).x₀ * (liftMarking t x).τ).g • v = v := by
    intro v
    show (t.x₀ * t.τ) • v = v
    rw [mul_smul, htau, hx0]
  have hu0 : (liftMarking t x).u0 = powOmega2 ((liftMarking t x).x₀ * (liftMarking t x).τ) := rfl
  rw [hu0, WordLift.powOmega2_u_of_trivial hV₂ _ hbase]
  show x 2 + t.x₀ • x 1 = x 2 + x 1
  rw [hx0]

/-- **`D(u₁) = x₃ + x₁`** (tame case), the `x₁`-analogue of `liftMarking_u0_u`. -/
theorem liftMarking_u1_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).u1.u = x 3 + x 1 := by
  have hbase : ∀ v : V, ((liftMarking t x).x₁ * (liftMarking t x).τ).g • v = v := by
    intro v
    show (t.x₁ * t.τ) • v = v
    rw [mul_smul, htau, hx1]
  have hu1 : (liftMarking t x).u1 = powOmega2 ((liftMarking t x).x₁ * (liftMarking t x).τ) := rfl
  rw [hu1, WordLift.powOmega2_u_of_trivial hV₂ _ hbase]
  show x 3 + t.x₁ • x 1 = x 3 + x 1
  rw [hx1]

/-! ### Ramified (`V^T = 0`) aux-word offsets (P-13b)

In the ramified case `τ` acts non-trivially, but its 2-primary part is trivial (`hTodd`), so the
ω₂-power bases `u0 = (x₀τ)^{ω₂}`, `u1 = (x₁τ)^{ω₂}` still act *trivially* on `V` (their base is the
2-part of the `τ`-action) while their offsets *vanish* (`powOmega2_u_of_oddFixedPointFree`).  Thus
every wild aux word remains trivially-based (so the split `.u`-additivity toolkit applies), only the
`u0`/`u1` offsets change to `0`. -/

/-- Ramified base-`g` triviality: `u0`'s base acts trivially on `V` (it is `powOmega2 (t.x₀ t.τ)`,
whose action is `τ`'s 2-part, killed by `hTodd`). -/
theorem liftMarking_u0_g_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).u0.g • v = v := by
  have hg : ((liftMarking t x).x₀ * (liftMarking t x).τ).g = t.x₀ * t.τ := rfl
  have hgeq : (liftMarking t x).u0.g = powOmega2 (t.x₀ * t.τ) := by
    show (powOmega2 ((liftMarking t x).x₀ * (liftMarking t x).τ)).g = powOmega2 (t.x₀ * t.τ)
    rw [powOmega2, WordLift.pow_g, hg]
    exact powOmega2_pow_eq (t.x₀ * t.τ)
      (orderOf_dvd_of_pow_eq_one (by rw [← hg, ← WordLift.pow_g, pow_orderOf_eq_one]; rfl))
      (orderOf_pos _).ne'
  rw [hgeq]; exact WordLift.powOmega2_smul_of_trivial_mul t.x₀ t.τ hx0 hTodd v

/-- Ramified base-`g` triviality: `u1`'s base acts trivially on `V`. -/
theorem liftMarking_u1_g_ramified (t : Marking C) (x : Fin 4 → V) (hx1 : ∀ v : V, t.x₁ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).u1.g • v = v := by
  have hg : ((liftMarking t x).x₁ * (liftMarking t x).τ).g = t.x₁ * t.τ := rfl
  have hgeq : (liftMarking t x).u1.g = powOmega2 (t.x₁ * t.τ) := by
    show (powOmega2 ((liftMarking t x).x₁ * (liftMarking t x).τ)).g = powOmega2 (t.x₁ * t.τ)
    rw [powOmega2, WordLift.pow_g, hg]
    exact powOmega2_pow_eq (t.x₁ * t.τ)
      (orderOf_dvd_of_pow_eq_one (by rw [← hg, ← WordLift.pow_g, pow_orderOf_eq_one]; rfl))
      (orderOf_pos _).ne'
  rw [hgeq]; exact WordLift.powOmega2_smul_of_trivial_mul t.x₁ t.τ hx1 hTodd v

/-- Ramified `D(u₀) = 0` (the ω₂-norm of the fixed-point-free `τ`-base vanishes). -/
theorem liftMarking_u0_u_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).u0.u = 0 := by
  show (powOmega2 ((liftMarking t x).x₀ * (liftMarking t x).τ)).u = 0
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => htau _ ?_)
    (fun v => WordLift.powOmega2_smul_of_trivial_mul t.x₀ t.τ hx0 hTodd v)
  have hact : ((liftMarking t x).x₀ * (liftMarking t x).τ).g • v = t.τ • v := by
    show (t.x₀ * t.τ) • v = t.τ • v; rw [mul_smul, hx0]
  rw [← hact]; exact hv

/-- Ramified `D(u₁) = 0`. -/
theorem liftMarking_u1_u_ramified (t : Marking C) (x : Fin 4 → V) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).u1.u = 0 := by
  show (powOmega2 ((liftMarking t x).x₁ * (liftMarking t x).τ)).u = 0
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => htau _ ?_)
    (fun v => WordLift.powOmega2_smul_of_trivial_mul t.x₁ t.τ hx1 hTodd v)
  have hact : ((liftMarking t x).x₁ * (liftMarking t x).τ).g • v = t.τ • v := by
    show (t.x₁ * t.τ) • v = t.τ • v; rw [mul_smul, hx1]
  rw [← hact]; exact hv

/-- **`D(d₀) = x₁`** (tame case, `P = 1`): from `d₀ = u₀·x₀⁻¹`, `D(d₀) = D(u₀) − x₂ = (x₂+x₁) − x₂ =
x₁`.  This is the paper's `Dd₀ = Pb + (P+1)c = b` at the split value `P = 1` (`c`-terms cancel). -/
theorem liftMarking_d0_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (liftMarking t x).d0.u = x 1 := by
  have hbase : ∀ v : V, ((liftMarking t x).x₀ * (liftMarking t x).τ).g • v = v := by
    intro v
    show (t.x₀ * t.τ) • v = v
    rw [mul_smul, htau, hx0]
  have hx0inv : ∀ v : V, t.x₀⁻¹ • v = v := fun v => by rw [inv_smul_eq_iff]; exact (hx0 v).symm
  have hu0g : ∀ v : V, (liftMarking t x).u0.g • v = v := fun v =>
    WordLift.powOmega2_g_smul_of_trivial _ hbase v
  have hd0 : (liftMarking t x).d0 = (liftMarking t x).u0 * (liftMarking t x).x₀⁻¹ := rfl
  rw [hd0, WordLift.mul_u, liftMarking_u0_u t x hV₂ hx0 htau, WordLift.inv_u]
  show x 2 + x 1 + (liftMarking t x).u0.g • -(t.x₀⁻¹ • x 2) = x 1
  rw [hx0inv, hu0g]
  abel

/-- **`σ₂`'s base is exactly `t.sigma2`** — the `ω₂`-exponent taken in `WordLift V C` agrees with the
one in `C` (Lemma 5.1, finite-exponent independence): `orderOf t.σ ∣ orderOf σ_WL`, so
`powOmega2_pow_eq` identifies the two representatives.  Hence the σ-tameness `hU` (stated on
`t.sigma2`) transfers to the wild-row evaluation — `hU v` gives `(liftMarking t x).sigma2.g • v = v`
after `rw [liftMarking_sigma2_g]`. -/
theorem liftMarking_sigma2_g (t : Marking C) (x : Fin 4 → V) :
    (liftMarking t x).sigma2.g = t.sigma2 := by
  have hg : (liftMarking t x).σ.g = t.σ := rfl
  have hdvd : orderOf t.σ ∣ orderOf (liftMarking t x).σ := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : ((liftMarking t x).σ ^ orderOf (liftMarking t x).σ).g = (1 : WordLift V C).g :=
      congrArg WordLift.g (pow_orderOf_eq_one _)
    rwa [WordLift.pow_g, hg, WordLift.one_g] at h1
  have hN : orderOf (liftMarking t x).σ ≠ 0 := (orderOf_pos _).ne'
  rw [show (liftMarking t x).sigma2 =
      (liftMarking t x).σ ^ omega2Exp (orderOf (liftMarking t x).σ) from rfl,
    WordLift.pow_g, hg]
  exact powOmega2_pow_eq t.σ hdvd hN

omit [Finite V] [Finite C] in
/-- **`D(x₁^σ) = S⁻¹·x₃`** (tame case): conjugating by `σ` shifts the `x₁`-offset by `t.σ⁻¹`, and the
`x₀`-offsets contributed by the two `σ`'s cancel.  This is the sole surviving `S⁻¹` in the wild row
(the paper's `xσ₁` ledger row `0 0 0 S⁻¹`). -/
theorem liftMarking_conjP_x1_sigma_u (t : Marking C) (x : Fin 4 → V)
    (hx1 : ∀ v : V, t.x₁ • v = v) :
    (conjP (liftMarking t x).x₁ (liftMarking t x).σ).u = t.σ⁻¹ • x 3 := by
  show -(t.σ⁻¹ • x 0) + t.σ⁻¹ • x 3 + (t.σ⁻¹ * t.x₁) • x 0 = t.σ⁻¹ • x 3
  rw [mul_smul, hx1]; abel

/-! ### Base-triviality of the wild aux words (tame case)

Each aux word evaluates to a trivially-based element, so `.u`-additivity (`mul_u_of_trivial` etc.)
applies.  `g₀ = σ₂²` and `z₀ = x₀^{σ₂}` use σ-tameness `hU`; the rest use the wild-core triviality. -/

theorem liftMarking_g0_g_smul (t : Marking C) (x : Fin 4 → V) (hU : ∀ v : V, t.sigma2 • v = v)
    (v : V) : (liftMarking t x).g0.g • v = v := by
  show ((liftMarking t x).sigma2 ^ 2).g • v = v
  rw [WordLift.pow_g, pow_two, mul_smul, liftMarking_sigma2_g, hU, hU]

theorem liftMarking_u0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).u0.g • v = v := by
  apply WordLift.powOmega2_g_smul_of_trivial
  intro a; show (t.x₀ * t.τ) • a = a; rw [mul_smul, htau, hx0]

theorem liftMarking_u1_g_smul (t : Marking C) (x : Fin 4 → V) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).u1.g • v = v := by
  apply WordLift.powOmega2_g_smul_of_trivial
  intro a; show (t.x₁ * t.τ) • a = a; rw [mul_smul, htau, hx1]

theorem liftMarking_d0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (v : V) : (liftMarking t x).d0.g • v = v := by
  show ((liftMarking t x).u0 * (liftMarking t x).x₀⁻¹).g • v = v
  exact WordLift.mul_g_trivial _ _ (liftMarking_u0_g_smul t x hx0 htau)
    (WordLift.inv_g_trivial (liftMarking t x).x₀ hx0) v

theorem liftMarking_z0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (v : V) : (liftMarking t x).z0.g • v = v := by
  show (conjP (liftMarking t x).x₀ (liftMarking t x).sigma2).g • v = v
  exact WordLift.conjP_g_trivial _ _ hx0 v

theorem liftMarking_h0_g_smul (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) (v : V) :
    (liftMarking t x).h0.g • v = v := by
  have hd0g := liftMarking_d0_g_smul t x hx0 htau
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hhcg : ∀ w : V, (liftMarking t x).hc.g • w = w := fun w =>
    WordLift.commP_g_trivial _ _ hdgg hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).g • v = v
  exact WordLift.mul_g_trivial _ _ hq4 hhcg v

/-- **`D(h₀) = 0`** (tame case): the paper's `h₀`-shadow (Lemma 5.3(i)).  With every base acting
trivially, `.u` is additive, so `D(h₀) = D(x₀^{g₀}) + D(x₀) + D(d_g) + D(d₀) + D(d₀²) + D([d_g,d₀])
= x₂ + x₂ + x₁ + x₁ + 0 + 0 = 0` (conjugates keep the offset, `d₀²` and the commutator vanish). -/
theorem liftMarking_h0_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).h0.u = 0 := by
  have hd0g := liftMarking_d0_g_smul t x hx0 htau
  have hg0g := liftMarking_g0_g_smul t x hU
  have hd0u := liftMarking_d0_u t x hV₂ hx0 htau
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  have hP1u : (conjP (liftMarking t x).x₀ (liftMarking t x).g0).u = x 2 :=
    WordLift.conjP_u_of_trivial _ _ hx0 hg0g
  have hdgu : (liftMarking t x).dg.u = x 1 := by
    show (conjP (liftMarking t x).d0 (liftMarking t x).g0).u = x 1
    rw [WordLift.conjP_u_of_trivial _ _ hd0g hg0g, hd0u]
  have hhcu : (liftMarking t x).hc.u = 0 := by
    show (commP (liftMarking t x).dg (liftMarking t x).d0).u = 0
    exact WordLift.commP_u_of_trivial _ _ hdgg hd0g
  have hd02u : ((liftMarking t x).d0 ^ 2).u = 0 := by
    rw [pow_two, WordLift.mul_u_of_trivial _ _ hd0g, hd0u]; exact hV₂ (x 1)
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).u = 0
  rw [WordLift.mul_u_of_trivial _ _ hq4, WordLift.mul_u_of_trivial _ _ hq3,
    WordLift.mul_u_of_trivial _ _ hq2, WordLift.mul_u_of_trivial _ _ hq1,
    WordLift.mul_u_of_trivial _ _ hP1g, hP1u, hhcu, hd02u, hdgu, hd0u]
  show x 2 + x 2 + x 1 + x 1 + 0 + 0 = 0
  rw [add_zero, add_zero, hV₂ (x 2), zero_add, hV₂ (x 1)]

/-- **`D(c₀) = 0`** (tame case): `c₀ = [d₀,z₀]` is a commutator of trivially-based elements. -/
theorem liftMarking_c0_u (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).c0.u = 0 := by
  show (commP (liftMarking t x).d0 (liftMarking t x).z0).u = 0
  exact WordLift.commP_u_of_trivial _ _ (liftMarking_d0_g_smul t x hx0 htau)
    (liftMarking_z0_g_smul t x hx0)

/-- **The split wild row (Lemma 5.5)**: `L_w = D(h₀) + D(u₁⁻¹) + D(x₁^σ) + D(c₀) =
0 + (x₃+x₁) + S⁻¹·x₃ + 0 = x₁ + (1 + S⁻¹)·x₃`.  This is `(d1Fun t x).2` at a split (`T = 1`) simple
tame module — the wild half of `lemma_5_13_split`'s `Z¹` characterisation. -/
theorem liftMarking_wildValue_u (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (hU : ∀ v : V, t.sigma2 • v = v) :
    (liftMarking t x).wildValue.u = x 1 + x 3 + t.σ⁻¹ • x 3 := by
  have hh0g := liftMarking_h0_g_smul t x hx0 htau hU
  have hu1g := liftMarking_u1_g_smul t x hx1 htau
  have hx1sg : ∀ w : V, (conjP (liftMarking t x).x₁ (liftMarking t x).σ).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx1 w
  have hu1invg : ∀ w : V, (liftMarking t x).u1⁻¹.g • w = w := fun w =>
    WordLift.inv_g_trivial _ hu1g w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hh0g hu1invg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hx1sg w
  show ((liftMarking t x).h0 * (liftMarking t x).u1⁻¹ *
    conjP (liftMarking t x).x₁ (liftMarking t x).σ * (liftMarking t x).c0).u =
    x 1 + x 3 + t.σ⁻¹ • x 3
  rw [WordLift.mul_u_of_trivial _ _ hq3, WordLift.mul_u_of_trivial _ _ hq2,
    WordLift.mul_u_of_trivial _ _ hh0g, liftMarking_h0_u t x hV₂ hx0 htau hU,
    WordLift.inv_u_of_trivial _ hu1g, liftMarking_u1_u t x hV₂ hx1 htau,
    liftMarking_conjP_x1_sigma_u t x hx1, liftMarking_c0_u t x hx0 htau hU,
    show -(x 3 + x 1) = x 3 + x 1 from neg_eq_of_add_eq_zero_left (hV₂ (x 3 + x 1))]
  abel

/-! ### Ramified wild row (P-13b): `L_w = S⁻¹·d`

With `u0.u = u1.u = 0` (collapse) and every aux base trivial, the ramified aux offsets are
`d0.u = x₂` (vs `x₁` split), `h0.u = 0`, `c0.u = 0`, and `conjP(x₁,σ).u = S⁻¹·x₃` (the split lemma,
`τ`-free).  So the wild value collapses to `S⁻¹·x₃` — the display (53) wild row. -/

/-- Ramified `d0.g` acts trivially (via the `hTodd` `u0.g`-triviality). -/
theorem liftMarking_d0_g_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).d0.g • v = v :=
  WordLift.mul_g_trivial _ _ (liftMarking_u0_g_ramified t x hx0 hTodd)
    (WordLift.inv_g_trivial _ hx0) v

/-- Ramified `D(d₀) = x₂` (`= Pb + (P+1)c = c` at `P = 0`; `c`-term survives, `b`-term dies). -/
theorem liftMarking_d0_u_ramified (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) : (liftMarking t x).d0.u = x 2 := by
  have hx0inv : ∀ v : V, t.x₀⁻¹ • v = v := fun v => by rw [inv_smul_eq_iff]; exact (hx0 v).symm
  show ((liftMarking t x).u0 * (liftMarking t x).x₀⁻¹).u = x 2
  rw [WordLift.mul_u, liftMarking_u0_u_ramified t x hx0 htau hTodd, WordLift.inv_u]
  show 0 + (liftMarking t x).u0.g • -(t.x₀⁻¹ • x 2) = x 2
  rw [hx0inv, liftMarking_u0_g_ramified t x hx0 hTodd, zero_add]
  exact neg_eq_of_add_eq_zero_left (hV₂ (x 2))

/-- Ramified `D(c₀) = 0` (`c₀ = [d₀,z₀]`, both trivially-based; `z0.g` reuses the split lemma). -/
theorem liftMarking_c0_u_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) : (liftMarking t x).c0.u = 0 :=
  WordLift.commP_u_of_trivial _ _ (liftMarking_d0_g_ramified t x hx0 hTodd)
    (liftMarking_z0_g_smul t x hx0)

/-- Ramified `h₀.g` acts trivially (all sub-word bases trivial; only `hd0g` differs from split). -/
theorem liftMarking_h0_g_ramified (t : Marking C) (x : Fin 4 → V) (hx0 : ∀ v : V, t.x₀ • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) : (liftMarking t x).h0.g • v = v := by
  have hd0g := liftMarking_d0_g_ramified t x hx0 hTodd
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hhcg : ∀ w : V, (liftMarking t x).hc.g • w = w := fun w =>
    WordLift.commP_g_trivial _ _ hdgg hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).g • v = v
  exact WordLift.mul_g_trivial _ _ hq4 hhcg v

/-- Ramified `D(h₀) = 0` — **`hU`-free** (de-`hU`'d 2026-07-05): the cancellation happens in
`g₀`-conjugate *pairs*, `(g₀⁻¹•x₂ + x₂) + (g₀⁻¹•x₂ + x₂) = 0`, via `conjP_u_of_base_trivial` —
the `x₀^{g₀}`/`dg` terms carry the same `g₀⁻¹` prefix as each other, so no triviality of `g₀`'s
action is needed.  (`hU` is *not* derivable from admissibility: `S₃` on its 2-dimensional simple
module, marking `x₀=x₁=1`, is admissible with `σ₂ = σ` acting nontrivially.) -/
theorem liftMarking_h0_u_ramified (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).h0.u = 0 := by
  have hd0g := liftMarking_d0_g_ramified t x hx0 hTodd
  have hd0u := liftMarking_d0_u_ramified t x hV₂ hx0 htau hTodd
  have hP1g : ∀ w : V, (conjP (liftMarking t x).x₀ (liftMarking t x).g0).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx0 w
  have hdgg : ∀ w : V, (liftMarking t x).dg.g • w = w := fun w =>
    WordLift.conjP_g_trivial (liftMarking t x).d0 (liftMarking t x).g0 hd0g w
  have hq1 := fun w => WordLift.mul_g_trivial _ (liftMarking t x).x₀ hP1g hx0 w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hq1 hdgg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hd0g w
  have hd02g : ∀ w : V, ((liftMarking t x).d0 ^ 2).g • w = w := fun w => by
    rw [WordLift.pow_g, pow_two, mul_smul, hd0g, hd0g]
  have hq4 := fun w => WordLift.mul_g_trivial _ _ hq3 hd02g w
  have hP1u : (conjP (liftMarking t x).x₀ (liftMarking t x).g0).u
      = (liftMarking t x).g0.g⁻¹ • x 2 :=
    WordLift.conjP_u_of_base_trivial _ _ hx0
  have hdgu : (liftMarking t x).dg.u = (liftMarking t x).g0.g⁻¹ • x 2 := by
    show (conjP (liftMarking t x).d0 (liftMarking t x).g0).u = _
    rw [WordLift.conjP_u_of_base_trivial _ _ hd0g, hd0u]
  have hhcu : (liftMarking t x).hc.u = 0 := by
    show (commP (liftMarking t x).dg (liftMarking t x).d0).u = 0
    exact WordLift.commP_u_of_trivial _ _ hdgg hd0g
  have hd02u : ((liftMarking t x).d0 ^ 2).u = 0 := by
    rw [pow_two, WordLift.mul_u_of_trivial _ _ hd0g, hd0u]; exact hV₂ (x 2)
  show (conjP (liftMarking t x).x₀ (liftMarking t x).g0 * (liftMarking t x).x₀ *
    (liftMarking t x).dg * (liftMarking t x).d0 * (liftMarking t x).d0 ^ 2 *
    (liftMarking t x).hc).u = 0
  rw [WordLift.mul_u_of_trivial _ _ hq4, WordLift.mul_u_of_trivial _ _ hq3,
    WordLift.mul_u_of_trivial _ _ hq2, WordLift.mul_u_of_trivial _ _ hq1,
    WordLift.mul_u_of_trivial _ _ hP1g, hP1u, hhcu, hd02u, hdgu, hd0u]
  show (liftMarking t x).g0.g⁻¹ • x 2 + x 2 + (liftMarking t x).g0.g⁻¹ • x 2 + x 2 + 0 + 0 = 0
  rw [add_zero, add_zero,
    show (liftMarking t x).g0.g⁻¹ • x 2 + x 2 + (liftMarking t x).g0.g⁻¹ • x 2 + x 2
      = ((liftMarking t x).g0.g⁻¹ • x 2 + (liftMarking t x).g0.g⁻¹ • x 2) + (x 2 + x 2) from by
        abel,
    hV₂, hV₂, add_zero]

/-- **The ramified wild row (Lemma 5.5, `V^T = 0`)**: `L_w = D(h₀) + D(u₁⁻¹) + D(x₁^σ) + D(c₀) =
0 + 0 + S⁻¹·x₃ + 0 = S⁻¹·x₃`.  This is `(d1Fun t x).2` at a ramified simple module — the wild half
forcing `d = x₃ = 0` in the normal form. -/
theorem liftMarking_wildValue_u_ramified (t : Marking C) (x : Fin 4 → V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (liftMarking t x).wildValue.u = t.σ⁻¹ • x 3 := by
  have hh0g := liftMarking_h0_g_ramified t x hx0 hTodd
  have hu1g := liftMarking_u1_g_ramified t x hx1 hTodd
  have hx1sg : ∀ w : V, (conjP (liftMarking t x).x₁ (liftMarking t x).σ).g • w = w := fun w =>
    WordLift.conjP_g_trivial _ _ hx1 w
  have hu1invg : ∀ w : V, (liftMarking t x).u1⁻¹.g • w = w := fun w =>
    WordLift.inv_g_trivial _ hu1g w
  have hq2 := fun w => WordLift.mul_g_trivial _ _ hh0g hu1invg w
  have hq3 := fun w => WordLift.mul_g_trivial _ _ hq2 hx1sg w
  show ((liftMarking t x).h0 * (liftMarking t x).u1⁻¹ *
    conjP (liftMarking t x).x₁ (liftMarking t x).σ * (liftMarking t x).c0).u = t.σ⁻¹ • x 3
  rw [WordLift.mul_u_of_trivial _ _ hq3, WordLift.mul_u_of_trivial _ _ hq2,
    WordLift.mul_u_of_trivial _ _ hh0g, liftMarking_h0_u_ramified t x hV₂ hx0 htau hTodd,
    WordLift.inv_u_of_trivial _ hu1g, liftMarking_u1_u_ramified t x hx1 htau hTodd,
    liftMarking_conjP_x1_sigma_u t x hx1, liftMarking_c0_u_ramified t x hx0 hTodd]
  show 0 + -(0 : V) + t.σ⁻¹ • x 3 + 0 = t.σ⁻¹ • x 3
  abel

end WildRow

/-! ## Lemma 5.14: the mixed Hessian (split case) via `agHom`/`lgHom` naturality

The `.a` and `.l` coordinates of the Heisenberg-evaluated aux words come free from the `WordLift`
wild-row results: `agHom`/`lgHom` are homs pushing `heisMarking` to `liftMarking` (over `V`, resp.
`V^∨`), so `(heisMarking t x y).W.a = (liftMarking t x).W.u` and `.l = (liftMarking t y).W.u`.  On
the x₀-supported rep (`x₁ = x₃ = 0` slots) these vanish for every aux word, leaving a pure central
computation. -/

section HessianRow

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-- The degree-one tuple supported on the `x₀`-slot (display (53)'s normal form). -/
def x0Supported (c : V) : Fin 4 → V := ![0, 0, c, 0]

theorem heisMarking_map_agHom (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).map agHom = liftMarking t x := rfl

theorem heisMarking_map_lgHom (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).map lgHom = liftMarking t y := rfl

/-- Naturality: the `.a` of an aux word at `heisMarking` is the `liftMarking` `.u` (via `agHom`);
`.l` is the dual `liftMarking` `.u` (via `lgHom`); `.g` agrees (both project the base). -/
theorem heisMarking_h0_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).h0.a = (liftMarking t x).h0.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).h0 = (liftMarking t x).h0 by
    rw [← Marking.map_h0, heisMarking_map_agHom])

theorem heisMarking_h0_l (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).h0.l = (liftMarking t y).h0.u :=
  congrArg WordLift.u (show lgHom (heisMarking t x y).h0 = (liftMarking t y).h0 by
    rw [← Marking.map_h0, heisMarking_map_lgHom])

theorem heisMarking_h0_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).h0.g = (liftMarking t x).h0.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).h0 = (liftMarking t x).h0 by
    rw [← Marking.map_h0, heisMarking_map_agHom])

theorem heisMarking_d0_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).d0.a = (liftMarking t x).d0.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).d0 = (liftMarking t x).d0 by
    rw [← Marking.map_d0, heisMarking_map_agHom])

theorem heisMarking_d0_l (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).d0.l = (liftMarking t y).d0.u :=
  congrArg WordLift.u (show lgHom (heisMarking t x y).d0 = (liftMarking t y).d0 by
    rw [← Marking.map_d0, heisMarking_map_lgHom])

theorem heisMarking_d0_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).d0.g = (liftMarking t x).d0.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).d0 = (liftMarking t x).d0 by
    rw [← Marking.map_d0, heisMarking_map_agHom])

theorem heisMarking_c0_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).c0.a = (liftMarking t x).c0.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).c0 = (liftMarking t x).c0 by
    rw [← Marking.map_c0, heisMarking_map_agHom])

theorem heisMarking_c0_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).c0.g = (liftMarking t x).c0.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).c0 = (liftMarking t x).c0 by
    rw [← Marking.map_c0, heisMarking_map_agHom])

theorem heisMarking_u1_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).u1.g = (liftMarking t x).u1.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).u1 = (liftMarking t x).u1 by
    rw [← Marking.map_u1, heisMarking_map_agHom])

theorem heisMarking_sigma2_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).sigma2.a = (liftMarking t x).sigma2.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).sigma2 = (liftMarking t x).sigma2 by
    rw [← Marking.map_sigma2, heisMarking_map_agHom])

theorem heisMarking_sigma2_l (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).sigma2.l = (liftMarking t y).sigma2.u :=
  congrArg WordLift.u (show lgHom (heisMarking t x y).sigma2 = (liftMarking t y).sigma2 by
    rw [← Marking.map_sigma2, heisMarking_map_lgHom])

theorem heisMarking_sigma2_g_eq (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).sigma2.g = (liftMarking t x).sigma2.g :=
  congrArg WordLift.g (show agHom (heisMarking t x y).sigma2 = (liftMarking t x).sigma2 by
    rw [← Marking.map_sigma2, heisMarking_map_agHom])

/-- On the x₀-supported rep, `σ` (index 0) lands in the base slice, so `σ₂` and `g₀` are pure base
elements: their `.a`, `.l`, `.z` all vanish (via `secHom`-slice + the square for `z`). -/
theorem heisMarking_sigma2_u_zero (t : Marking C) (x : Fin 4 → V)
    (hx0 : x 0 = 0) : (liftMarking t x).sigma2.u = 0 :=
  WordLift.powOmega2_u_zero _ (show x 0 = 0 from hx0)

/-! ### Base-triviality of the Heisenberg aux words (transferred from `liftMarking`). -/

theorem heisMarking_sigma2_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hU : ∀ v : V, t.sigma2 • v = v) (v : V) : (heisMarking t x y).sigma2.g • v = v := by
  rw [heisMarking_sigma2_g_eq, liftMarking_sigma2_g]; exact hU v

theorem heisMarking_d0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).d0.g • v = v := by
  rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_smul t x hx0 htau v

theorem heisMarking_h0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (v : V) : (heisMarking t x y).h0.g • v = v := by
  rw [heisMarking_h0_g_eq]; exact liftMarking_h0_g_smul t x hx0 htau hU v

theorem heisMarking_u1_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).u1.g • v = v := by
  rw [heisMarking_u1_g_eq]; exact liftMarking_u1_g_smul t x hx1 htau v

theorem heisMarking_g0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hU : ∀ v : V, t.sigma2 • v = v) (v : V) : (heisMarking t x y).g0.g • v = v := by
  show ((heisMarking t x y).sigma2 ^ 2).g • v = v
  rw [pow_two, HeisLift.mul_g, mul_smul, heisMarking_sigma2_g_smul t x y hU,
    heisMarking_sigma2_g_smul t x y hU]

theorem heisMarking_z0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (v : V) : (heisMarking t x y).z0.g • v = v :=
  HeisLift.conjP_g_trivial (heisMarking t x y).x₀ (heisMarking t x y).sigma2 hx0 v

theorem heisMarking_dg_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).dg.g • v = v :=
  HeisLift.conjP_g_trivial (heisMarking t x y).d0 (heisMarking t x y).g0
    (heisMarking_d0_g_smul t x y hx0 htau) v

theorem heisMarking_hc_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).hc.g • v = v :=
  HeisLift.commP_g_trivial (heisMarking t x y).dg (heisMarking t x y).d0
    (heisMarking_dg_g_smul t x y hx0 htau) (heisMarking_d0_g_smul t x y hx0 htau) v

theorem heisMarking_c0_g_smul (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t x y).c0.g • v = v :=
  HeisLift.commP_g_trivial (heisMarking t x y).d0 (heisMarking t x y).z0
    (heisMarking_d0_g_smul t x y hx0 htau) (heisMarking_z0_g_smul t x y hx0) v

/-! ### `g₀ = σ₂²` is a base-slice element on the x₀-supported rep (`a = l = z = 0`). -/

theorem heisMarking_sigma2_a_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).sigma2.a = 0 := by
  rw [heisMarking_sigma2_a]; exact heisMarking_sigma2_u_zero t (x0Supported c) rfl

theorem heisMarking_sigma2_l_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).sigma2.l = 0 := by
  rw [heisMarking_sigma2_l]; exact WordLift.powOmega2_u_zero _ rfl

theorem heisMarking_g0_a_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).g0.a = 0 := by
  have h := heisMarking_sigma2_a_zero t c lam
  show ((heisMarking t (x0Supported c) (x0Supported lam)).sigma2 ^ 2).a = 0
  rw [pow_two, HeisLift.mul_a, h, smul_zero, add_zero]

theorem heisMarking_g0_l_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).g0.l = 0 := by
  have h := heisMarking_sigma2_l_zero t c lam
  show ((heisMarking t (x0Supported c) (x0Supported lam)).sigma2 ^ 2).l = 0
  rw [pow_two, HeisLift.mul_l, h, smul_zero, add_zero]

theorem heisMarking_g0_z_zero (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).g0.z = 0 := by
  have h := heisMarking_sigma2_a_zero t c lam
  show ((heisMarking t (x0Supported c) (x0Supported lam)).sigma2 ^ 2).z = 0
  rw [pow_two, HeisLift.mul_z, h, smul_zero, map_zero, add_zero, CharTwo.add_self_eq_zero]

/-- **`h₀ ↦ λ(c)`** (Lemma 5.14, the `h₀`-shadow central contribution): on the x₀-supported rep the
central coordinate of the wild `h₀` word is `λ(c)`.  With `g₀` in the base slice, `φ = conj by g₀`
preserves all Heisenberg coordinates, so in the class-two peel `h₀ = φ(x₀)·x₀·φ(d₀)·d₀·d₀²·[φ(d₀),d₀]`
every factor but the leading `φ(x₀)·x₀` cross-term vanishes (`d₀.a = d₀.l = 0`; the paired `z`'s
cancel in char 2), leaving `φ(x₀).l(x₀.a) = λ(c)`. -/
theorem heisMarking_h0_z (t : Marking C) (c : V) (lam : ElemDual V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).h0.z = lam c := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have htaud : ∀ l : ElemDual V, t.τ • l = l := fun l => HeisLift.smul_elemdual_trivial t.τ htau l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  -- leaf coordinates
  have hd0a : M.d0.a = 0 :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported c) hV₂ hx0 htau)
  have hd0l : M.d0.l = 0 :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported lam) hV₂d hx0d htaud)
  have hx0a : M.x₀.a = c := rfl
  have hx0l : M.x₀.l = lam := rfl
  have hx0z : M.x₀.z = 0 := rfl
  have hg0a : M.g0.a = 0 := heisMarking_g0_a_zero t c lam
  have hg0l : M.g0.l = 0 := heisMarking_g0_l_zero t c lam
  have hg0z : M.g0.z = 0 := heisMarking_g0_z_zero t c lam
  have hg0g : ∀ v : V, M.g0.g • v = v := heisMarking_g0_g_smul t (x0Supported c) (x0Supported lam) hU
  have hd0g : ∀ v : V, M.d0.g • v = v := heisMarking_d0_g_smul t (x0Supported c) (x0Supported lam) hx0 htau
  have hdgg : ∀ v : V, M.dg.g • v = v := heisMarking_dg_g_smul t (x0Supported c) (x0Supported lam) hx0 htau
  -- derived φ / d₀² / hc coordinates
  have hφx0z : (conjP M.x₀ M.g0).z = 0 :=
    (HeisLift.conjP_z_of_gslice _ _ hg0a hg0l hg0z hg0g).trans hx0z
  have hφx0l : (conjP M.x₀ M.g0).l = lam :=
    (HeisLift.conjP_l_of_gslice _ _ hg0l hg0g).trans hx0l
  have hdgz : M.dg.z = M.d0.z := HeisLift.conjP_z_of_gslice M.d0 M.g0 hg0a hg0l hg0z hg0g
  have hdga : M.dg.a = 0 := (HeisLift.conjP_a_of_gslice M.d0 M.g0 hg0a hg0g).trans hd0a
  have hd02a : (M.d0 ^ 2).a = 0 := by
    rw [pow_two, HeisLift.mul_a_of_trivial _ _ hd0g, hd0a, add_zero]
  have hd02z : (M.d0 ^ 2).z = 0 := by
    rw [pow_two, HeisLift.mul_z_of_trivial _ _ hd0g, hd0a, map_zero, add_zero,
      CharTwo.add_self_eq_zero]
  have hhca : M.hc.a = 0 := HeisLift.commP_a_of_trivial M.dg M.d0 hdgg hd0g
  have hhcz : M.hc.z = 0 := by
    have h := HeisLift.commP_z_of_trivial M.dg M.d0 hdgg hd0g
    rw [hd0a, hdga, map_zero, map_zero, add_zero] at h; exact h
  -- base-trivialities of the accumulated products
  have hP1g : ∀ v : V, (conjP M.x₀ M.g0).g • v = v := HeisLift.conjP_g_trivial M.x₀ M.g0 hx0
  have hd02g : ∀ v : V, (M.d0 ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ hd0g hd0g v
  have hQ1g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.x₀ hP1g hx0 v
  have hQ2g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.dg hQ1g hdgg v
  have hQ3g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.d0 hQ2g hd0g v
  have hQ4g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ (M.d0 ^ 2) hQ3g hd02g v
  -- the class-two peel
  have e1 : (conjP M.x₀ M.g0 * M.x₀).z = lam c := by
    rw [HeisLift.mul_z_of_trivial _ _ hP1g, hφx0z, hx0z, hφx0l, hx0a, zero_add, zero_add]
  have e2 : (conjP M.x₀ M.g0 * M.x₀ * M.dg).z = lam c + M.d0.z := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ1g, e1, hdgz, hdga, map_zero, add_zero]
  have e3 : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).z = lam c := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ2g, e2, hd0a, map_zero, add_zero, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]
  have e4 : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).z = lam c := by
    rw [HeisLift.mul_z_of_trivial _ _ hQ3g, e3, hd02z, hd02a, map_zero, add_zero, add_zero]
  show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).z = lam c
  rw [HeisLift.mul_z_of_trivial _ _ hQ4g, e4, hhcz, hhca, map_zero, add_zero, add_zero]

omit [Finite C] [Finite V] in
/-- The 2-primary part of a base-slice element is base-slice: central coordinate vanishes. -/
theorem powOmega2_secHom_z (w : C) : (powOmega2 (secHom (A := V) w)).z = 0 := by
  rw [powOmega2, ← map_pow]; rfl

/-- **`[d₀,z₀] ↦ 0`** in the split case: `c₀`'s central coordinate vanishes since `d₀.a = d₀.l = 0`
(the paper's `P + 1 = 0` collapse for `T = 1`). -/
theorem heisMarking_c0_z (t : Marking C) (c : V) (lam : ElemDual V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).c0.z = 0 := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have htaud : ∀ l : ElemDual V, t.τ • l = l := fun l => HeisLift.smul_elemdual_trivial t.τ htau l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  have hd0a : M.d0.a = 0 :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported c) hV₂ hx0 htau)
  have hd0l : M.d0.l = 0 :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u t (x0Supported lam) hV₂d hx0d htaud)
  have hd0g := heisMarking_d0_g_smul t (x0Supported c) (x0Supported lam) hx0 htau
  have hz0g := heisMarking_z0_g_smul t (x0Supported c) (x0Supported lam) hx0
  have h := HeisLift.commP_z_of_trivial M.d0 M.z0 hd0g hz0g
  rw [hd0l, ElemDual.zero_apply, hd0a, map_zero, add_zero] at h
  exact h

/-- `u₁` is a base-slice element on the x₀-rep, so its central coordinate vanishes. -/
theorem heisMarking_u1_z (t : Marking C) (c : V) (lam : ElemDual V) :
    (heisMarking t (x0Supported c) (x0Supported lam)).u1.z = 0 := by
  show (powOmega2 ((heisMarking t (x0Supported c) (x0Supported lam)).x₁ *
    (heisMarking t (x0Supported c) (x0Supported lam)).τ)).z = 0
  rw [show (heisMarking t (x0Supported c) (x0Supported lam)).x₁ *
    (heisMarking t (x0Supported c) (x0Supported lam)).τ = secHom (t.x₁ * t.τ) from by
      rw [map_mul]; rfl]
  exact powOmega2_secHom_z _

/-- `x₁^σ` is a base-slice element on the x₀-rep, so its central coordinate vanishes. -/
theorem heisMarking_x1sig_z (t : Marking C) (c : V) (lam : ElemDual V) :
    (conjP (heisMarking t (x0Supported c) (x0Supported lam)).x₁
      (heisMarking t (x0Supported c) (x0Supported lam)).σ).z = 0 := by
  rw [show conjP (heisMarking t (x0Supported c) (x0Supported lam)).x₁
      (heisMarking t (x0Supported c) (x0Supported lam)).σ = secHom (conjP t.x₁ t.σ) from by
    simp only [conjP, map_mul, map_inv]; rfl]
  rfl

omit [Finite C] [Finite V] in
theorem powOmega2_secHom_a (w : C) : (powOmega2 (secHom (A := V) w)).a = 0 := by
  rw [powOmega2, ← map_pow]; rfl

theorem heisMarking_u1_a (t : Marking C) (x : Fin 4 → V) (y : Fin 4 → ElemDual V) :
    (heisMarking t x y).u1.a = (liftMarking t x).u1.u :=
  congrArg WordLift.u (show agHom (heisMarking t x y).u1 = (liftMarking t x).u1 by
    rw [← Marking.map_u1, heisMarking_map_agHom])

/-- **The split mixed pairing**, wild summand: `B_{ρ,A}(x₀-supported)` central coordinate is `λ(c)`.
Outer peel of `wildValue = h₀·u₁⁻¹·x₁^σ·c₀`: all four factors are trivially-based with vanishing
`.a` (naturality/base-slice), so `.z` is additive, and only `h₀.z = λ(c)` survives (`u₁⁻¹, x₁^σ, c₀`
have `.z = 0`). -/
theorem heisMarking_wildValue_z (t : Marking C) (c : V) (lam : ElemDual V) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (hU : ∀ v : V, t.sigma2 • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z = lam c := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hh0g := heisMarking_h0_g_smul t (x0Supported c) (x0Supported lam) hx0 htau hU
  have hu1g := heisMarking_u1_g_smul t (x0Supported c) (x0Supported lam) hx1 htau
  have hu1invg : ∀ v : V, M.u1⁻¹.g • v = v := fun v => HeisLift.inv_g_trivial M.u1 hu1g v
  have hx1sigg : ∀ v : V, (conjP M.x₁ M.σ).g • v = v := HeisLift.conjP_g_trivial M.x₁ M.σ hx1
  have hu1a : M.u1.a = 0 := by
    rw [show M.u1.a = (liftMarking t (x0Supported c)).u1.u from
        heisMarking_u1_a t (x0Supported c) (x0Supported lam),
      liftMarking_u1_u t (x0Supported c) hV₂ hx1 htau]
    simp [x0Supported]
  have hu1inva : M.u1⁻¹.a = 0 := by rw [HeisLift.inv_a_of_trivial M.u1 hu1g, hu1a, neg_zero]
  have hx1siga : (conjP M.x₁ M.σ).a = 0 := by
    rw [show conjP M.x₁ M.σ = secHom (conjP t.x₁ t.σ) from by
      simp only [conjP, map_mul, map_inv]; rfl]; rfl
  have hc0a : M.c0.a = 0 :=
    (heisMarking_c0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_c0_u t (x0Supported c) hx0 htau hU)
  have hh0z := heisMarking_h0_z t c lam hV₂ hx0 htau hU
  have hu1z := heisMarking_u1_z t c lam
  have hu1invz : M.u1⁻¹.z = 0 := by rw [HeisLift.inv_z, hu1z, hu1a, map_zero, add_zero]
  have hx1sigz := heisMarking_x1sig_z t c lam
  have hc0z := heisMarking_c0_z t c lam hV₂ hx0 htau
  have hQ2g : ∀ v : V, (M.h0 * M.u1⁻¹).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ M.u1⁻¹ hh0g hu1invg v
  have hQ3g : ∀ v : V, (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ (conjP M.x₁ M.σ) hQ2g hx1sigg v
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).z = lam c
  rw [HeisLift.mul_z_of_trivial _ _ hQ3g, hc0z, hc0a, map_zero, add_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hQ2g, hx1sigz, hx1siga, map_zero, add_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hh0g, hh0z, hu1invz, hu1inva, map_zero, add_zero, add_zero]

/-! ### Ramified mixed Hessian (P-13c): `U = σ₂` acts nontrivially

The ramified degree-one pairing `B(c,λ) = λ((1 + U + U⁻¹)c)`.  Two central contributions:
`h₀ ↦ λ(c)` (the shadow, with all `U²`-twisted cross-terms cancelling in char 2) and
`[d₀,z₀] ↦ λ(Uc) + λ(U⁻¹c)` (the symplectic commutator, now nonzero since `Dd₀ = c ≠ 0`).  Unlike
the split case `g₀ = σ₂²` is not `g`-slice, so the peel uses `conjP_*_of_slice` to track the
`U`-action. -/

omit [Finite C] in
/-- Contragredient fixed-point-freeness: if `T = τ` has no nonzero fixed vector on the finite
module `V` (`V^T = 0`), then the same holds on the dual `V^∨`.  (`T − 1` injective ⟹ surjective on
finite `V`; the dual `T^∨ − 1` is then injective.)  Supplies the ramified `d₀.l = λ` computation. -/
theorem elemDual_fixedPointFree_of (t : Marking C)
    (htau : ∀ v : V, t.τ • v = v → v = 0) :
    ∀ lam : ElemDual V, t.τ • lam = lam → lam = 0 := by
  have hsurj : Function.Surjective (fun w : V => t.τ⁻¹ • w - w) :=
    (Finite.injective_iff_surjective).mp (fun a b hab => by
      have hab' : t.τ⁻¹ • a - a = t.τ⁻¹ • b - b := hab
      have hfix : t.τ • (a - b) = (a - b) := by
        have h2 : t.τ⁻¹ • (a - b) = a - b := by
          rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]; exact hab'
        calc t.τ • (a - b) = t.τ • (t.τ⁻¹ • (a - b)) := by rw [h2]
          _ = a - b := smul_inv_smul t.τ (a - b)
      exact sub_eq_zero.mp (htau (a - b) hfix))
  intro lam hlam
  ext v
  obtain ⟨w, hw⟩ := hsurj v
  have hlw : lam (t.τ⁻¹ • w) = lam w := by
    have h := congrFun (congrArg (DFunLike.coe) hlam) w
    rwa [ElemDual.smul_apply] at h
  show lam v = 0
  rw [← hw, map_sub, hlw, sub_self]

/-- **`h₀ ↦ λ(c)`** (ramified Lemma 5.14).  Unlike the split case, `g₀ = σ₂²` acts *nontrivially*
(`U²`), so the conjugation `φ = ·^{g₀}` shifts the `A`/`A^∨` coordinates by `U⁻²`; but every
Heisenberg base still acts trivially on `V` (the conjugation cancels `U²`), so the class-two peel is
a `mul_z_of_trivial` computation whose `U²`-twisted cross-terms cancel in char 2, leaving `λ(c)`. -/
theorem heisMarking_h0_z_ramified (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).h0.z = lam c := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  -- dual-side hypotheses
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  have htaud : ∀ l : ElemDual V, t.τ • l = l → l = 0 := elemDual_fixedPointFree_of t htau
  have hToddd : ∀ l : ElemDual V, powOmega2 t.τ • l = l :=
    fun l => HeisLift.smul_elemdual_trivial (powOmega2 t.τ) hTodd l
  -- `d₀` coordinates (ramified: `a = c`, `l = lam`, base trivial)
  have hD_a : M.d0.a = c :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported c) hV₂ hx0 htau hTodd)
  have hD_l : M.d0.l = lam :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported lam) hV₂d hx0d htaud hToddd)
  have hD_g : ∀ v : V, M.d0.g • v = v := fun v => by
    rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_ramified t (x0Supported c) hx0 hTodd v
  -- `g₀` base-slice (`a = l = z = 0`, base `U²`)
  have hg0a : M.g0.a = 0 := heisMarking_g0_a_zero t c lam
  have hg0l : M.g0.l = 0 := heisMarking_g0_l_zero t c lam
  have hg0z : M.g0.z = 0 := heisMarking_g0_z_zero t c lam
  -- `x₀`
  have hX_a : M.x₀.a = c := rfl
  have hX_l : M.x₀.l = lam := rfl
  have hX_z : M.x₀.z = 0 := rfl
  have hX_g : ∀ v : V, M.x₀.g • v = v := hx0
  -- factor base-trivialities
  have hP_g : ∀ v : V, (conjP M.x₀ M.g0).g • v = v := HeisLift.conjP_g_trivial M.x₀ M.g0 hx0
  have hDg_g : ∀ v : V, M.dg.g • v = v := HeisLift.conjP_g_trivial M.d0 M.g0 hD_g
  -- factor `a/l/z` coordinates
  have hP_a : (conjP M.x₀ M.g0).a = M.g0.g⁻¹ • c := by
    rw [HeisLift.conjP_a_of_slice M.x₀ M.g0 hg0a, hX_a]
  have hP_l : (conjP M.x₀ M.g0).l = M.g0.g⁻¹ • lam := by
    rw [HeisLift.conjP_l_of_slice M.x₀ M.g0 hg0l, hX_l]
  have hP_z : (conjP M.x₀ M.g0).z = 0 := by
    rw [HeisLift.conjP_z_of_slice M.x₀ M.g0 hg0a hg0l hg0z, hX_z]
  have hDg_a : M.dg.a = M.g0.g⁻¹ • c := by
    show (conjP M.d0 M.g0).a = _; rw [HeisLift.conjP_a_of_slice M.d0 M.g0 hg0a, hD_a]
  have hDg_l : M.dg.l = M.g0.g⁻¹ • lam := by
    show (conjP M.d0 M.g0).l = _; rw [HeisLift.conjP_l_of_slice M.d0 M.g0 hg0l, hD_l]
  have hDg_z : M.dg.z = M.d0.z := by
    show (conjP M.d0 M.g0).z = _; rw [HeisLift.conjP_z_of_slice M.d0 M.g0 hg0a hg0l hg0z]
  -- `d₀²`
  have hD2_a : (M.d0 ^ 2).a = 0 := by
    rw [pow_two, HeisLift.mul_a_of_trivial _ _ hD_g, hD_a]; exact hV₂ c
  have hD2_l : (M.d0 ^ 2).l = 0 := by
    rw [pow_two, HeisLift.mul_l_of_trivial _ _ hD_g, hD_l]; exact hV₂d lam
  have hD2_z : (M.d0 ^ 2).z = lam c := by
    rw [pow_two, HeisLift.mul_z_of_trivial _ _ hD_g, hD_l, hD_a, CharTwo.add_self_eq_zero, zero_add]
  -- `[φ(d₀),d₀]`
  have hHc_a : M.hc.a = 0 := HeisLift.commP_a_of_trivial M.dg M.d0 hDg_g hD_g
  have hHc_z : M.hc.z = lam (M.g0.g • c) + lam (M.g0.g⁻¹ • c) := by
    show (commP M.dg M.d0).z = _
    rw [HeisLift.commP_z_of_trivial M.dg M.d0 hDg_g hD_g, hDg_l, hD_a, hD_l, hDg_a,
      ElemDual.smul_apply, inv_inv]
  -- prefix base-trivialities
  have hQ2g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hP_g hX_g v
  have hQ3g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hQ2g hDg_g v
  have hQ4g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hQ3g hD_g v
  have hD2g : ∀ v : V, (M.d0 ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ hD_g hD_g v
  have hQ5g : ∀ v : V, (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).g • v = v :=
    fun v => HeisLift.mul_g_trivial _ _ hQ4g hD2g v
  -- peel `h₀ = φ(x₀)·x₀·φ(d₀)·d₀·d₀²·[φ(d₀),d₀]`
  show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).z = lam c
  rw [HeisLift.mul_z_of_trivial _ _ hQ5g, HeisLift.mul_z_of_trivial _ _ hQ4g,
    HeisLift.mul_z_of_trivial _ _ hQ3g, HeisLift.mul_z_of_trivial _ _ hQ2g,
    HeisLift.mul_z_of_trivial _ _ hP_g,
    HeisLift.mul_l_of_trivial _ _ hQ4g, HeisLift.mul_l_of_trivial _ _ hQ3g,
    HeisLift.mul_l_of_trivial _ _ hQ2g, HeisLift.mul_l_of_trivial _ _ hP_g,
    hP_z, hX_z, hDg_z, hD2_z, hHc_z, hP_l, hX_l, hDg_l, hD2_l, hHc_a, hX_a, hDg_a, hD_a, hD2_a]
  simp only [ElemDual.add_apply, ElemDual.smul_apply, inv_inv, smul_inv_smul, ElemDual.zero_apply,
    map_zero, smul_zero, add_zero, zero_add]
  generalize lam c = a
  generalize lam (M.g0.g • c) = b
  generalize lam (M.g0.g⁻¹ • c) = e
  generalize M.d0.z = δ
  revert a b e δ
  decide

/-- **`[d₀,z₀] ↦ λ(Uc) + λ(U⁻¹c)`** (ramified Lemma 5.14, `U = σ₂`).  On the x₀-rep `Dd₀ = c` and
`Dz₀ = U⁻¹c`; the Heisenberg commutator symplectic form `commP_z_of_trivial` gives
`[d₀,z₀].z = d₀.l(z₀.a) + z₀.l(d₀.a) = λ(U⁻¹c) + (U⁻¹λ)(c) = λ(U⁻¹c) + λ(Uc)`. -/
theorem heisMarking_c0_z_ramified (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).c0.z
      = lam (t.sigma2⁻¹ • c) + lam (t.sigma2 • c) := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hx0d : ∀ l : ElemDual V, t.x₀ • l = l := fun l => HeisLift.smul_elemdual_trivial t.x₀ hx0 l
  have hV₂d : ∀ l : ElemDual V, l + l = 0 := fun l => by
    ext v; simp only [ElemDual.add_apply, ElemDual.zero_apply]; exact CharTwo.add_self_eq_zero (l v)
  have htaud : ∀ l : ElemDual V, t.τ • l = l → l = 0 := elemDual_fixedPointFree_of t htau
  have hToddd : ∀ l : ElemDual V, powOmega2 t.τ • l = l :=
    fun l => HeisLift.smul_elemdual_trivial (powOmega2 t.τ) hTodd l
  have hD_a : M.d0.a = c :=
    (heisMarking_d0_a t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported c) hV₂ hx0 htau hTodd)
  have hD_l : M.d0.l = lam :=
    (heisMarking_d0_l t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_d0_u_ramified t (x0Supported lam) hV₂d hx0d htaud hToddd)
  have hD_g : ∀ v : V, M.d0.g • v = v := fun v => by
    rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_ramified t (x0Supported c) hx0 hTodd v
  have hsig_g : M.sigma2.g = t.sigma2 :=
    (heisMarking_sigma2_g_eq t (x0Supported c) (x0Supported lam)).trans
      (liftMarking_sigma2_g t (x0Supported c))
  have hX_a : M.x₀.a = c := rfl
  have hX_l : M.x₀.l = lam := rfl
  have hz0a : M.z0.a = t.sigma2⁻¹ • c := by
    show (conjP M.x₀ M.sigma2).a = _
    rw [HeisLift.conjP_a_of_slice M.x₀ M.sigma2 (heisMarking_sigma2_a_zero t c lam), hX_a, hsig_g]
  have hz0l : M.z0.l = t.sigma2⁻¹ • lam := by
    show (conjP M.x₀ M.sigma2).l = _
    rw [HeisLift.conjP_l_of_slice M.x₀ M.sigma2 (heisMarking_sigma2_l_zero t c lam), hX_l, hsig_g]
  have hz0g : ∀ v : V, M.z0.g • v = v :=
    heisMarking_z0_g_smul t (x0Supported c) (x0Supported lam) hx0
  show (commP M.d0 M.z0).z = _
  rw [HeisLift.commP_z_of_trivial M.d0 M.z0 hD_g hz0g, hD_l, hz0a, hz0l, hD_a,
    ElemDual.smul_apply, inv_inv]

/-- **The ramified mixed pairing, wild summand**: `wildValue.z = λ((1 + U + U⁻¹)c)`.  The peel
`wildValue = h₀·u₁⁻¹·(x₁^σ)·c₀`: `u₁⁻¹` and `x₁^σ` are pure `secHom` base elements (`a = l = z = 0`),
so right-multiplication by them preserves `.z`; only `h₀.z = λ(c)` and `c₀.z = λ(Uc) + λ(U⁻¹c)`
survive. -/
theorem heisMarking_wildValue_z_ramified (t : Marking C) (c : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z
      = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c) := by
  set M := heisMarking t (x0Supported c) (x0Supported lam) with hM
  have hh0z : M.h0.z = lam c := heisMarking_h0_z_ramified t c lam hV₂ hx0 htau hTodd
  have hc0z : M.c0.z = lam (t.sigma2⁻¹ • c) + lam (t.sigma2 • c) :=
    heisMarking_c0_z_ramified t c lam hV₂ hx0 htau hTodd
  -- base-trivialities for `c₀.a`
  have hD_g : ∀ v : V, M.d0.g • v = v := fun v => by
    rw [heisMarking_d0_g_eq]; exact liftMarking_d0_g_ramified t (x0Supported c) hx0 hTodd v
  have hz0g : ∀ v : V, M.z0.g • v = v :=
    heisMarking_z0_g_smul t (x0Supported c) (x0Supported lam) hx0
  have hc0a : M.c0.a = 0 := HeisLift.commP_a_of_trivial M.d0 M.z0 hD_g hz0g
  -- pure-base coordinates of `u₁` and `x₁^σ`
  have hu1a : M.u1.a = 0 := by
    show (powOmega2 (M.x₁ * M.τ)).a = 0
    rw [show M.x₁ * M.τ = secHom (t.x₁ * t.τ) from by rw [map_mul]; rfl]
    exact powOmega2_secHom_a _
  have hu1z : M.u1.z = 0 := heisMarking_u1_z t c lam
  have hu1inva : M.u1⁻¹.a = 0 := by rw [HeisLift.inv_a, hu1a, smul_zero, neg_zero]
  have hu1invz : M.u1⁻¹.z = 0 := by rw [HeisLift.inv_z, hu1a, map_zero, add_zero, hu1z]
  have hx1sa : (conjP M.x₁ M.σ).a = 0 := by
    rw [show conjP M.x₁ M.σ = secHom (conjP t.x₁ t.σ) from by
      simp only [conjP, map_mul, map_inv]; rfl]; rfl
  have hx1sz : (conjP M.x₁ M.σ).z = 0 := heisMarking_x1sig_z t c lam
  -- right-multiplication by a pure-base element preserves `.z`
  have hmulpure : ∀ (p q : HeisLift V C), q.a = 0 → q.z = 0 → (p * q).z = p.z :=
    fun p q hqa hqz => by rw [HeisLift.mul_z, hqa, smul_zero, map_zero, add_zero, hqz, add_zero]
  have hX4z : (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ).z = M.h0.z := by
    rw [hmulpure _ _ hx1sa hx1sz, hmulpure _ _ hu1inva hu1invz]
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).z = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c)
  rw [HeisLift.mul_z, hc0a, smul_zero, map_zero, add_zero, hX4z, hh0z, hc0z, map_add, map_add]
  abel

end HessianRow

section NormalForms

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

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
(`wild_acts_trivially`); `hVS` is `V^S = 0`, i.e. `1 + S⁻¹` invertible — it excludes the trivial
module `𝔽₂` (where `1 + S⁻¹ = 0` and the `x 3 = 0` clause would fail; that module is handled
separately in `prop_5_15`).  `hU` is the σ-tameness (`σ₂ = U` acts trivially).  Both `hVS` and `hU`
are *derivable* in the split case — with `τ, x₀, x₁` acting trivially the `C`-action factors through
the cyclic `⟨σ̄⟩`, so a nontrivial simple `V` is a simple `𝔽₂[⟨σ⟩]`-module: `V^S = V^C = 0` and `σ`
has odd order (⇒ `σ₂ = 1`).  Those derivations need `t.Generates` and simple-cyclic rep theory, so
they are factored out as hypotheses here, keeping the normal-form proof pure finite-Fox calculus.
See `docs/p13-normal-form-hypothesis-gap.md` §7.

Proved (P-13): `B¹` half from `b1w_split_shape`; `Z¹` half from the tame row `d1Fun_tame_split`
(`= S⁻¹·x₁`) and the wild row `liftMarking_wildValue_u` (`= x₁ + (1+S⁻¹)·x₃`), with `x 1 = 0` from
`S⁻¹` injective and `x 3 = 0` from `hVS`. -/
theorem lemma_5_13_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (hVS : ∀ v : V, t.σ • v = v → v = 0) :
    (∀ x : Fin 4 → V, x ∈ Z1w (A := V) t ↔ x 1 = 0 ∧ x 3 = 0) ∧
    (∀ y : Fin 4 → V, y ∈ B1w (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0]) := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
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

/-- **Lemma 5.13, ramified case (ii), unique normal form**: if `V^T = 0`, every degree-one
class has a unique representative supported on `x₀` (display (53)).

Hypothesis `hcore` supplies trivial wild action (`wild_acts_trivially`); the ramified condition
`V^T = 0` (`htau`) gives `1 + T` invertible.

**Hypothesis `hTodd`** (added P-13b, 2026-07-04): `τ`'s 2-primary part `powOmega2 t.τ` acts
trivially on `V`, i.e. `τ` acts with *odd* order on `V`.  This is the ramified analogue of the
split case's `hU : ∀ v, t.sigma2 • v = v` (`sigma2 = powOmega2 t.σ`), and is the arithmetic fact
that `τ = ` tame inertia is prime-to-2, so acts through an odd quotient on the `𝔽₂`-module `V`.
It is **required** (not implied by `V^T = 0`, which admits even-order fixed-point-free actions):
the wild-row aux offset `(powOmega2 p).u` is a geometric sum whose length is the `ω₂`-exponent,
and it collapses to `0` (via the `P = 0` norm ledger `WordLift.norm_eq_zero_of_fixedPointFree`)
exactly because the odd action-period divides that length.  Like `hU`/`hVS` in the split case,
this is factored out as an explicit hypothesis, to be supplied per simple factor by P-13d.
See `docs/p13-normal-form-hypothesis-gap.md` and P-13b in `docs/p13-ticket-split.md`.

*Status*: hypothesis amended (P-13b); `P = 0` ledger landed; the wild/tame rows + `∃!`-assembly
remain sorried.

**Signature note (P-13f, 2026-07-05)**: the trivial wild action is now taken as hypotheses
`hx0`/`hx1` rather than derived from `(hsimple, hcore)` via `wild_acts_trivially` — so the lemma
applies to the contragredient dual `A∨` (whose wild-triviality transfers from `A`'s) without a
"dual of simple is simple" detour, mirroring the split-side `split_shapes_of_wild`.

**`hU` REMOVED (P-13f de-`hU`, 2026-07-05)**: the σ-tameness `∀ v, σ₂ • v = v` is *not derivable
from admissibility* (`S₃` on its 2-dim simple module and `C₅⋊C₄` on `𝔽₁₆`, markings `x₀=x₁=1`,
are admissible ramified counterexamples), and it is not needed: the `h₀`-row `x₂`-cancellation
happens in `g₀`-conjugate pairs (`liftMarking_h0_u_ramified`, via `conjP_u_of_base_trivial`). -/
theorem lemma_5_13_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    ∀ x ∈ Z1w (A := V) t, ∃! c : V, x - x0Supported c ∈ B1w (A := V) t := by
  -- `T − 1` is injective (`V^T = 0`) hence surjective on the finite space `V`.
  have hTsurj : Function.Surjective (fun w : V => t.τ • w - w) :=
    (Finite.injective_iff_surjective).mp (fun a b hab => by
      have hab' : t.τ • a - a = t.τ • b - b := hab
      exact sub_eq_zero.mp (htau (a - b)
        (by rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]; exact hab')))
  intro x hx
  rw [Z1w, AddMonoidHom.mem_ker] at hx
  -- Wild row `S⁻¹·x₃ = 0` forces `x₃ = 0`.
  have hx3 : x 3 = 0 := by
    have hwild : (liftMarking t x).wildValue.u = 0 := congrArg Prod.snd hx
    rw [liftMarking_wildValue_u_ramified t x hV₂ hx0 hx1 htau hTodd] at hwild
    rw [← smul_inv_smul t.σ (x 3), hwild, smul_zero]
  -- `v = (T − 1)⁻¹ x₁`; subtracting `d⁰v` kills the `x₁`-slot.
  obtain ⟨v, hv⟩ := hTsurj (x 1)
  have hv2 : t.τ • v - v = x 1 := hv
  have hc0 : (x - d0 t v) 0 = x 0 - (t.σ • v - v) := by
    simp only [Pi.sub_apply, d0, AddMonoidHom.mk'_apply, Matrix.cons_val_zero]
  have hc1 : (x - d0 t v) 1 = 0 := by
    simp only [Pi.sub_apply, d0, AddMonoidHom.mk'_apply, Matrix.cons_val_one, Matrix.cons_val_zero]
    rw [hv2, sub_self]
  have hxcob : d1Fun t (x - d0 t v) = 0 := by
    have hsub : d1 t (x - d0 t v) = d1 t x - d1 t (d0 t v) := (d1 t).map_sub x (d0 t v)
    rw [hx, show d1 t (d0 t v) = d1Fun t (d0 t v) from rfl, d1Fun_comp_d0 t ht hw v, sub_zero]
      at hsub
    exact hsub
  -- The reduced cocycle's tame row `σ⁻¹(T − 1)x'₀ = 0` forces `x'₀ = 0`, i.e. `x₀ = (S − 1)v`.
  have hx'0 : x 0 - (t.σ • v - v) = 0 := by
    have ht' : (d1Fun t (x - d0 t v)).1 = 0 := congrArg Prod.fst hxcob
    rw [d1Fun_tame t ht (x - d0 t v), hc0, hc1] at ht'
    simp only [smul_zero, add_zero, sub_zero] at ht'
    rw [sub_eq_zero] at ht'
    refine htau (x 0 - (t.σ • v - v)) ?_
    have h3 := congrArg (fun w => t.σ • w) ht'
    simpa only [smul_inv_smul] using h3
  have hx0v : x 0 = t.σ • v - v := sub_eq_zero.mp hx'0
  -- Hence `x − x0Supported(x₂) = d⁰v`, and `c = x₂` is the unique witness.
  have hcob : x - x0Supported (x 2) = d0 t v := by
    funext i
    fin_cases i <;> simp [Pi.sub_apply, x0Supported, d0, hx0, hx1, hx3, hx0v, ← hv2]
  refine ⟨x 2, ?_, fun c hc => ?_⟩
  · simp only [B1w, AddMonoidHom.mem_range]; exact ⟨v, hcob.symm⟩
  · simp only [B1w, AddMonoidHom.mem_range] at hc
    obtain ⟨w, hw'⟩ := hc
    have h := congrFun hw' 2
    have hcw : (0 : V) = x 2 - c := by simpa [d0, x0Supported, hx0, Pi.sub_apply] using h
    exact (sub_eq_zero.mp hcw.symm).symm

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
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  show (heisMarking t (x0Supported c) (x0Supported lam)).tameValue.z
      + (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z = lam c
  rw [heisMarking_tameValue_z_eq_zero t (x0Supported c) (x0Supported lam) rfl rfl rfl rfl,
    heisMarking_wildValue_z t c lam hV₂ hx0 hx1 htau hU, zero_add]

/-- **Lemma 5.13, pairing display (54), ramified case**: when `V^T = 0` the pairing on
`x₀`-supported representatives is `(c, λ) ↦ λ((1 + U + U⁻¹)c)` for `U = S₂^ω`
(`Marking.sigma2`).

The tame relator's central coordinate vanishes on the x₀-supported rep
(`heisMarking_tameValue_z_eq_zero`), so the pairing is carried entirely by the wild relator
(`heisMarking_wildValue_z_ramified`): `h₀ ↦ λ(c)` (the shadow) plus the `[d₀,z₀]` symplectic term
`λ(Uc) + λ(U⁻¹c)` (nonzero here because `Dd₀ = c ≠ 0`, unlike the split `P + 1 = 0` collapse).

**Hypothesis `hTodd`** (added P-13c, mirroring P-13b's `lemma_5_13_ramified`): `τ`'s 2-primary part
acts trivially on `V` (tame inertia is prime-to-2), needed for the ramified `Dd₀ = c` via the
`P = 0` ledger.  Supplied per simple factor by P-13d.  The trivial wild action is taken as
hypotheses `hx0`/`hx1` (P-13f signature note on `lemma_5_13_ramified`). -/
theorem lemma_5_13_pairing_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (c : V)
    (lam : ElemDual V) :
    mixedB t (x0Supported c) (x0Supported (V := ElemDual V) lam)
      = lam (c + t.sigma2 • c + t.sigma2⁻¹ • c) := by
  show (heisMarking t (x0Supported c) (x0Supported lam)).tameValue.z
      + (heisMarking t (x0Supported c) (x0Supported lam)).wildValue.z = _
  rw [heisMarking_tameValue_z_eq_zero t (x0Supported c) (x0Supported lam) rfl rfl rfl rfl,
    heisMarking_wildValue_z_ramified t c lam hV₂ hx0 hx1 htau hTodd, zero_add]

end NormalForms

section MainDuality

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/- **Prop 5.15 relocated to `GQ2/DualityAssembly.lean` (P-13f) — PROVED, no sorry.**  The proof
composes the dévissage strong induction `prop_5_15_of_simple` (`GQ2/DevissageInduction.lean`,
via `lemma_5_11`) with the simple case `selfDual_of_simple` (split/ramified dichotomy) — all of
which live in files importing *this* one, so proving it here would be an import cycle.  The
qualified name `GQ2.FoxH.prop_5_15` and the statement are unchanged. -/

/- **§5.16–§5.17 relocated to `GQ2/LocalLiftingDuality.lean` (P-13g).**  `prop_5_16` (local
lifting duality) and its corollary `cor_5_17_card` moved there so their proofs can invoke B6
(`GQ2.tateDuality`) and the `𝔽₂`-cup transport, which live in files that import *this* one —
proving them here would be an import cycle.  Both keep their `GQ2.FoxH.*` qualified names, so
downstream references are unaffected.  `prop_5_15` (P-13f) stays above. -/

end MainDuality

end FoxH

end GQ2
