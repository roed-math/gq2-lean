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

/-- The base projection `HeisLift A C →* C`. -/
def gHom : HeisLift A C →* C where
  toFun := HeisLift.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem gHom_apply (p : HeisLift A C) : gHom p = p.g := rfl

/-- The central element `⟨0, 0, w, 1⟩` (the paper's `z(w)`).  It is genuinely central. -/
noncomputable def zc (w : ZMod 2) : HeisLift A C := ⟨0, 0, w, 1⟩

@[simp] theorem zc_z (w : ZMod 2) : (zc (A := A) (C := C) w).z = w := rfl

theorem mul_zc (p : HeisLift A C) (w : ZMod 2) : p * zc w = ⟨p.a, p.l, p.z + w, p.g⟩ := by
  ext <;> simp [zc, mul_a, mul_l, mul_z, mul_g]

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

/-- **Lemma 5.7, display (38)**: for a word `r` with trivial lower value, evaluating at the
generic coboundary `x = d⁰a = ((cᵢ−1)a)ᵢ` gives
`β_r(d⁰a, y) = ⟨a, L^{A^∨}_r(y)⟩ + Σᵢ εᵢ(r)·yᵢ(cᵢa)`.

*Status*: sorried (P-13; central-conjugation bookkeeping in `H(A) ⋊ C`). -/
theorem lemma_5_7_left (c : Fin n → C) (r : FreeGroup (Fin n))
    (hr : FreeGroup.lift c r = 1) (a : A) (y : Fin n → ElemDual A) :
    (stokesEval c (fun i => c i • a - a) y r).z
      = (stokesEval c 0 y r).l a
        + ∑ i, (Multiplicative.toAdd (expMod2 i r)) * (y i (c i • a)) := by
  sorry

/-- **Lemma 5.7, display (39)**: the dual-variable form,
`β_r(x, d⁰λ) = ⟨L^A_r(x), λ⟩ + Σᵢ εᵢ(r)·λ(xᵢ)`.

*Status*: sorried (P-13). -/
theorem lemma_5_7_right (c : Fin n → C) (r : FreeGroup (Fin n))
    (hr : FreeGroup.lift c r = 1) (x : Fin n → A) (lam : ElemDual A) :
    (stokesEval c x (fun i => c i • lam - lam) r).z
      = lam ((stokesEval c x 0 r).a)
        + ∑ i, (Multiplicative.toAdd (expMod2 i r)) * (lam (x i)) := by
  sorry

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

/-- **Prop 5.8, display (41)** (= chain identity (47) of Prop 5.10 under the canonical
identifications): `B_{ρ,A}(d⁰a, y) = ⟨a, L^{A^∨}_t(y) + L^{A^∨}_w(y)⟩`, where the dual
first relation differentials are `d1Fun` on `A^∨`.

*Status*: sorried (P-13; via Lemma 5.7 at the two relator words with trace coefficients
`(1,1)` — their mod-2 exponent vectors are both `(0,1,0,0)`, so the corrections cancel). -/
theorem prop_5_8_left (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (a : A)
    (y : Fin 4 → ElemDual A) :
    mixedB t (d0 t a) y
      = ((d1Fun (A := ElemDual A) t y).1 + (d1Fun (A := ElemDual A) t y).2) a := by
  sorry

/-- **Prop 5.8, display (42)** (= chain identity (48)): `B_{ρ,A}(x, d⁰λ) = ⟨L_t(x)+L_w(x), λ⟩`.

*Status*: sorried (P-13). -/
theorem prop_5_8_right (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (x : Fin 4 → A)
    (lam : ElemDual A) :
    mixedB t x (d0 (A := ElemDual A) t lam)
      = lam ((d1Fun t x).1 + (d1Fun t x).2) := by
  sorry

/-- **Lemma 5.6 (strict coefficient naturality)**, in the traced form Prop 5.10 uses: for an
equivariant `f : A → A'`, `B_{A'}(f∗x, y') = B_A(x, f^∨ y')`.

*Status*: sorried (P-13; evaluate in the mixed Heisenberg group `A × A'^∨ × 𝔽₂`). -/
theorem lemma_5_6 {A' : Type*} [AddCommGroup A'] [DistribMulAction C A'] (f : A →+ A')
    (hf : ∀ (g : C) (a : A), f (g • a) = g • f a) (t : Marking C) (x : Fin 4 → A)
    (y' : Fin 4 → ElemDual A') :
    mixedB t (fun i => f (x i)) y'
      = mixedB t x (fun i => ((y' i : A' →+ ZMod 2).comp f : ElemDual A)) := by
  sorry

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
simplicity forces it to be all of `V`.  (Proved for P-13; the remaining §5 sorries concentrate
in the Heisenberg word-evaluation core — `d1Fun_add`, 5.6, 5.7 — see the P-13 note.) -/
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

section NormalForms

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- The degree-one tuple supported on the `x₀`-slot (display (53)'s normal form). -/
def x0Supported (c : V) : Fin 4 → V := ![0, 0, c, 0]

/-- **Lemma 5.13, split case (i), cocycle shape**: if `T = 1` (trivial `τ`-action on a
nontrivial simple module), `Z¹ = {(a, 0, c, 0)}` and `B¹ = {((S−1)v, 0, 0, 0)}`.

*Status*: sorried (P-13; uses invertibility of `1 + S⁻¹` from simplicity). -/
theorem lemma_5_13_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (htau : ∀ v : V, t.τ • v = v) :
    (∀ x : Fin 4 → V, x ∈ Z1w (A := V) t ↔ x 1 = 0 ∧ x 3 = 0) ∧
    (∀ y : Fin 4 → V, y ∈ B1w (A := V) t ↔ ∃ v : V, y = ![t.σ • v - v, 0, 0, 0]) := by
  sorry

/-- **Lemma 5.13, ramified case (ii), unique normal form**: if `V^T = 0`, every degree-one
class has a unique representative supported on `x₀` (display (53)).

*Status*: sorried (P-13). -/
theorem lemma_5_13_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (htau : ∀ v : V, t.τ • v = v → v = 0) :
    ∀ x ∈ Z1w (A := V) t, ∃! c : V, x - x0Supported c ∈ B1w (A := V) t := by
  sorry

/-- **Lemma 5.13, pairing display (54), split case**: on `x₀`-supported representatives the
degree-one pairing is `(c, λ) ↦ λ(c)` when `T = 1`.

*Status*: sorried (P-13; via the mixed Hessian ledger, Lemma 5.14). -/
theorem lemma_5_13_pairing_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (htau : ∀ v : V, t.τ • v = v) (c : V) (lam : ElemDual V) :
    mixedB t (x0Supported c) (x0Supported (V := ElemDual V) lam) = lam c := by
  sorry

/-- **Lemma 5.13, pairing display (54), ramified case**: when `V^T = 0` the pairing on
`x₀`-supported representatives is `(c, λ) ↦ λ((1 + U + U⁻¹)c)` for `U = S₂^ω`
(`Marking.sigma2`).

*Status*: sorried (P-13). -/
theorem lemma_5_13_pairing_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (htau : ∀ v : V, t.τ • v = v → v = 0) (c : V)
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

*Status*: sorried (P-13; route: 5.12 + 5.13 for simples — including the trivial module, where
the traced form is the scalar cup–Bockstein table (25) — then 5.11 dévissage along a
composition series). -/
theorem prop_5_15 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
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
    (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
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
  obtain ⟨hc2, hc1, -⟩ := prop_5_15 t ht hw (A := A) hA₂
  obtain ⟨hl2, hl1, -⟩ := prop_5_16 ρ hρ (A := A) hcomp hA₂ hcompD htriv hpair
  exact ⟨hc1.trans hl1.symm, hc2.trans hl2.symm⟩

end MainDuality

end FoxH

end GQ2
