# P-25 sub-plan: deriving `tame_reciprocity` from B5 (no new axiom)

Target (`GQ2/BoundaryMapsWitness.lean`, the sole remaining P-25 sorry):

```
tame_reciprocity : ∀ g, ι(ν_t(tameF g)) = ν_ur(toAb g)
```

`tameF` from B10 (`prop_3_2_local`), `ν_ur` from B5, `ι = ztwoEquivPadic`.  Equivalent (via the
proved `prop_3_10_local_marked`) to `compatF : ν_t∘tameF = ν₂∘pro2F`.

## Analysis summary (2026-07-05, Opus/Fable)

Write `f₁ := ι∘ν_t∘tameF : G_{ℚ₂} → Multiplicative ℤ₂`.  Since `Mult ℤ₂` is abelian pro-2, `f₁`
factors through `G(2) = D₀` and then its abelianization `B = D₀^{ab} ≅ ℤ/2⟨t⟩ × ℤ₂⟨S̄⟩ × ℤ₂⟨Ȳ⟩`
(eq. (11), P-07's `BDecomposition`).  So `f₁` is determined by two 2-adic parameters
`(β, γ) = (λ(S̄), λ(Ȳ))`; torsion `t` dies automatically, and `λ(Ā) = β⁻²` is forced.  The goal
is `(β, γ) = (ztwoOne-side 1, 0)` matched against `ν_ur`'s `(1, 0)` (prop_1_1's `(−2,1,0)` row).

Via P-07's `markedHom_bijective` (`Ā,S̄,Ȳ ↔` classes of `rec(−4), rec(1/2), rec(−3)`), the goal
reduces to exactly **two atomic values** of `μ := f₁-descended ∘ rec : ℚ₂ˣ → Mult ℤ₂`:

* **(F)**  `μ(2) = ofAdd(−1)`   (uniformizer ↦ arithmetic Frobenius, geometric coordinate −1);
* **(U₋₃)** `μ(−3) = 1`         (the unit −3 dies — "units are unramified-trivial").

(`μ(−1) = 1` is free: torsion into torsion-free.  `−4 = (−1)·2²` handles the Ā-row.)

Facts established en route, worth banking regardless:

1. **Witness-rigidity of `f₁`** (formalizable, axiom-free): all B10 witnesses share `W`
   (Lemma 3.3 maximality, proved) and `Aut(Ttame)` acts trivially on `Ttame^{ab} = Ẑ` — an
   automorphism sends `σ ↦ σ^u·i`, and the relation `σ⁻¹τσ = τ²` forces `2^u = 2` on the odd
   procyclic inertia `I = ⟨⟨τ⟩⟩`; primes `p ∣ 2^{2^k}+1` have `ord_p(2) = 2^{k+1}`, so the
   ℤ₂-component of `u` is `1`.  (Repo already has the `emN = 2^{2^m}−1` order machinery;
   Fermat-factor primes are the explicit 2-power-order source.)  Hence `f₁` is canonical.
   Corollaries: `⟨⟨τ⟩⟩ = closure of derived subgroup` in `Ttame` (since `τ = [σ⁻¹,τ]·…`), so
   `Ttame^{ab} ≅ Ẑ`; inertia is characteristic.
2. **The gap is irreducible to abelian data**: `ker λ` (the tame character's kernel in `D₀`)
   equals the image of the B10 inertia; whether `rec(−3)` lies in it — (U₋₃) — is precisely
   the statement that the B10 tame quotient is *unramified-oriented*.  B3c (`DyadicOrientation`)
   pins only the χ-coordinate (`χ(A),χ(S),χ(Y) = −1, 1, (−3)⁻¹`); B8 is 2-primary/anabelian;
   neither touches `λ`.  The only axiom clause producing Galois-restriction data is B5's
   `norm_reciprocity` (currently **dead code** — never consumed), which speaks of finite
   **abelian** intermediate fields of `AlgebraicClosure ℚ₂`.

So the derivation must run `norm_reciprocity` against the **concrete unramified 2-tower**
`M_n := ℚ₂(ζ_{2^{2^n}−1})` and connect it to `f₁`.  The connection closes if and only if we can
show the B10 wild subgroup `W` (equivalently, B10 inertia) **acts trivially on odd roots of
unity** — the linear-algebra form: the cyclotomic-tower character `h̄_n : D₀ → ℤ/2^n` is
proportional to `λ`.  This is the crux (P-25e); routes below.

## Sub-tickets

| # | Deliverable | Risk |
|---|---|---|
| **P-25b** | **The reduction** (do first — unconditional value): `tame_reciprocity_of_two_values : (F) → (U₋₃) → tame_reciprocity`.  Machinery: factor `f₁` through `B` (`isProP`, abelian target), transport generators along `markedHom_bijective`/`markedPi`, density via `denseRange_recip`.  Replaces the current sorry by two sharply-scoped sorries `(F)`, `(U₋₃)` in `BoundaryMapsWitness.lean` (or a new `TameCharacter.lean`). | LOW |
| **P-25a** | **Rigidity**: `Ttame_ab ≅ Ẑ` (`τ ∈ derived closure`), `Aut(Ttame)` trivial on the ℤ₂-coordinate (Fermat-factor prime orders; reuse `emN`/`u2`), Hopfian-ness of top.f.g. profinite groups, ⇒ `nuT_tameF_witness_independent`.  Not on the critical path for (F)/(U₋₃) but certifies the statement is well-posed and reusable for P-18. | LOW-MED |
| **P-25c** | **Level-1 pilot**: the concrete unramified quadratic `M₁ = ℚ₂(ζ₃) = ℚ₂(√−3)` as `IntermediateField ℚ₂ (AlgebraicClosure ℚ₂)`: `[M₁:ℚ₂] = 2`, Galois, abelian; `normSubgroup M₁ ⊇ ℤ₂ˣ` via the explicit witness `N(√−15 + 2√−3) = −3` pattern (`a² + 3b² : a = √−15` exists by P-07's `mod8_sq`/`hensel_sq`) plus the unit-parametrized version; feed `norm_reciprocity M₁`.  Output: `(F)`, `(U₋₃)` **mod 2**.  De-risks all of P-25d's technology on the smallest instance. | MED |
| **P-25d** | **The tower**: for all `n`, `M_n = ℚ₂(ζ_{m_n})`, `m_n = 2^{2^n}−1`: degree `= ord_{m_n}(2) = 2^n` (`u2` machinery gives the order; the *field* degree needs unramified/Hensel lifting of `𝔽₂(ζ)`-degrees — likely Mathlib gap: build by hand via `PadicInt` Hensel + cyclotomic polynomial factor degrees), `Gal(M_n/ℚ₂)` cyclic `2^n` (embed via `IsPrimitiveRoot.autToPow`, count), **norm-unit surjectivity** `N(𝒪ˣ) = ℤ₂ˣ` (residue-norm + trace-surjectivity filtration — the big build, ~mini-project), nested compatibility.  Output: `h_n := restrictAb M_n ∘ rec` kills units, sends 2 to a generator, coherently in `n`. | HIGH |
| **P-25e** | **The bridge** (crux): identify the `h`-tower with `f₁`, i.e. `W ≤ G_{M_n}` / `h̄_n ∝ λ`.  Attack routes, in order: (i) **Lemma 3.1 refinement** — in a finite quotient carrying the tame relation, a normal 2-subgroup is central *and unramified* (the repo's `Tame.lean` analysis says "central+unramified"; check whether the unramified clause, applied to the joint image of `G` in `(Ttame-level) × Gal(M_n/ℚ₂)` with `W`-image `= 1 × A_n`, kills `A_n`); (ii) **transfer/Verlagerung** on the index-`2^n` subgroup; (iii) if both stall: the residue is the single clean statement `W_acts_trivially_on_odd_roots` — dramatically smaller than `tame_reciprocity`, abelian-checkable, and the honest minimal-axiom fallback (user decision). | HIGH / possibly blocked |

**Order**: P-25b → P-25c → P-25d ∥ P-25a → P-25e.  P-25b alone already shrinks the trusted
surface to two one-line arithmetic atoms even if P-25e ends in the fallback.

## Sizing

P-25b ~150–250 ln; P-25a ~200–300; P-25c ~250–400; P-25d ~600–1200 (Mathlib-gap risk in
unramified degree theory and norm-unit surjectivity); P-25e unknown (research-grade).  All new
work in own files (`GQ2/TameCharacter.lean`, `GQ2/UnramifiedTower.lean`, …); splices into
`BoundaryMapsWitness.lean` are one-liners.

---

## Refined analysis after P-25b (2026-07-05, Opus) — the blocker is precise

**P-25b DONE** (commit `cef787e`): `tame_reciprocity` is proved modulo two atoms
`tame_recip_uniformizer` (F) and `tame_recip_unitNeg3` (U₋₃).  All reduction machinery
(`padic_hom_eq_of_gens`, `padicInt_eq_zero_of_forall_two_pow_dvd`, `mult_padic_sq_eq_one`,
`tameChar`) is **std-3**.

**A cleaner intrinsic reduction (records the crux for P-25e).**  Because `Ztwo` is pro-2,
`ν_t∘tameF` factors through the maximal pro-2 quotient: `ν_t∘tameF = ψ∘pro2F` for a unique
`ψ : Π → Ztwo` (`proPKernel_le_ker`).  Since `ν₂∘pro2F = ι⁻¹∘ν_ur∘toAb` (proved,
`prop_3_10_local_marked`) and `pro2F` is surjective,

>  `tame_reciprocity  ⟺  ψ = ν₂`   (as homs `Π → Ztwo`).

By `topGen_piBd` this is three generator values:
* `ψ(x₀) = 1`, `ψ(x₁) = 1`: **provable iff `x₀, x₁ ∈ pro2F(W)`** — because `W = ker tameF`
  gives `pro2F(W) ⊆ ker ψ` for free (`ν_t∘tameF` kills `W`), so once `x_i ∈ pro2F(W)` the wild
  atoms vanish with *no* arithmetic.
* `ψ(σ) = ztwoOne`: the Frobenius-orientation value.

So the entire gap is: **`pro2F(W) = ker ν₂`** (equivalently `pro2F(W) = ⟨⟨x₀,x₁⟩⟩`) **and the
`σ`-normalization** — i.e. that B10's abstract wild subgroup `W` maps, under the
`prop_3_10_local_marked` iso `e : G_{ℚ₂}(2) ≅ Π`, onto the wild part of `Π`.

**Why this is irreducible from B10 + B5 as stated.**  `W` is fixed by B10 only up to
*maximality* (`W = O₂(G_{ℚ₂})`, the largest normal closed pro-2 — this much IS forced and
witness-independent).  The iso `e` is fixed by B5 *reciprocity* (via `prop_1_1`/`markedHom`),
independently of `W`.  Nothing tells us `e(W-image) = ⟨⟨x₀,x₁⟩⟩`: that is the statement that the
B10 tame filtration and the B5 reciprocity filtration are the *same* filtration of `G_{ℚ₂}` —
genuine local-CFT input.  The concrete route (P-25c/d/e) must produce it by realizing `ν_t∘tameF`
as `restrictHom` of a concrete unramified tower and invoking `norm_reciprocity`; but
`restrictHom M = ρ_M∘pro2F` (provable, `M/ℚ₂` a 2-extension) only relates `restrictHom` to
`pro2F`, **not** to `tameF` — so it still cannot see `W`.  The `tameF`↔`restrictHom` identification
is exactly `W = concrete wild inertia`, which needs Mathlib's (absent) ramification theory for
`AbsGalQ2 = Field.absoluteGaloisGroup ℚ₂`.

**Status of the sub-tickets after this analysis:**
* P-25c/d (unramified tower + norm surjectivity): buildable but **do not close the gap** on their
  own — they give `restrictHom`/`ρ_M`, never `W`.  Deprioritized unless P-25e cracks.
* P-25e (the bridge `pro2F(W) = ⟨⟨x₀,x₁⟩⟩`): the real obstruction.  Needs either (a) a Mathlib
  development identifying `O₂(Field.absoluteGaloisGroup ℚ₂)` with the fixed group of the maximal
  unramified subextension (large, research-grade), or (b) **a minimal bridging axiom** — now
  dramatically smaller than the original `tame_reciprocity`: e.g. `pro2F(W) = ker ν₂`, a single
  equality of explicit subgroups of `Π`, abelian/finite-checkable and with a clean NSW citation
  (the wild-inertia filtration).  User decision (the "avoid a new axiom" preference collides with
  the absence of Mathlib local ramification theory).

---

## Axiom proposal with verified citations (2026-07-06, Opus; NSW page/theorem numbers checked in `references/Neukirch, Schmidt, Wingberg -- Cohomology of Number Fields.pdf`)

**Shape: an oriented refinement of the B10 bundle** (existential form — no rigidity needed for
its classical justification; census stays a user decision, B10 → B10′ rather than a new leaf):

```lean
/-- B10′ (oriented tame quotient): a B10 tame-quotient datum compatible with B5 reciprocity —
units land in the ν_t-kernel, the uniformizer in the geometric-Frobenius coordinate. -/
structure OrientedTameQuotient extends TameQuotientData where
  nuT_recip_unit : ∀ (u : ℤ_[2]ˣ) (g : AbsGalQ2),
      toAb g = localReciprocity.recip (unitEmbed u) →
      nuT (equiv (QuotientGroup.mk g)) = 1
  nuT_recip_uniformizer : ∀ g : AbsGalQ2,
      toAb g = localReciprocity.recip uniformizer →
      nuT (equiv (QuotientGroup.mk g)) = ztwoOne⁻¹

axiom tameQuotientOriented : OrientedTameQuotient   -- replaces the B10 use-site in P-25
```

Both clauses are ∀-lift-form (well-posed: `ν_t∘equiv∘mk` kills `commClosure`, abelian pro-2
target).  They are exactly the atoms: `locTame := tameQuotientOriented`-based `tameFHom` makes
`tame_recip_unitNeg3` immediate (u = −3) and `tame_recip_uniformizer` a one-line sign
computation (`ι(ztwoOne⁻¹) = ofAdd(−1)`).  Note the clauses are stated against **the B5
constant `GQ2.localReciprocity`**, not ∀-quantified over bundles `R` — see the caveat below.

**Citations (verified in the local NSW copy):**

* **NSW (7.1.2)(i)**, Ch. VII §1 (pp. 372–373): *for `K|k` unramified, the unit group `U_K` is a
  cohomologically trivial `G(K|k)`-module* — in particular `Ĥ⁰ = U_k/N_{K|k}U_K = 0`, i.e.
  **every unit is a norm from every finite unramified extension**.  This is the classical core of
  the units clause (`rec(U)` fixes every unramified extension).
* **NSW (7.2.11)** (p. 385): the reciprocity sequence `0 → k^× → G_k^{ab} → Ẑ/ℤ → 0`, with
  **(7.2.12)**: the characterization `χ((a,k)) = inv(a ∪ δχ)`.
* **NSW, proof of (8.3.13)** (p. 460), verbatim: *“the norm residue symbol `( , k)` maps the
  subgroup `k_𝔭^× ⊆ C_k` onto the decomposition group … and the group of units `U_𝔭 ⊆ k_𝔭^×`
  onto the inertia group”*, citing **Neukirch, Algebraic Number Theory [NSW ref. 160], Chap. V,
  (6.2)** (and Chap. VI (5.6) for the global part).  [160] confirmed in NSW's bibliography:
  *Algebraische Zahlentheorie*, Springer 1992 / English *Algebraic Number Theory* (Grundlehren
  322).  **Neukirch ANT V (6.2)** is the sharpest single reference for “units ↦ inertia, prime
  elements ↦ Frobenius lifts”.
* **NSW (7.5.2)** (p. 410): the tame structure `1 → Ẑ^{(p′)}(1) → G_k^{tr} → Γ → 1`, `Γ = ⟨φ_k⟩`
  the unramified quotient; **(7.5.3) (Iwasawa)** with the relation `στσ⁻¹ = τ^q`, `σ ↦ σ_k` =
  **arithmetic** Frobenius.  Since the repo's `tame_relation` is `σ⁻¹τσ = τ²`, the repo's
  `tameSigma` is NSW's `σ⁻¹` = *geometric* Frobenius — whence the `ztwoOne⁻¹` value at the
  arithmetic `rec(2)` (matching B5's geometric `ν_ur` normalization, `nu_ur_recip`).
* Serre, *Local Fields* [7], Part Four (local CFT) is the natural secondary citation, but the
  local PDF copy is an image-only scan (no text layer) — pinpoint numbers not verifiable here.

**Caveat recorded (and an honesty correction).**  The clauses must NOT be ∀-quantified over
`R : LocalReciprocity`: a “Ẑ-coordinate twist” `ψ_c` (scaling the Frobenius coordinate of a
valid bundle by `c ∈ Ẑˣ`) preserves clauses (b)/(c) and the *unramified* norm kernels, so a
∀-R form would be classically false.  However — correcting the earlier “irreducible” claim —
such a twist does **not** preserve the norm kernels of *mixed ramified* layers (e.g.
`L = ℚ₂(√2)`: `N(Lˣ) ∋ −2` couples valuation and unit coordinates), so `norm_reciprocity`
(∀ L) **does** pin the Frobenius coordinate of `recip` in principle.  A no-new-axiom derivation
is therefore *not* independence-blocked; it remains blocked in practice by the same two builds
(concrete `IntermediateField` layers with computed norm groups; the `W`↔fields bridge).  The
oriented-B10′ axiom stays the honest price of skipping those builds.
