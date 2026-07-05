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
