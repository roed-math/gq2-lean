# P-16d6e4aA-P2: the isotypic-pack derivation design
### (the blueprint for P3 — discharging `zeroCount_qDouble_ramified_of_faithful`)

**Sources**: paper pp. 25–29 (§6.1–6.2: (82)–(91), Lemmas 6.6–6.8, Prop 6.9) re-read
2026-07-08; in-repo `SectionSix.lean` (`lemma_6_8` :240, `prop_6_9_ramified` :368),
`GQ2/GaussZFinalGammaA.lean` (`zeroCount_qDouble_ramified_of_faithful`, the target sorry).

---

## §0. The target and its interface

The ONE remaining sorry of P-16d6e4aA:

```
zeroCount_qDouble_ramified_of_faithful
  {C V} [Group C] [top/disc/Finite C] [AddCommGroup V] [Finite V] [DistribMulAction C V]
  (c : ContinuousMonoidHom Ttame C) (hc : Surjective ⇑c)
  (hfaith : ∀ g, (∀ v, g • v = v) → g = 1)
  (hsimple : ∀ W : AddSubgroup V, stable → W = ⊥ ∨ W = ⊤)
  (hram : c tameTau ≠ 1)
  (q) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
  (m) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2*m)) :
  zeroCount (qDouble q (powOmega2 (c tameSigma) • ·)) = 2^(2m−1) + 2^(m−1)
```

This is LITERALLY `SectionSix.prop_6_9_ramified` minus its pack.  So the deliverable is
the pack, in `prop_6_9_ramified`'s exact field shapes (from `SectionSix.lean:368`):

| field | shape | paper source |
|---|---|---|
| `s r a : ℕ`, `hr : Odd r`, `ha : 1 ≤ a`, `hs1 : 1 ≤ s` | numerology | Lemma 6.8 setup |
| `Wt : Type`, `[AddCommGroup Wt]`, `[DistribMulAction ↥(Subgroup.zpowers (c tameTau)) Wt]` | the simple summand | `W` |
| `hWt2 : ∀ w, w + w = 0`, `hWtsimple : FoxH.IsSimpleModTwo (zpowers (c tameTau)) Wt` | | |
| `hWcard : Nat.card Wt = 2 ^ (2^a * r)` | `#W = 2^f`, `f = 2^a·r` | |
| `e : V ≃+ (Fin s → Wt)`, `he : ∀ (t : zpowers (c tameTau)) v j, e ((t:C) • v) j = t • e v j` | `V\|_I ≅ W^{⊕s}` | isotypicity |
| `hVU : Nat.card {v // powOmega2 (c tameSigma) • v = v} = 2 ^ (r*s)` | `dim V^U = rs` | (88) |
| `hrank : ∀ k, Nat.card (onePlusU …).range = 2^k → (k : ZMod 2) = s` | `rank(1+U) ≡ s` | (88) |

Note the AVAILABLE hypotheses: `hfaith` IS in scope (the A-4.5f actionization already
ran), `hram` is ELEMENT-level (`c tameTau ≠ 1`) — both essential below.  Everything
downstream of the pack (`arf q = s`, Wall doubling (86), the zero count (91)) is
already proved in-repo (`lemma_6_8`, `GaussSigns.*`, `zeroCount_of_arf_zero`).

---

## §1. The paper's derivation, mapped

Write `t := c tameTau`, `T := Subgroup.zpowers t`, `d := orderOf t` (ODD —
`odd_orderOf_tameInertia`, banked), `S := c tameSigma`, `U := powOmega2 S`.

1. **(Lemma 6.8 setup)** `V|_T` is ISOTYPIC: `V ≅ W^{⊕s}` for a single simple
   `𝔽₂[T]`-module `W`, `#W = 2^f`.
2. **(self-duality)** `f` is EVEN, i.e. `f = 2^a·r` with `a ≥ 1`, `r` odd: the
   nonsingular invariant polar form `B` makes `V` self-dual as a `T`-module, so the
   inverse inertia character lies in the Frobenius orbit; nontrivial odd order ⟹ the
   orbit has even length and `ζ⁻¹ = ζ^{2^{f/2}}`.
3. **(Hermitian model, (89)/(90))** `V ≅ D^s` over `D := 𝔽_{2^f}`, `B` and `q` become
   Hermitian-trace forms; per-line zero count `2^{2m'−1} − 2^{m'−1}` ⟹ **(87)
   `Arf q ≡ s (mod 2)`**.  [ALREADY FORMALIZED — this is exactly what in-repo
   `lemma_6_8`/`GaussSigns.arf_eq_s_ramified` prove FROM the pack.  P3 does NOT
   re-derive it.]
4. **((88), the `U`-fixed count)** `ω₂`'s congruences (`e_ω ≡ 1 (mod 2^a)`,
   `≡ 0 (mod r)`) make the weight-translation decompose `ℤ/f` into `r` cycles of
   length `2^a`; the key group-theoretic step: **`U^{2^a}` centralizes inertia and
   `S`, hence is a central 2-element of the faithful image; its fixed space is a
   nonzero submodule; simplicity forces `U^{2^a} = 1`.**  A `U`-fixed vector is then
   determined by one component per cycle: `dim V^U = rs`, and
   `rank(1+U) = fs − rs = rs(2^a −1) ≡ s (mod 2)`.
5. **(Wall doubling, Lemma 6.6 = in-repo)** `Arf(q_U) = Arf(q) + rank(1+U) = s+s = 0`,
   then the standard count (91).  [FORMALIZED ✓]

---

## §2. The recommended Lean route: PID/étale, NOT raw Clifford — and NO Maschke

**The step-1 isotypicity does not need Clifford theory or Maschke complements.**
`T = ⟨t⟩` is cyclic of ODD order `d` on an elementary-2 `V`, so `V` is a module over
`R := 𝔽₂[X]/(X^d − 1)`, and `X^d − 1` is SEPARABLE over `𝔽₂` (`d` odd) — `R` is étale:

```
R ≅ ∏_i 𝔽₂[X]/(P_i)      (P_i the irreducible factors of X^d − 1, pairwise coprime)
```

- The **idempotent decomposition** `V = ⊕_i V_i` (`V_i := (the P_i-component)`) is
  CANONICAL — no complement-choosing, no averaging.  Two implementation options:
  - (i) *Mathlib-module route*: put `Module (ZMod 2) V` on the exponent-2 group
    (`AddCommGroup.zmodModule`-shaped adapter), regard `t` as a linear automorphism
    annihilated by `X^d − 1`, and use the PID/torsion machinery
    (`Submodule.torsionBy`, internal-direct-sum over coprime factors) or directly the
    CRT idempotents `e_i := (X^d−1)/P_i · inverse` acting through `t`.
  - (ii) *elementary route*: define `V_i := AddMonoidHom.range (êᵢ(t))` for the CRT
    idempotent polynomials evaluated at `t` (a ℕ-polynomial in `t` — pure
    `AddMonoidHom` algebra), prove `⊕` by the idempotent identities.  Heavier by hand
    but avoids the module adapter.
- **Each `V_i` is automatically `W_i^{⊕ s_i}`**: `V_i` is a module over the FIELD
  `D_i := 𝔽₂[X]/(P_i)` (the étale factor!), hence a `D_i`-vector space, hence FREE:
  `V_i ≅ D_i^{s_i}`.  The simple summand is `W_i := D_i` with `t` acting as the image
  of `X` — simple because `P_i` is irreducible (any nonzero `T`-submodule is a
  `D_i`-subspace of a line).  **This kills the need for P-16d6e4aA-P1 (Maschke) in
  this lane** — see §8.

### §3. Single isotype: every conjugation-twist is a 2-power (the Frobenius argument)

`C` permutes the `V_i`: for `g ∈ C`, `g·V_i` is the `P_j`-component where the twist
`t ↦ g⁻¹tg = t^k` acts.  **The banked conjugation calculus
(`tau_fixed_eq_zero_of_gen`'s `hconj`, GaussZFinalGammaA)** shows every conjugate of
`t` in `C = ⟨S,t⟩` (generation: `gen_ttame_quotient`) is `t^k` with `k` in the
subgroup of `(ℤ/d)^×` generated by `2` (the `S`-twist is `t ↦ t²` — the tame relation
`S⁻¹tS = t²` — and its inverse is the square root `t^{(d+1)/2}`; `t`-conjugation is
trivial).  The component-permutation induced by `t ↦ t^{2^j}` is the **`𝔽₂`-Frobenius
on roots, which STABILIZES every Frobenius orbit** — i.e. every `V_i` is `C`-stable.
[Concretely: `V_i` is characterized by `P_i(t)·V_i = 0`; if `g⁻¹tg = t^{2^j}` then
`P_i(t^{2^j}) = P_i(t)^{2^j}` (char-2 polynomial Frobenius) kills `V_i`, so
`g·V_i ⊆ V_i`.]  Then `hsimple` forces exactly ONE nonzero component:
`V = V_P ≅ D^s`, `Wt := D`, `f := deg P`, `hs1` from `V ≠ 0`.

`P ≠ X + 1` (i.e. `Wt` nontrivial, `f` well-defined `≥ 1`, and the RAMIFIED
constraint): the `P = X+1`-component is `V^t`; `hram` + `hfaith` give `t ≠ 1`, and if
`V = V^t` then `t` acts trivially ⟹ `t = 1` by `hfaith` — contradiction.  (This is
also exactly `tau_fixed_eq_zero_of_gen`: `V^t = 0`.)

### §4. `f` even (`a ≥ 1`): self-reciprocity from the nonsingular pairing

`B := polar q` is a perfect (nonsingular) `T`-invariant pairing.  Invariance
`B(t·v, t·w) = B(v,w)` pairs the `P`-component perfectly with the `P*`-component
(`P*` := the reciprocal polynomial, root-map `ζ ↦ ζ⁻¹`): for a single isotype this
forces **`P self-reciprocal`**.  A self-reciprocal irreducible over `𝔽₂` other than
`X + 1` has EVEN degree, and moreover the involution is `x* = x^{2^{f/2}}`
(the paper's display): if `ζ⁻¹ = ζ^{2^j}` (some `0 ≤ j < f`) then `j ≠ 0` (else
`ζ² = 1`, odd order ⟹ `ζ = 1` — excluded by §3), and squaring the relation gives
`f | 2j` ⟹ `2j = f`.  Lean shape: work with `orderOf ζ`-free arithmetic — `t` has a
root of `P` in `D` itself (`X mod P`); state as: the multiplicative order `n` of
`x := X mod P` in `D^×` satisfies `x⁻¹ = x^{2^{f/2}}`… or avoid elements entirely and
argue with `P` and the reversal operation on polynomials.  Either way this is
finite-field bookkeeping with `orderOf`/`Polynomial` API — self-contained.
Then `a := (f).factorization 2 ≥ 1`, `r := f / 2^a` odd — pure `Nat` arithmetic.

### §5. The `U`-fixed count `#V^U = 2^{rs}` — two routes

**Common first step (elementary, banked-adjacent): `U^{2^a} = 1`.**
`U := powOmega2 S` has 2-power order (`orderOf_powOmega2_dvd_two_pow` ✓).  Show
`U^{2^a}` centralizes `t`: with `ω := omega2Exp (orderOf S)` one has
`U⁻¹ t U = t^{2^ω}` (iterate `S⁻¹tS = t²`), so the `U^{2^a}`-twist exponent is
`2^{ω·2^a} (mod d)`, and triviality needs `f ∣ ω·2^a` (`f = ord_d(2)`, the degree).
**Congruence transport**: the conjugation action of `S` on `⟨t⟩` has order exactly
`f`, so `f ∣ orderOf S`; hence `r = oddPart f ∣ oddPart (orderOf S) ∣ ω` (the
banked "omega2Exp ≡ 0 mod odd part") — giving `f = 2^a·r ∣ ω·2^a` ✓.  [The `≡ 1
(mod 2^a)`-side of `e_ω` is NOT needed for centralization, only for the descent
twist-order in Route A: there use `ω ≡ 1 (mod 2^A)` (`2^A` = the 2-part of
`orderOf S`, `a ≤ A`) — verify the exact banked form of this congruence in
FoxH/AppendixB at P3-start; it is the lemma making `powOmega2` the 2-Sylow
component.]  Then `U^{2^a}`
commutes with `t` AND with `S` (power of `S`), i.e. with generators
(`gen_ttame_quotient`) ⟹ CENTRAL in `C`; its fixed space is a `C`-submodule
(centrality!), NONZERO (a 2-element on a finite 2-group fixes ≥ 2 points —
`card_modEq_card_fixedPoints`, the A-4.5c device verbatim) ⟹ `⊤` by `hsimple` ⟹
**`U^{2^a}` acts trivially ⟹ `= 1` by `hfaith`**.  [This is the ONE place `hfaith`
is needed — and it IS available at the faithful level. ✓]

**Route A (recommended): Galois descent / additive Hilbert 90.**  `U` normalizes the
`D`-structure semilinearly: `U (x·v) = φ(x)·U(v)` where `φ := Frob^{e_ω}` on `D`
(from `U⁻¹tU = t^{2^{e_ω}}`).  The twist `φ` has order `2^a` on `D` (`e_ω ≡ 0 (mod r)`,
`≡ 1 (mod 2^a)` ⟹ `gcd(e_ω, f) = r`), with fixed field `F := 𝔽_{2^r}`.  A semilinear
automorphism of `D^s` of order exactly the twist-order descends: `V^U` is an
`F`-form, `#V^U = (#F)^s = 2^{rs}`.  The descent input is finite-field cyclic descent
(additive Hilbert 90 — surjectivity of the `φ`-twisted trace; Mathlib has trace-form
surjectivity for finite fields).  ~100–150 lines with Mathlib's `FiniteField` API.

**Route B (paper-literal): weight cycles.**  Decompose over `𝔽̄₂`-weights and count
`r` cycles of length `2^a` each contributing `s`.  Requires base-change machinery —
HEAVIER in Lean; prefer Route A.

**Route C (worth 30 minutes before committing to A): pure counting.**  `V^U` is a
`D^{φ}`-subspace…; try to get `#V^U = 2^{rs}` from `U^{2^a} = 1` + the semilinearity
alone by an orbit/rank count over `F`.  If a slick elementary count exists it beats
both.  (Do NOT expect `#V^U` to be computable without the semilinear structure — the
2-power-order of `U` alone only gives `#V^U ≥ 2^{fs/2^a}`-type bounds, not equality.)

### §6. `hrank` from `hVU` — free

For the additive endo `N := 1 + U` (in-repo `onePlusU`): `#range N · #ker N = #V`
(first isomorphism theorem, `Nat.card`-form) and `ker N = V^U` (char 2!):
`2^k · 2^{rs} = 2^{fs}` ⟹ `k = (f−r)s = rs(2^a −1) ≡ s (mod 2)` since `r`, `2^a −1`
odd.  Pure arithmetic given `hVU` + `hcard` (note `fs = 2m`: from
`#V = (2^f)^s = 2^{2m}`).

### §7. Assembly checklist (inside `zeroCount_qDouble_ramified_of_faithful`)

1. `t ≠ 1` from `hram`; `d := orderOf t` odd (`odd_orderOf_tameInertia`); `V^t = 0`
   (`tau_fixed_eq_zero_of_gen` at `hgen := gen_ttame_quotient`,
   `hrel := c`-image of `tame_relation`, `hmoved` from `hram` + `hfaith`… note: need
   `∃ v, t•v ≠ v` — from `hram : t ≠ 1` + `hfaith` contrapositive ✓).
2. §2–§3: the étale decomposition + single isotype ⟹ `(Wt, s, e, he, hWtsimple,
   hWt2, #Wt = 2^f, hs1)`.
3. §4 ⟹ `a ≥ 1`, `r` odd, `hWcard`-shape.
4. §5 ⟹ `hVU`; §6 ⟹ `hrank`.
5. `exact SectionSix.prop_6_9_ramified c hc hfaith hsimple hram q hq hns hinv hV₂ s r
   a hr ha hs1 Wt hWt2 hWtsimple hWcard e he hVU hrank m hm hcard` — where
   `hV₂ := DeepPart.exp_two_of_simple_of_card`-shape (or derive from `hcard` +
   simplicity as in-repo).  DONE — the sorry falls, and with it the last sorryAx of
   `gaussZResidue_gammaA_ramified`.

### §8. Feasibility verdict and consequences

- **Pack route: FEASIBLE**, via §2's étale/PID route.  Estimated 600–1000 lines over
  2–4 sessions: the module-adapter + decomposition (§2–3, ~250–400 ln), the
  self-reciprocity (§4, ~100–150 ln), the descent count (§5A, ~150–250 ln, the
  riskiest part — do Route C's 30-minute check first), the glue (§6–7, ~100 ln).
- **Pack-free `arf(qDouble) = 0` route: REFUTED.**  `V = 𝔽₂²`, `q(x,y) = xy`,
  `U = swap` is an isometry of 2-power order with `arf(q_U) = 1` — the ramified
  structure is essential.  Do not pursue.
- **P-16d6e4aA-P1 (Maschke) is NOT needed for this lane** (§2: isotypic components
  are vector spaces over the étale field factors — freeness is automatic).  P1 can be
  dropped, or kept only as a fallback if the étale route hits an unexpected wall.
- The two hypotheses that make everything work at the target: `hfaith` (for
  `U^{2^a} = 1`, §5) and element-level `hram` — both present BECAUSE the A-4.5f
  actionization already moved the statement to the faithful quotient.  Do not weaken
  them.

### §9. Mathlib entry points to verify at P3-start (30-minute recon)

- `AddCommGroup.zmodModule` (or the current name) — exponent-`n` group ⟹
  `Module (ZMod n)`;
- `Polynomial` CRT/coprime factorization over `𝔽₂`; separability of `X^d − 1` for
  odd `d` (`Polynomial.separable_X_pow_sub_C`-adjacent, char-2 form);
- torsion decomposition: `Submodule.torsionBy` internal-⊕ over coprime ideals (PID),
  or hand-rolled CRT idempotents;
- `AdjoinRoot P` field instance for irreducible `P`; `Module.Free` over a field +
  `Nat.card`-of-free (`#(D^s) = #D^s`);
- finite-field API: `orderOf` in `Dˣ`, Frobenius `frobenius (ZMod 2)`-powers,
  trace surjectivity (`Algebra.trace_surjective`-shape) for §5A;
- `onePlusU` (in-repo, GaussSigns) + `AddMonoidHom` first-iso `Nat.card`-count (§6).
