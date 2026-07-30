# NC1 — the corrected noncompact-N cross-operator theorem: design memo + spike

**Ticket NC1** (dyadic campaign, R3(a) commission; board [`tickets.md`](tickets.md)). Written on
branch `dyadic-nc1` (worktree `~/claude/gq2-dyadic-lg`, at the `dyadic` head `337647f`). Every
Lean anchor below was opened and read in this checkout; Python anchors are from
`~/claude/general_2adic` (the simplification campaign's repo, read-only).

**Commission.** The simplification campaign machine-refuted the draft's eq:Ncross (S3.2,
`general_2adic/BOARD.md:581`; errata item 5, [`packet-errata-draft.md`](packet-errata-draft.md)):
for the corrected noncompact-N word the universal second jet on ramified simples carries

```
Q(c₀, c₁) = Q₀(c₀) + b_q(c₁, L_c c₀),
L_c = A⁻¹ + B + B·A⁻¹ = 1 + (1 + A⁻¹)(1 + B),   M_c = adj(L_c),
A = S^{η̂},  B = S^{2^r}
```

— NOT the draft's `L_c = A⁻¹`. The owner chose R3 option (a): prove the corrected identity in
Lean (symbolic in `r ≥ 1`, `η ∈ ℤ₂ˣ`, on ramified simples), replacing the twisted-path
diagnostic status. This memo designs that theorem: statement, proof route, missing machinery,
ticket plan, feasibility spike, timing.

*(Sections are committed incrementally; this header commit fixes scope.)*

---

## 0. Headline verdicts

| # | Question | Verdict |
|---|---|---|
| V1 | Does the corrected formula state cleanly in existing vocabulary? | **Yes — every piece elaborates from merged code** (spike §5). Word = `PWord (Generator n)` over F2's syntax with `deltaW`/`etaHatZ`; evaluation = F2's `Marking.eval` into `CentExt (kappa0Cocycle dat hdat)` over `Sd C V` (the ℚ₂ κ⁰-extension layer, `GQ2/GaussZ/RelatorGammaA.lean`); form data = `QuadraticFp2.polar` + `FactorSet`/`IsEquivariantFactorSet` (`GQ2/OrbitData.lean:43/:54`). No new type is needed. |
| V2 | Proof difficulty | **Mechanical, and cheaper than the twisted-engine framing suggests.** At the Gate-E marking (wild letters trivial-lower, `N.py:891`) the whole computation collapses into the Heisenberg slice `{((v,1),z)}` of the κ⁰-extension. §3 works the evaluation block-by-block by hand: `E_{r,η}` evaluates to the **central** element `((0,1), b_q(L_c c₀, c₁))` with `L_c c₀` literally the sum of the three inverse-conjugators of the D-block — the corrected operator `A⁻¹+B+BA⁻¹` falls out of `conjR`'s `g⁻¹·(−)·g` convention in three lines. One block is genuinely nontrivial (the `(x₀τ)^{ω₂}`-power inside `δ₀`, §3.3). |
| V3 | Hypothesis bundle | **Strictly weaker than "ramified simple"** — the identity needs only: char 2 (`hV2`), the factor-set laws (`hdat`), `Odd (orderOf u)` (rule 1's hypothesis), and `V^u = 0` (rule 2's). Simplicity, faithfulness, nonsingularity, invariance of `q` (derivable from `hdat` in char 2), the tame relation `sus⁻¹ = u^q`, and `η` a unit are **not needed for the identity**. Each reduction rule's hypothesis is stated, per the engine-side caveat; a companion lemma recovers `V^u = 0` from simple + ramified + `⟨u⟩`-normality for the WNP instantiation (§2.4). |
| V4 | `padicOmega2` additivity (the G1 flag) | **Not needed.** The draft's sum exponent `η̂−2^r` has no `etaHatZ` spelling (its odd components are `1−2^r ≠ 1`); the AST — and the Lean word — use the product conjugator `σ^{η̂}·σ^{−2^r}`, and element-level additivity is the existing `zpowHat_mul` (already used inside `zpowHat_etaHatZ`, `Syntax.lean:229-231`). Commuting lemmas for powers of one base are one-liners via `zpowHat_mul` + commutativity of `ℤ̂`. |
| V5 | Missing machinery | Exactly one small new layer: the **per-element `ω₂`-power bridge** in the extension (`powOmega2 y = y^m` for `ord y ∣ 2m`, `m` odd, §3.3) + the elementary **norm-vanishing** lemma (`V^u = 0` ⇒ `Σ_{i<m} uⁱ• = 0`). Both build on congruence lemmas already in the repo (`omega2Exp_modEq_one`, `oddPart_dvd_omega2Exp`, used at `Syntax.lean:122/:133`). Everything else is assembly. |
| V6 | Proof-grade upgrade | The Lean route is **exact where the Python is diagnostic**: it computes the honest finite evaluation (the atom-level identity), not S1.T's twisted symbolic value, so the "nonvanishing is only diagnostic" caveat and the S1.5 completeness caveat both dissolve. The S1.4/S1.T lift-level-4 constant is also sidestepped — profinite exponents reduce per-element at `orderOf` in the finite extension, no global level. |
| V7 | Timing | **Prove now.** The theorem depends only on F2 + the merged ℚ₂ κ⁰ layer — G-1/WW-lane are *not* prerequisites, and nothing here duplicates WW3 (Stokes chain map, clause (4)) or WW4 (certificate packaging). It is WNP-c's centerpiece (the "claimed cross operators" half of packet row WC-Npc) pulled forward; WNP-b/c later consume the theorem instead of re-proving it. One coordination point: the word tree should land where WNP-a expects it (§6). |
| V8 | Statement fidelity vs the machine | The designed statement was cross-checked term-by-term against `N.py`: `L_c` = the machine's `A⁻¹+B+BA⁻¹` (`cross_operators`, :2990), `Q₀` = `PLUS_FORM_TEXT_NONCOMPACT`'s `β_A(a, A⁻¹a) + c_{A⁻¹}(a)` (:2536) = `dat.f c₀ (â⁻¹•c₀) + dat.m â⁻¹ c₀`, and the `q(c₀)`-cancellation that makes `Q₀` free of a diagonal `q`-term is exactly the α ≥ 2 condition (`LabuteType.Valid (.N α)`, `Parameters.lean:170`). Handles contribute the standard `Σ b_q` hyperbolic tail. |

---

## 1. The commissioned mathematics, pinned to sources

### 1.1 The word (draft eq:Npc-word; `N.py:2136` `noncompact_n`)

```
g = x₁σ^{2^r}
R_{N,α,r,η} = x₀^{p_α} [x₀, σ^{η̂}] · x₂^{-g} (x₂τ)^{ω₂} · E_{r,η} · H_h ,   p_α = 2+2^α
D_{r,η} = δ₀^{σ^{η̂}} δ₀^{σ^{−2^r}} δ₀^{σ^{η̂−2^r}}      (expanded)
        = δ₀^A (δ₀ δ₀^A)^{B⁻¹}                          (compressed, §8.3; A = σ^{η̂}, B = σ^{2^r})
E_{r,η} = [D_{r,η}, x₁],    δ₀ = (x₀τ)^{ω₂} x₀⁻¹
```

`η̂ ∈ ℤ̂ˣ` has 2-component `η` and odd components 1. Two AST decisions the Lean word must
mirror (both already made by F2):

* **`x^{-g}` is sugar** (`PWord.invConj`, `Syntax.lean:477`; packet Rem. 2.3).
* **The sum exponent `η̂−2^r` does not exist as a node**: the third conjugator is the *product*
  `A·B⁻¹` of two σ-powers (`N.py:2103-2111`, "no such node exists … the AST therefore conjugates
  by the product"). Lean-side the same product spelling is forced and sufficient (V4).

### 1.2 The refuted display and the corrected operators

Draft eq:Ncross claims `M_c = A, L_c = A⁻¹` (`ETA_CROSS_DRAFT`, `N.py:2543`). S3.2
machine-refuted it (`CROSS_OPERATOR_FINDING`, `N.py:2549`; BOARD.md:581; R3 row :476; errata
item 5): reducing the universal twisted class-two value of eq:Npc-word by the three
`RAMIFIED_REDUCTION_RULES` (`N.py:3090`) gives

```
L_c = A⁻¹ + B + B·A⁻¹ = 1 + (1 + A⁻¹)(1 + B),    M_c = adj(L_c) = A + B⁻¹ + A·B⁻¹,
Q(c₀, c₁) = Q₀(c₀) + b_q(c₁, L_c c₀),
Q₀(c₀) = β_A(a_{x₀}, A⁻¹ a_{x₀}) [+ c_{A⁻¹}(a_{x₀}) on a twisted lift]      (N.py:2536)
```

symbolically in `(r, η)` (`SigmaOperator`, `N.py:2877`: operators are `F₂`-sums of
`σ^{a·2^r + b·η̂}`), validated at the six instances `NONCOMPACT_INSTANCES` (`N.py:2458`) on both
twisted ramified simples. The discrepancy `B(1+A⁻¹)` vanishes iff `A = 1`. The draft's
*conclusion* (`L_c` invertible ⇒ the `c₀–c₁` pairing restored) survives.

### 1.3 The three reduction rules and their hypotheses (`N.py:3090-3117`)

| rule | Python statement | hypothesis it needs | Lean form (§3) |
|---|---|---|---|
| `tame-omega2-power` | an operator factor `τ^{ω₂[v]}` is the identity | `ord(τ-image)` odd | `powOmega2`-of-odd = 1 (T1; `zpowHat_padicOmega2_eq_one_of_odd` shape, `Syntax.lean:208`) |
| `tame-geom-vanishes` | `geom(τ^{±1}; ω₂[v])` is zero on a ramified module | `V^T = 0`, `ord(τ)` odd | norm-vanishing: `im(N_u) ⊆ V^u = 0` — elementary, **no semisimplicity needed** (§3.3) |
| `diagonal-q-invariance` | `β_A(Pa, Pa) = β_A(a,a)` | invariance of `q` only | derivable from `IsEquivariantFactorSet` in char 2 (`m_quad` at `w = v`, `m_zero` at `RelatorGammaA.lean:113`) |

The engine applies these to 78 twisted atoms and gets 8; `report.complete` guards against
silent loss (`reduce_ramified_simple`, `N.py:3206`). The Lean proof does **not** replay this
atom algebra: it computes the honest evaluation, on which the three rules appear as the three
lemma families in the right column (§3). That is exactly the "atom-level identity, not a
post-collapse shadow" requirement — the S1.5 normalizer and its completeness caveat never enter.

### 1.4 What the packet requires

* Def. 9.1 (word certificate, `refs/…-proof.tex:833`) items (3)–(6): the Fox, **Stokes**,
  scalar, and **quadratic/Hessian** certificates. NC1's theorem is the mathematical core of
  item (6) for the Npc row (the claimed quadratic shape on the relevant modules), and is the
  deliverable packet row **WC-Npc** (:1089) names: "Replay the correction `E_{r,η}`
  symbolically and prove the claimed cross operators for all allowed `r, η`" — with "claimed"
  now meaning the S3.2-corrected operators (errata item 5).
* Prop. 10.2 (boundary, :855; noncompact clause :882-883): `x₂^{-g}x₂ = [g,x₂]`, correction
  `= 1` under pro-2; tame side dies. Boundary is WNP-a's business, **not** NC1's; the NC1
  theorem is jet-level and holds at a marking where the boundary block evaluates to 1 exactly.
* The packet overrides drafts; eq:Ncross is draft display, and the packet's WC-Npc row asks
  for "the claimed cross operators" without displaying values — so proving the corrected `L_c`
  *satisfies* the packet as written while correcting the draft (errata item 5 already drafted).

---

## 2. The Lean statement

### 2.1 Ambient objects (all existing)

* **Carrier**: `C V : Type` (universe 0, the ℚ₂ pattern), `[Group C] [AddCommGroup V]
  [DistribMulAction C V]`, both finite with discrete topology. `Sd C V` = the semidirect
  product carrier with `Group`/`Finite`/`DiscreteTopology` instances
  (`GQ2/GaussZ/RelatorGammaA.lean:51-100`).
* **Extension**: `dat : FactorSet C V`, `hdat : IsEquivariantFactorSet q dat`
  (`GQ2/OrbitData.lean:43/:54`); `kappa0Cocycle dat hdat : TwoCocycle (Sd C V)`
  (`RelatorGammaA.lean:123`); the evaluation group is
  `E := CentExt (kappa0Cocycle dat hdat)` with `Group`/`TopologicalSpace ⊥`/
  `DiscreteTopology`/`Finite` instances (`GQ2/WordCoh2.lean:69/:84/:143-145`). `CentExt.fib`
  (:79) is the central coordinate.
* **Word**: `PWord (Generator n)` (`Syntax.lean:450`) with `deltaW 0` (:580), `etaHatZ η`
  (:222), `PWord.invConj` (:477); evaluation `Marking.eval : Marking n E → PWord (Generator n) → E`
  (`Eval.lean:610`, via `PWord.eval` :304 — the typeclass obligations
  `IsTopologicalGroup/CompactSpace/TotallyDisconnectedSpace` synthesize from finite + discrete,
  as the F2 finite section itself demonstrates at `Eval.lean:399-405`).
* **Form data**: `QuadraticFp2.polar` (`GQ2/QuadraticFp2.lean:53`); the polar identity
  `dat.f v w + dat.f w v = polar q v w` is the `f_polar` field.

### 2.2 New definitions (statement-level, small)

```lean
-- the noncompact word, h = 0 core (general h appends the handle block, §2.5)
noncomputable def npcDBlock (η : ℤ_[2]) (r : ℕ) : PWord (Generator 2) :=
  .mul (.conj (deltaW 0) ((PWord.gen .sigma).etaPow η))
    (.conj (.mul (deltaW 0) (.conj (deltaW 0) ((PWord.gen .sigma).etaPow η)))
      (.zpow (.gen .sigma) (-(2 ^ r : ℤ))))          -- compressed spelling, N.py:2095

noncomputable def npcEBlock (η : ℤ_[2]) (r : ℕ) : PWord (Generator 2) :=
  .comm (npcDBlock η r) (.gen (.wild 1))

noncomputable def npcWord (α r : ℕ) (η : ℤ_[2]) : PWord (Generator 2) :=
  .mul (.zpow (.gen (.wild 0)) ((2 : ℤ) + 2 ^ α))
    (.mul (.comm (.gen (.wild 0)) ((PWord.gen .sigma).etaPow η))
      (.mul (PWord.invConj (.gen (.wild 2))
              (.mul (.gen (.wild 1)) (.zpow (.gen .sigma) ((2 : ℤ) ^ r))))
        (.mul (PWord.omega2Pow (.mul (.gen (.wild 2)) (.gen .tau)))
          (npcEBlock η r))))
```

```lean
-- the corrected cross operator, as the module action (SigmaOperator specialized;
-- A-element â := s ^ᶻ etaHatZ η, B-element b := s ^ (2^r))
noncomputable def lcOp (s : C) (η : ℤ_[2]) (r : ℕ) (v : V) : V :=
  (s ^ᶻ etaHatZ η)⁻¹ • v + s ^ (2 ^ r) • v + (s ^ (2 ^ r) * (s ^ᶻ etaHatZ η)⁻¹) • v

-- the diagonal part: β_A(c₀, A⁻¹c₀) + c_{A⁻¹}(c₀), in factor-set vocabulary
noncomputable def npcQ0 (dat : FactorSet C V) (s : C) (η : ℤ_[2]) (c₀ : V) : ZMod 2 :=
  dat.f c₀ ((s ^ᶻ etaHatZ η)⁻¹ • c₀) + dat.m ((s ^ᶻ etaHatZ η)⁻¹) c₀

-- the Gate-E marking: σ ↦ s, τ ↦ u free; wild letters trivial-lower (N.py:891),
-- offsets c₀, c₁ on x₀, x₁, none on the boundary letter x₂ (primal_names, N.py:270)
noncomputable def npcMarking (s u : C) (c₀ c₁ : V) :
    Marking 2 (CentExt (kappa0Cocycle dat hdat)) :=
  Marking.ofLetters ((Sd.mk 0 s, 0)) ((Sd.mk 0 u, 0))
    ![((Sd.mk c₀ 1, 0)), ((Sd.mk c₁ 1, 0)), ((Sd.mk 0 1, 0))]
```

### 2.3 The theorem (h = 0 headline)

```lean
/-- **The corrected noncompact-N cross-operator identity** (S3.2 finding, R3(a) commission;
replaces draft eq:Ncross): on any 𝔽₂-module of a finite group in which the τ-image has odd
order and no nonzero fixed vector, the second jet of `R_{N,α,r,η}` at the Gate-E marking is
`Q₀(c₀) + b_q(c₁, L_c c₀)` with `L_c = A⁻¹ + B + B·A⁻¹` — symbolically in r and η. -/
theorem npc_cross_operators
    {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
    [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace V] [DiscreteTopology V]
    {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) :
    ((npcMarking dat hdat s u c₀ c₁).eval (npcWord α r η)).fib
      = npcQ0 dat s η c₀ + polar q c₁ (lcOp s η r c₀) := …
```

Elaboration of this exact statement is the spike (§5).

### 2.4 Quantification design, spelled out

* **`r` and `η`**: plain `(r : ℕ) (η : ℤ_[2])` — `B` enters as the integer power `s ^ 2^r`
  and `A` as `s ^ᶻ etaHatZ η` (F2's η̂-vehicle). The identity is proved for **all** `r` and
  **all** `η`: neither `1 ≤ r` nor `IsUnit η` is consumed by the computation (§3), so the
  theorem is stated without them, and the draft-validity side conditions (`r ≥ 1`, `η ∈ ℤ₂ˣ`)
  remain where they belong — on the *word row*, not the jet identity. (`hα : 2 ≤ α` **is**
  consumed — the `q(c₀)`-cancellation in §3.4 — and is exactly `LabuteType.Valid (.N α)`.)
  This is strictly stronger than the commissioned "for all `r ≥ 1`, `η ∈ ℤ₂ˣ`". Note `η` here
  quantifies over the η̂-*value*, which subsumes the Python's pinned-`EtaHat`-instances
  limitation (`check_eta`, `N.py:2008`: "eta cannot be symbolic" engine-side — Lean-side it
  can, and is).
* **The ramified-simple hypothesis bundle**: the identity itself needs only
  `(hV2, hdat, hu, hVu)` (V3). The packet-facing phrasing "on every ramified simple" is
  recovered by a companion lemma
  `hVu_of_simple : (∀ W : AddSubgroup V, (∀ h : C, ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤) →
  (∃ v, u • v ≠ v) → (∀ g, g * u * g⁻¹ ∈ Subgroup.zpowers u ∨ …) → …` — concretely: if
  `⟨u⟩ ◁ C` (which the oriented tame relation `s u s⁻¹ = u^{q_K}` supplies for `C = ⟨s,u⟩`)
  then `V^u` is a `C`-submodule, and simple + ramified forces it to `⊥`. This mirrors
  `DetRamified.prop_6_18_ramified`'s bundle (`GQ2/DetRamified.lean:57-64`:
  `hsimple`/`hram`/`hinv`/`hfaith`), which is the repo's canonical "ramified simple" spelling.
* **Which `L_c`**: `lcOp` is the *left-slot* operator of the symmetric pairing — the
  machine's `L_c` from the `(x₀,x₁)` and `(x₁,x₀)` atoms jointly (`extracted_cross_operators`,
  `N.py:3303`, `symmetric` check). `polar` is symmetric, so `polar q c₁ (lcOp … c₀)` *is*
  `b_q(c₁, L_c c₀)`; the adjoint `M_c` needs no separate Lean object (it is the same datum
  read in the other slot — record this in the docstring rather than as a second def).
* **The boundary letter**: `x₂` carries lower value 1 and offset 0 (`primal_names`,
  `N.py:270-281` — "x₂ is deliberately absent"); giving it an offset computes the
  three-variable diagnostic form, which is *not* the commissioned identity.

### 2.5 General h (the handle tail)

State over `Generator n` with `n = 2 + 2h`, handle letters `x_{3+2j}, x_{4+2j}` carrying
offsets `e : Fin (2h) → V`, and conclusion
`… = npcQ0 … + polar q c₁ (lcOp …) + ∑ j : Fin h, polar q (e ⟨2j⟩) (e ⟨2j+1⟩)` (the
`plus_form_noncompact` tail, `N.py:3429`). The handle block is `handlesProd`-shaped
(`Blocks.lean:209`) and its jet is an induction on `h` independent of the core — ticket NC5
(§4), so the h = 0 headline is not blocked on it.

---

## 3. The proof route, block by block

Throughout: `E = CentExt (kappa0Cocycle dat hdat)`, elements written `((v, c), z)`
(`v ∈ V`, `c ∈ C`, `z ∈ 𝔽₂`); multiplication
`((v,c),z)·((w,d),z') = ((v + c•w, cd), z + z' + f(v, c•w) + m_c(w))` (`Sd.mul_v/mul_cc`,
`RelatorGammaA.lean:89-90`; `CentExt.mul_fib`, `WordCoh2.lean:112`; `kappa0Cocycle_κ`, :149).
All facts below were verified by hand against these definitional rewrites; each is a
`simp`/`rw` computation over the listed simp set.

### 3.0 The three structural sub-lemmas (new, small)

* **(a) The κ-free `C`-line**: `c ↦ ((0,c),0)` is an injective hom `C →* E`
  (κ vanishes: `f_zero_left` + `m_zero`), so σ/τ-words evaluate with fiber 0 and
  `orderOf ((0,u),0) = orderOf u`.
* **(b) The Heisenberg slice**: on `{((v,1),z)}` the product law is
  `((v,1),z)·((w,1),z') = ((v+w,1), z+z'+f(v,w))` and inversion is
  `((v,1),z)⁻¹ = ((v,1), z + q v)` (char 2; `f_diag`). Two consequences used repeatedly:
  - **commutator**: `[((d,1),ζ), ((w,1),ξ)] = ((0,1), polar q d w)` — fibers `ζ, ξ` cancel,
    `f(d,w)+f(w,d) = polar` by `f_polar`. *(This single lemma is the entire cross-term
    mechanism.)*
  - **conjugation by the C-line**: `((v,1),z)^{((0,g),0)} = ((g⁻¹•v, 1), z + m_{g⁻¹}(v))` —
    right conjugation `conjR` applies `g⁻¹`, which is where the *inverse* operators of `L_c`
    come from.
* **(c) The `ω₂`-power bridge** (the one nontrivial lemma): for `y : E` with
  `orderOf y ∣ 2*m`, `m` odd: `y ^ᶻ omega2 = y ^ m`. Proof: `zpowHat_omega2` reduces to
  `y ^ omega2Exp (orderOf y)`; `omega2Exp (orderOf y) ≡ m [MOD orderOf y]` by CRT — `≡ 1 ≡ m`
  on the 2-part (`≤ 2`; `omega2Exp_modEq_one`) and `≡ 0 ≡ m` on the odd part (which divides
  `m`; `oddPart_dvd_omega2Exp`) — the exact congruence toolkit `padicOmega2Exp_modEq` already
  exercises (`Syntax.lean:113-143`). Special case `m = orderOf u` odd, `y = ((0,u),0)`:
  `y ^ᶻ omega2 = y^m = 1` (rule 1 / T1).
* **(d) Norm vanishing** (rule 2): if `∀ v, u • v = v → v = 0` and `u^m = 1` then
  `∑ i ∈ Finset.range m, u^i • v = 0` for all `v` — because `u • (∑ uⁱ•v) = ∑ uⁱ•v` (reindex
  by `u^m = 1`), so the sum is `u`-fixed, hence 0. **No semisimplicity, no projector theory.**

### 3.1 δ₀ (the only block that uses (c) at a mixed element)

`y := eval(x₀τ) = ((c₀, u), 0)`. Powers: `y^k = ((N_k c₀, u^k), z_k)` with
`N_k = ∑_{i<k} uⁱ•` and `z_k = ∑_{j<k} [f(N_j c₀, uʲ•c₀) + m_{uʲ}(c₀)]` (finite induction).
At `k = m := orderOf u`: `N_m = 0` by (d), so `y^m = ((0,1), z_m)`, hence `y^{2m} = 1` and
`orderOf y ∣ 2m`; by (c), `(x₀τ)^{ω₂}` evaluates to `y^m = ((0,1), z_m)`. Then

```
δ₀  evaluates to  ((c₀, 1), γ₀(c₀)),     γ₀(c₀) := z_m(c₀) + q c₀
```

(the `x₀⁻¹`-factor contributes `q c₀` via (b)-inversion). δ₀ is trivial-lower ✓ (the
"commutator of trivial-lower letters" fact, `N.py:2608-2617`), with V-part `c₀` and a
quadratic fiber charge that the E-block will cancel.

### 3.2 The D-block and the corrected operator

Conjugators evaluate on the κ-free C-line (a): `â := s ^ᶻ etaHatZ η`, `b := s ^ 2^r`,
third conjugator `â·b⁻¹` (product spelling). By (b)-conjugation, in the compressed spelling:

```
δ₀ δ₀^{â}                    = (((1+A⁻¹)c₀, 1), …)
D = δ₀^{â} · (δ₀ δ₀^{â})^{b⁻¹} = ((A⁻¹c₀ + B(1+A⁻¹)c₀, 1), ζ_D(c₀))
                              = (( (A⁻¹ + B + BA⁻¹)•c₀, 1), ζ_D(c₀))
```

— **the corrected `L_c` is literally the sum of the three inverse-conjugators**
(`conjR x g = g⁻¹xg` applies `g⁻¹`; conjugators `â, b⁻¹, âb⁻¹` give operators
`A⁻¹, B, BA⁻¹`). The draft's `L_c = A⁻¹` is transparently the first term alone — the
refutation is visible in the Lean computation's shape. `ζ_D` (three γ₀'s + m-corrections +
one f-cross-term) never needs to be computed: see 3.3.

### 3.3 The E-block: pure cross term

`x₁` evaluates to `((c₁,1),0)`. By the (b)-commutator lemma:

```
E_{r,η} = [D, x₁]  evaluates to  ((0,1), polar q (L_c c₀) c₁)
```

— central, V-part zero, fiber exactly `b_q(c₁, L_c c₀)`, **independent of `ζ_D`** (the
commutator cancels both arguments' fibers). This is why the correction contributes exactly
the missing pairing and nothing else — the Lean proof exhibits the mechanism, not just the
answer.

### 3.4 The front block and Q₀

* `x₀^{p_α}`: `((c₀,1),0)^2 = ((0,1), q c₀)`, so `x₀^{2+2^α} = ((0,1), (1+2^{α-1})·q c₀)`
  `= ((0,1), q c₀)` for `α ≥ 2` (`1+2^{α-1}` odd — **the hα consumption**; at α = 1 the
  identity fails as stated, matching S3.1's α ≥ 2 Hessian finding).
* `[x₀, σ^{η̂}]`: direct (a)+(b) computation gives
  `(((1+A⁻¹)c₀, 1), q c₀ + f(c₀, A⁻¹c₀) + m_{â⁻¹}(c₀))`.
* Product: the two `q c₀`'s cancel (char 2), leaving fiber
  `npcQ0 = f(c₀, A⁻¹c₀) + m_{â⁻¹}(c₀)` — the `PLUS_FORM_TEXT_NONCOMPACT` display
  `β_A(a, A⁻¹a) + c_{A⁻¹}(a)` verbatim, with the twisted-lift term `c_{A⁻¹}` landing as the
  factor-set correction `dat.m`.

### 3.5 The boundary block dies exactly

`x₂ ↦ ((0,1),0) = 1`, so `x₂^{-g} = 1` (whatever `g` evaluates to), and
`(x₂τ)^{ω₂} = ((0,u),0) ^ᶻ ω₂ = 1` by (c) with odd order (rule 1). No second-order residue —
consistent with `NONCOMPACT_WILD_ROW`'s boundary column being Gate-D (first-order) data only.

### 3.6 Assembly

All five block values have been computed; the remaining κ-cross-terms between blocks vanish
(`f(·,0) = 0`, `m_1 = 0`, and E's V-part is 0), giving

```
fib(eval R) = q c₀ + [q c₀ + f(c₀, A⁻¹c₀) + m_{â⁻¹}(c₀)] + 0 + 0 + polar q (L_c c₀) c₁
            = npcQ0(c₀) + polar q c₁ (lcOp c₀).            ∎
```

The proof is a straight-line finite computation: no cohomology, no census axioms, no
topology beyond the discrete instances the evaluator needs. Every step is either a
definitional rewrite of the `Sd`/`CentExt`/`kappa0` simp set or one of the four sub-lemmas
(a)–(d).

### 3.7 What is missing, exactly

1. **(c) + (d)** — the `ω₂`-power bridge and norm vanishing (§3.0): new, elementary,
   ~120 ln together, on top of existing `omega2Exp` congruences.
2. **The (b)-slice simp kit** — Heisenberg-slice product/inverse/commutator/conjugation
   lemmas over `CentExt (kappa0Cocycle …)`: new, ~150 ln, pure `rfl`-adjacent rewrites.
3. **The word + marking defs** (§2.2) and the power-law `y^k` induction of §3.1: ~150 ln.
4. **Nothing else.** In particular NOT needed: `padicOmega2` additivity (V4), a
   `Zhat → ZMod N` residue map (the G1 note's other flag — per-element `orderOf` reduction
   suffices), the twisted symbolic engine, S1.5's normalizer, the Fox/Stokes layers
   (`stokesEval`/`lemma_5_7_*` are the *mixed*-jet toolkit — the quadratic route via
   `CentExt κ⁰` is self-contained, which is also how the ℚ₂ side did it:
   `QZero_eq_relZPair_kappa0`, `RelatorGammaA.lean:223`), and any census axiom (§7).

## 4. File map and NC2+ tickets

(to be filled)

## 5. Feasibility spike

(to be filled)

## 6. Timing: now vs post-G-1 (WNP-b/c)

(to be filled)

## 7. Risks

(to be filled)

## 8. Owner questions

(to be filled)
