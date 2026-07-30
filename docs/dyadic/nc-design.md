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

**Status: complete.** Statement designed and spike-elaborated verbatim (§5, zero errors, one
intentional `sorry`); two of the four structural sub-lemmas plus the slice mechanism's two
atomic laws proved in scratch at std-3; tickets NC2–NC6 sized (§4); recommendation: prove now
(§6).

---

## 0. Headline verdicts

| # | Question | Verdict |
|---|---|---|
| V1 | Does the corrected formula state cleanly in existing vocabulary? | **Yes — every piece elaborates from merged code** (spike §5). Word = `PWord (Generator n)` over F2's syntax with `deltaW`/`etaHatZ`; evaluation = F2's `Marking.eval` into `CentExt (kappa0Cocycle dat hdat)` over `Sd C V` (the ℚ₂ κ⁰-extension layer, `GQ2/GaussZ/RelatorGammaA.lean`); form data = `QuadraticFp2.polar` + `FactorSet`/`IsEquivariantFactorSet` (`GQ2/OrbitData.lean:43/:54`). No new type is needed. |
| V2 | Proof difficulty | **Mechanical, and cheaper than the twisted-engine framing suggests.** At the Gate-E marking (wild letters trivial-lower, `N.py:891`) the whole computation collapses into the Heisenberg slice `{((v,1),z)}` of the κ⁰-extension. §3 works the evaluation block-by-block by hand: `E_{r,η}` evaluates to the **central** element `((0,1), b_q(L_c c₀, c₁))` with `L_c c₀` literally the sum of the three inverse-conjugators of the D-block — the corrected operator `A⁻¹+B+BA⁻¹` falls out of `conjR`'s `g⁻¹·(−)·g` convention in three lines. One block is genuinely nontrivial (the `(x₀τ)^{ω₂}`-power inside `δ₀`, §3.3). |
| V3 | Hypothesis bundle | **Strictly weaker than "ramified simple"** — the identity needs only: char 2 (`hV2`), the factor-set laws (`hdat`), `Odd (orderOf u)` (rule 1's hypothesis), and `V^u = 0` (rule 2's). Simplicity, faithfulness, nonsingularity, invariance of `q` (derivable from `hdat` in char 2), the tame relation `sus⁻¹ = u^q`, and `η` a unit are **not needed for the identity**. Each reduction rule's hypothesis is stated, per the engine-side caveat; a companion lemma recovers `V^u = 0` from simple + ramified + `⟨u⟩`-normality for the WNP instantiation (§2.4). |
| V4 | `padicOmega2` additivity (the G1 flag) | **Not needed.** The draft's sum exponent `η̂−2^r` has no `etaHatZ` spelling (its odd components are `1−2^r ≠ 1`); the AST — and the Lean word — use the product conjugator `σ^{η̂}·σ^{−2^r}`, and element-level additivity is the existing `zpowHat_mul` (already used inside `zpowHat_etaHatZ`, `Syntax.lean:229-231`). Commuting lemmas for powers of one base are one-liners via `zpowHat_mul` + commutativity of `ℤ̂`. |
| V5 | Missing machinery | Exactly one small new layer: the **per-element `ω₂`-power bridge** in the extension (`powOmega2 y = y^m` for `ord y ∣ 2m`, `m` odd, §3.3) + the elementary **norm-vanishing** lemma (`V^u = 0` ⇒ `Σ_{i<m} uⁱ• = 0`). Both build on congruence lemmas already in the repo (`omega2Exp_modEq_one`, `oddPart_dvd_omega2Exp`, used at `Syntax.lean:122/:133`) — and **both are already proved in the spike, std-3** (§5). Everything else is assembly. |
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
noncomputable def npcMarking (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (s u : C) (c₀ c₁ : V) : Marking 2 (CentExt (kappa0Cocycle dat hdat)) :=
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

### 3.0 The four structural sub-lemmas (new, small)

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

### 4.1 File map

New directory **`GQ2/Dyadic/NpcJet/`**, **plain (non-module) files** — forced: the proof
imports both F2's module-style Word layer *and* the plain ℚ₂ κ⁰ layer
(`GQ2/GaussZ/RelatorGammaA.lean` has no `module` header), and module files may not import
plain ones. The spike confirms the mixed import works in a plain file. Names steer clear of
the WNP lane's reserved `GQ2/Dyadic/Words/Npc.lean` / `GQ2/Dyadic/Certificates/Npc*.lean`.

| file | contents |
|---|---|
| `NpcJet/Blocks.lean` | `npcDBlock`/`npcEBlock`/`npcWord`, `lcOp`, `npcQ0`, `sliceElt`, `npcMarking`, statement skeleton; the slice simp kit (product/inversion/conjugation/commutator as **named lemmas**, replacing the spike's `show`-style) |
| `NpcJet/Omega.lean` | κ-free `C`-line hom + `orderOf` transport; `zpowHat_omega2_eq_pow_of_dvd_two_mul` (spike-proved); `sum_pow_smul_eq_zero` (spike-proved); the `y^k` power law on `((v,c),z)` and `y^m = ((0,1), z_m)` |
| `NpcJet/Delta.lean` | δ₀ evaluation (§3.1), D-block (§3.2), E-block (§3.3) |
| `NpcJet/Main.lean` | front/boundary blocks (§3.4/3.5), h = 0 assembly = **`npc_cross_operators`**, `M_c`-reading docstring |
| `NpcJet/Handles.lean` | general-h tail (§2.5); `hVu_of_simple` companion; concrete-module stress pin |

### 4.2 Tickets (campaign model policy: fable = hard seams, opus = well-specified fills)

| id | title | model | files owned | depends on | est |
|---|---|---|---|---|---|
| NC2 | defs + statement + slice simp kit | opus | `NpcJet/Blocks.lean` | this memo (statement frozen §2) | ~350 ln |
| NC3 | ω₂/norm machinery (transplant spike proofs; `y^k` law) | opus | `NpcJet/Omega.lean` | memo only (∥ NC2) | ~300 ln |
| NC4 | δ₀/D/E evaluation theorems (the `z_m` bookkeeping seam) | fable | `NpcJet/Delta.lean` | NC2, NC3 | ~450 ln |
| NC5 | assembly: headline theorem at h = 0 | fable | `NpcJet/Main.lean` | NC4 | ~350 ln |
| NC6 | handle tail + `hVu_of_simple` + stress pin | opus | `NpcJet/Handles.lean` | NC5 | ~300 ln |

Sequencing: NC2 ∥ NC3 → NC4 → NC5 → NC6; one lane (suggest the freed `lg` worktree,
branch-per-ticket as usual). Acceptance for the commission = NC5 (the h = 0 headline,
std-3); NC6 completes the `plus_form_noncompact` shape. Total ≈ 1750 ln — comparable to a
single HM-lane ticket, and the two seam tickets carry the friction notes of §5.3.

## 5. Feasibility spike

Scratch file (uncommitted, per constraints): `NCSpike.lean`, reproduced in full in the
Appendix. Checked with `lake env lean` against this worktree's built cache
(toolchain v4.31.0-rc2, `dyadic` head `337647f`).

### 5.1 Result: everything elaborates; (c), (d) and (b)'s atomic laws are proved

| item | status |
|---|---|
| `npcDBlock` / `npcEBlock` / `npcWord` (§2.2, F2 vocabulary) | **elaborates** |
| `lcOp` / `npcQ0` / `npcMarking` (operator, diagonal, Gate-E marking) | **elaborates** |
| **`npc_cross_operators`** — the §2.3 headline statement, verbatim | **elaborates** (single `sorry` = the NC4/NC5 proof body) |
| `sum_pow_smul_eq_zero` — rule 2 (norm vanishing) | **PROVED**, 11 ln |
| `zpowHat_omega2_eq_pow_of_dvd_two_mul` — rule 1 / §3.0(c) bridge | **PROVED**, ~28 ln, via `powOmega2_pow_eq` (`GQ2/Omega2.lean:89`) + `omega2Exp_modEq_one`/`oddPart_dvd_omega2Exp` (:38/:26) |
| slice product law + slice inversion law — the §3.0(b) mechanism's two atomic ingredients | **PROVED** (4 ln each, on a typed `sliceElt`) |
| axiom check on the proved lemmas | **exactly `[propext, Classical.choice, Quot.sound]`** (std-3) |

Final run: zero errors, one `sorry` warning (the headline body). Not probed: sub-lemma (a)
(the κ-free `C`-line hom — a 5-line `MonoidHom` construction) and (b)'s commutator/
conjugation composites (their two atomic ingredients are proved; the composites are NC2's
named-lemma kit). The §3.7 missing-machinery list therefore shrinks to: the slice kit as
named lemmas, the `y^k` power-law induction, and assembly.

### 5.2 What the spike settles

* The mixed import `GQ2.Dyadic.Word.Eval` (module-style) + `GQ2.GaussZ.RelatorGammaA`
  (plain) works in a plain file — the §4.1 file map is viable.
* `Marking.eval` into `CentExt (kappa0Cocycle dat hdat)` synthesizes all five evaluator
  typeclasses from finite + discrete — no new instances needed.
* The η̂-quantification via `(η : ℤ_[2])` + `etaHatZ`/`etaPow` and the `2^r`-quantification
  via `zpow`-of-`ℤ` both elaborate symbolically — WC-Npc's "for all allowed r, η" is
  representable exactly (and more: §2.4).
* No `padicOmega2`-additivity, no `Zhat → ZMod N` residue map, no new axiom was needed
  anywhere (V4/V5 confirmed by construction).

### 5.3 Elaboration frictions found (recorded for NC2/NC4)

1. **Raw `Prod` literals shadow the extension's algebra.** `(Sd.mk v 1, z) : CentExt …`
   ascriptions notwithstanding, applying `*` or `.fib` to raw pairs lets Lean unfold
   `CentExt` (a plain `def`) to `Sd C V × ZMod 2` and find `Prod`'s component-wise `Mul` —
   which is the *wrong* multiplication — after which `CentExt.mul_fib` cannot fire (and an
   unascribed literal can even default `C := ℕ`). **Mitigation (verified in the spike):
   route every element through a typed constructor** (`sliceElt`); `Marking.ofLetters`'s
   binder types protect `npcMarking`, and `Marking.eval` multiplies through its `[Group G]`
   instance, so evaluation itself is safe.
2. `CentExt.fib` on expression-typed terms needs the cocycle passed explicitly
   (`CentExt.fib (c := …)`) or a binder-typed argument; dot-notation on `def`-typed
   *binders* is fine (the headline statement uses it).
3. The `show`-style definitional steps in the probes should become named simp lemmas in
   NC2 (`sliceElt_mul`, `sliceElt_inv`, `sliceElt_conj`, `sliceElt_comm`) — same content,
   robust against toolchain-bump reduction changes.

## 6. Timing: now vs post-G-1 (WNP-b/c)

**Recommendation: prove now (dispatch NC2–NC5 at the next free slots).** Grounds:

* **No gate blocks it.** The proof rides F2 + the merged ℚ₂ κ⁰ layer only — not G-1, not
  the WW lane, not any AX flip. It is std-3 end to end (§7 discipline), so it cannot
  disturb the census or the capstone prints.
* **It is WNP-c pulled forward, not duplicated.** The dependency picture: WW3 builds the
  Stokes *chain map* + composition-series extension (packet item (4)) — disjoint content;
  WW4 builds `HessianCertificate` *packaging* (change-of-variables records, phase
  interface) — the NC theorem is precisely the mathematical identity WNP-c's row
  ("`Q₀(c₀)+b_q(c₁,L_c c₀)`, explicit invertible `L_c`") will wrap, minus per-module-class
  invertibility of `L_c`, which stays WNP-c (it genuinely varies with the module and
  belongs with the Fox/normal-form clauses). WNP-b (Fox certificate) is untouched. When the
  WNP lane runs post-G-1, WNP-c cites `npc_cross_operators` instead of re-deriving it.
* **It retires an owner-accepted debt early.** R3(a) accepted the twisted-path diagnostic
  status "meanwhile"; NC5 replaces it with a proof-grade statement — and the proof's shape
  (§3.2) makes the refutation of eq:Ncross *visible* (the three inverse-conjugators), which
  strengthens errata item 5's standing if the packet author pushes back.
* **The one coordination cost** is the word tree: WNP-a (post-G-1, opus) owns
  `Words/Npc.lean` and WW5's one-tree gate will want a single `PWord`. Options in Q3;
  either is cheap (`npcWord` is 15 lines; an `eval`-equality bridge is `rfl`-adjacent).

Cost of the alternative (fold into WNP-b/c post-G-1): the identity would sit unproved for
the whole G-1/WW/G2 span, the diagnostic-status debt stays open, and nothing is saved —
the WNP tickets would do the same ~1750 ln then, without today's spike momentum.

## 7. Risks

1. **Assembly slips, not statement slips.** §3's block computation was done by hand
   (cancellations included) and cross-checks against four independent Python anchors
   (`L_c`, `Q₀`, the α ≥ 2 condition, the `x₂`-exclusion) — but it is not yet
   Lean-verified end to end. Failure mode is a stuck `rw` in NC4/NC5, not a false theorem:
   the statement itself is machine-validated (S3.2's 6-instance battery) and
   spike-elaborated. Contingency: if a block value differs, the memo's per-block form
   localizes the discrepancy immediately.
2. **The `z_m` bookkeeping** (δ₀'s fiber charge) is the largest single computation; it is
   deliberately *quarantined* — the E-block theorem is charge-independent (§3.3), so NC4
   can prove `[D,x₁]`'s value without ever normalizing `ζ_D`. Only δ₀'s `y^m` reduction
   (§3.1) needs the charge sum, and only up to "some `z_m : ZMod 2` depending on `c₀`
   alone".
3. **Toolchain fragility** of definitional `show`-steps — mitigated by the named-simp-kit
   mandate (§5.3(3)).
4. **Board drift**: the WNP lane note (`tickets.md:896-902`) still displays the refuted
   draft operators `M_c = A, L_c = A⁻¹` in its spec text (the :424 log entry corrects it,
   but the lane row does not). NC1 cannot edit the board — orchestrator fix, Q4.
5. **Scope boundary**: the theorem is the jet identity at the Gate-E marking
   (wild-trivial-lower, `c₂ = 0`). The three-variable diagnostic (offset on `x₂`) and
   invertibility of `L_c` per module class are *deliberately* out of scope — they are
   Gate-D data resp. WNP-c's certificate clauses. Anyone citing NC5 for "the pairing is
   restored" still needs `L_c` invertible on their module (per-module, easy on the
   battery's simples, e.g. `decide` on concrete instances in NC6's stress pin).
6. **Naming**: `GQ2.Dyadic.sum_pow_smul_eq_zero` and the bridge lemma are generic-sounding;
   if a mathlib upstream candidate exists (`orbitNorm`-adjacent), NC3 should
   `lean_local_search` before committing names (spike found no clash in this cache).

## 8. Owner questions

1. **File map** (§4.1): approve the new plain-file dir `GQ2/Dyadic/NpcJet/`? (Alternative:
   park everything in one file `GQ2/Dyadic/NpcJet.lean` and split later; the 5-file map
   matches the ticket cut.)
2. **Statement form** (§2.4): adopt the hypothesis-minimal headline (no `1 ≤ r`, no
   `IsUnit η`, direct `hVu`), with `hVu_of_simple` as the packet-facing companion — or
   mirror `prop_6_18_ramified`'s full ramified-simple bundle in the headline for
   uniformity? (Design recommends the former: strictly stronger theorem, cleaner reuse.)
3. **Word-tree ownership**: pre-agree `npcWord` as *the* eq:Npc-word tree that WNP-a will
   adopt (WW5 one-tree gate), or let WNP-a own the tree and NC keep a proven
   `Marking.eval`-equality bridge? (Recommend the former — the tree is this memo's §2.2,
   already spelled compressed-D per §8.3 of the campaign doc.)
4. **Board fix** (orchestrator, not NC): update the WNP lane note `tickets.md:896-902` to
   the corrected operators with a pointer here; optionally add the NC2–NC6 rows of §4.2.
5. **Dispatch**: approve NC2–NC6 now (≈1750 ln, one lane, NC2 ∥ NC3 start), or hold until
   MC3/MC4 land per the current dispatch queue?
6. **`M_c` presentation**: docstring-only adjoint reading (as designed), or a stated
   corollary `npc_cross_operators_adjoint` exhibiting `M_c = A + B⁻¹ + AB⁻¹` in the
   `(c₀, c₁)`-slot for the untwisted-engine comparison? (Docstring recommended; the
   corollary adds an object with no Lean consumer.)

## 9. Census / axiom discipline

The theorem and all NC2–NC6 lemmas are **std-3** (`propext`, `Classical.choice`,
`Quot.sound`) — spike-verified on the two proved lemmas, and structurally forced for the
rest: the development touches only finite group theory, factor sets, and the F2 evaluator
(whose `Classical.propDecidable` use in `pro2` is not on this path; `noncomputable` defs
are fine). **No obligation axiom (B-series) is cited or needed**; no `EXPECTED_AXIOMS`
change; the ℚ₂ capstone prints cannot move (nothing upstream of them is edited). The only
existing-census citation in the eventual files is *zero* — consumers that later specialize
`V` to genuine Galois modules bring their own hypotheses, exactly as `DetRamified` does.

---

## Appendix: the spike file (verbatim, final green state)

One `sorry` (the headline body — NC4/NC5's work); everything else proved; zero errors.

```lean
/-
NC1 feasibility spike (uncommitted scratch; see docs/dyadic/nc-design.md §5).
Typechecks the corrected-L_c statement skeleton against the built cache.
-/
import GQ2.Dyadic.Word.Eval
import GQ2.GaussZ.RelatorGammaA

namespace GQ2.Dyadic

open WordCoh2 SectionEight.AffineTLift QuadraticFp2

/-! ## Statement-level definitions (nc-design §2.2) -/

/-- The compressed D-block `δ₀^A (δ₀ δ₀^A)^{B⁻¹}`, `A = σ^{η̂}`, `B = σ^{2^r}`
(draft eq:Npc-word; `N.py` `d_block_noncompact`, compressed spelling). -/
noncomputable def npcDBlock (η : ℤ_[2]) (r : ℕ) : PWord (Generator 2) :=
  .mul (.conj (deltaW 0) ((PWord.gen .sigma).etaPow η))
    (.conj (.mul (deltaW 0) (.conj (deltaW 0) ((PWord.gen .sigma).etaPow η)))
      (.zpow (.gen .sigma) (-(2 ^ r : ℤ))))

/-- The correction `E_{r,η} = [D_{r,η}, x₁]`. -/
noncomputable def npcEBlock (η : ℤ_[2]) (r : ℕ) : PWord (Generator 2) :=
  .comm (npcDBlock η r) (.gen (.wild 1))

/-- The corrected noncompact `N_α` relator (draft eq:Npc-word), `h = 0` core. -/
noncomputable def npcWord (α r : ℕ) (η : ℤ_[2]) : PWord (Generator 2) :=
  .mul (.zpow (.gen (.wild 0)) ((2 : ℤ) + 2 ^ α))
    (.mul (.comm (.gen (.wild 0)) ((PWord.gen .sigma).etaPow η))
      (.mul (PWord.invConj (.gen (.wild 2))
              (.mul (.gen (.wild 1)) (.zpow (.gen .sigma) ((2 : ℤ) ^ r))))
        (.mul (PWord.omega2Pow (.mul (.gen (.wild 2)) (.gen .tau)))
          (npcEBlock η r))))

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-! ### Reduction rule 2 (`tame-geom-vanishes`), proved: norm vanishing from `V^u = 0` -/

/-- **Rule 2's Lean form**: if `u` fixes only `0` and `u ^ m = 1`, the `u`-norm vanishes.
No semisimplicity, no projector theory: the norm is `u`-fixed by reindexing. -/
theorem sum_pow_smul_eq_zero {u : C} (hVu : ∀ v : V, u • v = v → v = 0)
    {m : ℕ} (hm : u ^ m = 1) (v : V) :
    ∑ i ∈ Finset.range m, u ^ i • v = 0 := by
  refine hVu _ ?_
  rw [Finset.smul_sum]
  have hshift : ∀ i : ℕ, u • u ^ i • v = u ^ (i + 1) • v := by
    intro i
    rw [← mul_smul, ← pow_succ']
  simp only [hshift]
  have h1 := Finset.sum_range_succ' (fun i => u ^ i • v) m
  have h2 := Finset.sum_range_succ (fun i => u ^ i • v) m
  simp only [pow_zero, one_smul, hm] at h1 h2
  exact add_right_cancel (h1.symm.trans h2)

variable [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  {q : V → ZMod 2}

/-- **The corrected cross operator** `L_c = A⁻¹ + B + B·A⁻¹` as the module action
(`A`-element `s ^ᶻ η̂`, `B`-element `s ^ 2^r`) — the S3.2 machine value replacing draft
eq:Ncross's `A⁻¹`. -/
noncomputable def lcOp (s : C) (η : ℤ_[2]) (r : ℕ) (v : V) : V :=
  (s ^ᶻ etaHatZ η)⁻¹ • v + s ^ (2 ^ r) • v + (s ^ (2 ^ r) * (s ^ᶻ etaHatZ η)⁻¹) • v

/-- The diagonal part `Q₀(c₀) = β_A(c₀, A⁻¹c₀) + c_{A⁻¹}(c₀)` in factor-set vocabulary. -/
noncomputable def npcQ0 (dat : FactorSet C V) (s : C) (η : ℤ_[2]) (c₀ : V) : ZMod 2 :=
  dat.f c₀ ((s ^ᶻ etaHatZ η)⁻¹ • c₀) + dat.m ((s ^ᶻ etaHatZ η)⁻¹) c₀

/-- The Gate-E marking (`N.py` `symbolic_marking`): `σ ↦ s`, `τ ↦ u`, wild letters
trivial-lower with offsets `c₀, c₁` on `x₀, x₁` and none on the boundary letter `x₂`. -/
noncomputable def npcMarking (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (s u : C) (c₀ c₁ : V) : Marking 2 (CentExt (kappa0Cocycle dat hdat)) :=
  Marking.ofLetters ((Sd.mk 0 s, 0)) ((Sd.mk 0 u, 0))
    ![((Sd.mk c₀ 1, 0)), ((Sd.mk c₁ 1, 0)), ((Sd.mk 0 1, 0))]

/-! ## The headline statement (nc-design §2.3) -/

/-- **The corrected noncompact-N cross-operator identity** (R3(a) commission; skeleton). -/
theorem npc_cross_operators (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) :
    ((npcMarking dat hdat s u c₀ c₁).eval (npcWord α r η)).fib
      = npcQ0 dat s η c₀ + polar q c₁ (lcOp s η r c₀) := by
  sorry

/-! ## Reduction rule 1 (`tame-omega2-power`) at the extension, statement -/

/-- **Rule 1's Lean form**: the `ω₂`-power bridge — for `orderOf y ∣ 2m`, `m` odd,
the `ω₂`-power is the `m`-th power.  (nc-design §3.0(c); via `zpowHat_omega2` +
`powOmega2_pow_eq` + the two `omega2Exp` congruences.) -/
theorem zpowHat_omega2_eq_pow_of_dvd_two_mul {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] {y : P} {m : ℕ} (hm : Odd m)
    (hdvd : orderOf y ∣ 2 * m) : y ^ᶻ omega2 = y ^ m := by
  have hm0 : m ≠ 0 := by rintro rfl; simp [Nat.odd_iff] at hm
  have h2m : 2 * m ≠ 0 := by lia
  rw [zpowHat_omega2, ← powOmega2_pow_eq y hdvd h2m]
  refine pow_eq_pow_iff_modEq.mpr (Nat.ModEq.of_dvd hdvd ?_)
  -- `omega2Exp (2m) ≡ m [MOD 2m]`, by CRT over `2 · m`
  have hnd : ¬ (2 : ℕ) ∣ m := by
    rw [Nat.two_dvd_ne_zero, ← Nat.odd_iff]
    exact hm
  have hfac : (2 * m).factorization 2 = 1 := by
    rw [Nat.factorization_mul two_ne_zero hm0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hnd]
  have h2part : omega2Exp (2 * m) ≡ m [MOD 2] := by
    have h1 : omega2Exp (2 * m) ≡ 1 [MOD 2] := by
      have := omega2Exp_modEq_one h2m (by rw [hfac]; exact one_ne_zero)
      rwa [hfac, pow_one] at this
    have h2 : m ≡ 1 [MOD 2] := by
      rw [Nat.ModEq, Nat.one_mod, ← Nat.odd_iff.mp hm]
    exact h1.trans h2.symm
  have hoddpart : omega2Exp (2 * m) ≡ m [MOD m] := by
    have hdvdm : m ∣ omega2Exp (2 * m) := by
      have := oddPart_dvd_omega2Exp (2 * m)
      rwa [hfac, pow_one, Nat.mul_div_cancel_left m two_ne_zero.bot_lt] at this
    exact (Nat.modEq_zero_iff_dvd.mpr hdvdm).trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl).symm
  exact (Nat.modEq_and_modEq_iff_modEq_mul
    ((Nat.prime_two.coprime_iff_not_dvd).mpr hnd)).mp ⟨h2part, hoddpart⟩

/-! ## The Heisenberg-slice mechanism (nc-design §3.0(b)), probed -/

/-- Slice elements `((v,1),z)`, as a *typed* constructor.  (NC2/NC4 friction note, found by
this spike: a raw pair `(Sd.mk v 1, z)` with a type ascription still lets `Prod`'s
component-wise `Mul`/projections be found after `CentExt` unfolds — `*` then means the WRONG
multiplication and `CentExt.mul_fib` does not fire.  Route every slice element through a
`def` typed `CentExt …`, as here, and the instance paths stay canonical.) -/
noncomputable def sliceElt (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (v : V) (z : ZMod 2) : CentExt (kappa0Cocycle dat hdat) := (Sd.mk v 1, z)

/-- The slice product law: on `{((v,1),z)}` the κ-correction is `f(v,w)` — the Heisenberg
group of `(V, f)` sits inside the extension. -/
example (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat) (v w : V) (z z' : ZMod 2) :
    (sliceElt dat hdat v z * sliceElt dat hdat w z').fib = z + z' + dat.f v w := by
  rw [CentExt.mul_fib, kappa0Cocycle_κ]
  show z + z' + (dat.f v ((1 : C) • w) + dat.m 1 w) = z + z' + dat.f v w
  rw [one_smul, hdat.m_one, add_zero]

/-- The slice inversion law: `((v,1),z)⁻¹` has fiber `z + q v` in char 2 — the `q`-charge of
inversion, the second ingredient of the §3.0(b) commutator mechanism. -/
example (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    ((sliceElt dat hdat v z)⁻¹).fib = z + q v := by
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_of_add_eq_zero_left (hV2 x)
  show z + (kappa0Cocycle dat hdat).κ (Sd.mk v 1) (Sd.mk v 1)⁻¹ = z + q v
  rw [kappa0Cocycle_κ]
  show z + (dat.f v ((1 : C) • -((1 : C)⁻¹ • v)) + dat.m 1 (-((1 : C)⁻¹ • v))) = z + q v
  rw [inv_one, one_smul, one_smul, hneg v, hdat.m_one, add_zero, hdat.f_diag]

end Module

end GQ2.Dyadic
```

*Run log*: `lake env lean NCSpike.lean` → one warning (`npc_cross_operators` uses `sorry`),
zero errors; `#print axioms` on the two proved theorems → `[propext, Classical.choice,
Quot.sound]`.
