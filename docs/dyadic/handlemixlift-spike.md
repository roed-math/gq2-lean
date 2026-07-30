# MC-HM — the `HandleMixLift` spike: the binder, and the Dehn–Nielsen/Sp realization

**Ticket.** MC-HM, authorised by the owner at gate R2 (S2.4 memo §13 Q1: "binder now plus a bounded
spike on the Dehn–Nielsen/Sp-realization route; the spike would settle L, N and M at once").
Memo-only ticket: no `.lean` file is edited, no board entry is written.

**Inputs.** S2.4's marked-stabilization memo §6, §7
(`~/claude/general_2adic/artifacts/reports/marked-stabilization-memo.md`, read-only), MC1
(`docs/dyadic/mc-design.md`) §4.2, §5, §6, §8, MC2 (`GQ2/Dyadic/MarkedCore/Cores.lean`),
`GQ2/PeripheralAction.lean:72–140` (B8), `GQ2/Roe/MarkedPro2.lean:141` (`BLabHypothesis`).

**Conventions.** The repo's (`GQ2/Words.lean:56,59`): `x ^ g = conjP x g = g⁻¹ x g`,
`[x,y] = commP x y = x⁻¹ y⁻¹ x y`. Consequently
`[xz, y] = [x,y]^z · [z,y]` and `[x, yz] = [x,z] · [x,y]^z`.

---

## 0. Headline verdicts

| # | verdict |
|---|---|
| **V1** | **The binder is written** (§1), in the `BLabHypothesis` pattern, with per-family instantiations and the exact MC5/WL threading points. This is the required deliverable and it stands independently of everything below. |
| **V2** | **Route (b) resolved: the triple commutator obstructs the candidate, not the lift.** S2.4 §6.4's residue `[[σ,v₁],u₁]` is reproduced verbatim by machine (§3); it is a defect of *one* substitution, and it is **absorbed** by a corrected substitution. The corrected map is not "the naive one plus an inner twist": it replaces the naive `u₁ ↦ σu₁`, `a ↦ av₁` by a genuinely different pair of words (§4). |
| **V3** | **Route (a) is GREEN, and stronger than S2.4 hoped.** The mixing elements the ν-correction consumes are realized by explicit automorphisms of the *free pro-2 group* that fix the relator **on the nose** (`Φ(P) = P`, not `P^g`, not `∈ ⟨⟨P⟩⟩`). S2.4's "residual gap" — that the realizing automorphism must in addition fix `⟨⟨W·S⟩⟩` because `W` shares the letter `σ` with the surface part — is **empty for the elements needed**: they can be chosen to fix `σ` *and* `x₀` literally, hence `W` literally. Verified by machine for the L collector/`L_tw` core, for `N_α` and for `M_α`, uniformly in the number of handles `h ≤ 4`, in the handle index `j`, and in `α ≤ 4` (§4.5). |
| **V4** | **The 2-adic parameter is not an obstacle.** The correction needs `k = −ν'(ū_j)/ν'(σ̄) ∈ ℤ₂`, and the constructed mixing element is integral. Resolution (§5.2): the intra-handle transvections are exact for **2-adic** exponents (`u ↦ v^k u`, `k ∈ ℤ₂`, because `v^k` commutes with `v`), they generate `SL₂(ℤ₂)` on each handle plane, and conjugating the integral mixing element by `diag(w, w⁻¹)` multiplies its mixing coefficient by `w⁻¹`. Since every `x ∈ ℤ₂` is `2^{v(x)} · unit`, integer powers times unit rescalings exhaust `ℤ₂`. **No compactness of `Aut(D_P)` is needed, and no new axiom** — in particular not B8. |
| **V5** | **The obligation should be restated, then discharged.** What §4–§5 prove is not `HandleMixLift` as S2.4 §2.4 states it (a lift for *every* Smith–Witt stabilizer element) but exactly the statement MC5's proof consumes: `ν_P ∈ ν'·A(P,h)`, i.e. the handle part of the ν-correction (S2.4 §6.1's own reformulation). The recommendation therefore **changes**: replace the binder by the consumed statement and prove it; keep the binder only for the general-`St` version, which nothing consumes. |
| **V6** | **Verdict: PROVED at the mathematical level, PROVABLE-WITH-PLAN in Lean.** Skeleton and sized ticket list in §7 (≈900–1400 lines, 5 tickets, no new machinery, no Labute/levelwise input). Two honest residues: the `L_sq` word (§6.3) and the M-side unit hypothesis (§6.4). |
| **V7 (bonus)** | The same identity **also reaches one of MC1's *core* mixing families for `N_α`** at rank four (§6.5): `N_α`'s relator is a genus-2 surface word times `x₀^{2+2^α}`, so `[x₀,x₁]` and `[σ,x₂]` are mixable by the same construction, exactly, α-uniformly. This bears on MC1 §8 **Decision 2**, which the owner has in front of them. It does **not** extend to `M_α`: the `c^{2^α}` factor sits *between* the two commutators and breaks the adjacency the identity needs (checked, §6.5). |

---

## 1. The binder (land-ready) — required output

Modelled on `BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean:141`) and on MC1 §6.4's
`MLabHypothesis`/`NMixHypothesis`: a `def`, **never** an axiom (plan §0.1; MC1 §8 Decision 2(D) is
excluded in substance).

### 1.1 The statement

The frame vocabulary is MC3/MC4's (`mc-design.md` §6.2): `MDecomposition α n` /
`NDecomposition α n` carry the frame `e`, and `IsMStabilizer`/`IsNStabilizer` are the
χ-preserving cup isometries. `HandleMixLift` is stated in that vocabulary, per core, with the
handle plane singled out.

```lean
namespace GQ2.Dyadic.MarkedCore

/-- The handle plane of the degree-`n` frame: the span of the `2h` handle coordinates
(`handleIdxU`/`handleIdxV`, `Cores.lean:148,152`).  `χ ≡ 1` on it
(`handleWord_wordLift_one`, `Cores.lean:362`) and it carries `h` orthogonal hyperbolic
cup blocks (MC1 §4.2). -/
def handlePlaneM (α n : ℕ) (B : MDecomposition α n) : Submodule ℤ_[2] (Frame B) := …

/-- **`HandleMixLiftHypothesis` (hypothesis form — never an axiom).**  S2.4's obligation
(memo §2.4, §6): every element of the Smith–Witt stabilizer whose handle↔core block is
nonzero — the S3 mixing stratum of MC1 §5.3, unreachable from the elementary Nielsen lifts
(S1), from the B8 unit scalings (S2), or from the intra-handle symplectic block
(MC1 §4.2) — lifts to a continuous automorphism of the presented core.

By S2.4 Lemma 6.3 the hypothesis cannot be dropped: blocks (a) and (b) preserve the handle
plane setwise, so no element of the subgroup they generate can correct a `ν'` that is
nonzero on it. -/
def MHandleMixHypothesis (α n : ℕ) (B : MDecomposition α n) : Prop :=
  ∀ φ : ContinuousMulEquiv (topAbelianization (DM α n)) (topAbelianization (DM α n)),
    IsMStabilizer α n B φ →
      ∃ Ψ : ContinuousMulEquiv (DM α n) (DM α n),
        ∀ x, B.e (abMk (Ψ x)) = B.e (φ (abMk x))

def NHandleMixHypothesis (α n : ℕ) (B : NDecomposition α n) : Prop := …   -- mirror
```

Two remarks that must travel with the `def`:

* **It is the same shape as MC1's `MMixHypothesis`/`NMixHypothesis`**, and deliberately so: MC1 §8
  Decision 2(B) already tabled that shape, so this adds a third instance of a decision already in
  front of the owner rather than a new decision (S2.4 §6.6 Route (B)).
* **It is stated on the concrete presented core, not on abstract `G`.** Unlike
  `MLabHypothesis` (MC1 §6.4, R6), the abstract-`G` form is *not* forced here: both sides of the
  statement are `D_P`, so the `BLabHypothesis` quarantining convention
  (`MarkedPro2.lean:133–136`) applies verbatim and should be used.

### 1.2 Per-family instantiations

The handle block is identical across the five branch words (S2.4 §6.6), so one `def` per core
family suffices and the L family reuses the frozen rank-three base:

| family | instance | rank-three base | what the binder adds |
|---|---|---|---|
| **L** (odd `n = 2h+1`; collector, `L_tw`) | `LHandleMixHypothesis h` on `D_L h` | already discharged (`GQ2/Roe/MarkedPro2.lean`, `MarkedMatching.lean`, modulo `BLabHypothesis`) | `hMix` alone — this is S2.4 §2.3's `C_mark = 1` claim |
| **L_sq** (odd `n`) | `LsqHandleMixHypothesis h` | **not** discharged (`C_mark = 3`, the 2-adic orientation computation) | `hMix` **plus** the rank-three input (S2.4 §2.2) |
| **N** (even `n`, rank 4 + handles) | `NHandleMixHypothesis α n B` | `NLabHypothesis α n` (MC1 §6.4) | `hMix`, plus MC1's separate core-mixing binder `NMixHypothesis` |
| **M** (even `n`, rank 4 + handles) | `MHandleMixHypothesis α n B` | `MLabHypothesis α n` | `hMix`, plus `MMixHypothesis` |

`MMixHypothesis`/`NMixHypothesis` (MC1 §8 Decision 2) and `*HandleMixHypothesis` (this memo) are
**different** obligations and must not be merged: the first is core↔core mixing at rank four
(families M4–M7, N5–N6), the second is handle↔core mixing at rank `n+2`. §6.5 reports that the
technique of §4 reaches part of the first for `N`.

### 1.3 Where it threads

* **MC5** (`mc-design.md` §6.3): `marked_matching_reduction` currently takes
  `hLift : ∀ φ, IsMStabilizer α n B φ → ∃ Ψ, …`. That antecedent is exactly
  `MHandleMixHypothesis` **conjoined with** MC1's `MMixHypothesis` and the S1/S2 families. The
  binder therefore threads by **splitting that one field into three**, and `MarkedCoreCertificate`
  itself is untouched (the certificate's `correction` field is the *output*, not the input).
* **WL lane** (S2.4 §8.1): `marked_L_core_stabilize` and `marked_square_core_stabilize` take it as
  the fourth explicit argument, exactly as S2.4 §2.2/§2.3 already write it (`hMix : HandleMixLift …`).
* **WC lane**: the collector's marked core is byte-identical to `L_tw`'s at every certified degree
  (S2.4 §2.3), so WC consumes the *same* instance — one binder, two words.
* **Capstone print**: a `def`-shaped hypothesis is invisible to the axiom census
  (`AxiomLedger`), exactly as `BLabHypothesis` was before L6; census stays at 11.

**This section is the deliverable regardless of §§2–7.** If the owner declines the discharge plan,
§1 lands as-is and every other lane stays unconditional.

---

## 2. The obligation, in word terms

Write the type-L relator at degree `n = 2h+1` (S2.4 §6.4, collector/`L_tw`):

```
P  =  W · [a, σ] · ∏_{j=1..h} [u_j, v_j] ,        W = x₀^{σ²} · x₀ ,   a = x₁
```

so `P` is a **genus-`(h+1)` surface word `S := [a,σ]·∏_j[u_j,v_j]` times a prefix `W`**, and the
frame is `ℤ/2·t ⊕ ℤ₂ā ⊕ ℤ₂σ̄ ⊕ P_han` with `t = x̄₀`, `P_han = ⟨ū_j, v̄_j⟩` (S2.4 §6.2).

The element needed (S2.4 §6.4) is the symplectic unipotent `U_{σ̄,v̄_j}` — on the frame

```
ū_j ↦ ū_j + k·σ̄ ,   ā ↦ ā − v̄_j ,   σ̄, v̄_j, t, and the other handles  fixed
```

with `k ∈ ℤ₂` chosen so that `(ν'∘φ)(ū_j) = ν'(ū_j) + k·ν'(σ̄) = 0`; `ν'(σ̄) ∈ ℤ₂ˣ` because `ν'`
is surjective on `ker χ ⊇ ⟨σ̄⟩ ⊕ P_han` for type L. The mod-2 cup condition forces the two
coefficients congruent mod 2 (`⟨ū_j + kσ̄, ā + k'v̄_j⟩ = k + k' ≡ 0`), which is why S2.4's display
takes `k` odd with coefficient 1 on the `ā`-side.

The three constraints a *word-level* realization must satisfy are therefore:

1. **(surface)** it preserves `S`, the genus-`(h+1)` surface word — Dehn–Nielsen–Baer/Zieschang
   says the boundary-fixing mapping class group of `Σ_{h+1,1}` does this and surjects onto
   `Sp_{2h+2}(ℤ)`, so *some* realization exists;
2. **(prefix)** it must not disturb `⟨⟨W·S⟩⟩` — and `W` shares the letter `σ` with `S`. This is
   S2.4's "precise and bounded residual gap" (§6.6 Route (A));
3. **(2-adic)** the coefficient `k` must be an arbitrary 2-adic integer, whereas
   `Sp_{2h+2}(ℤ)` is only dense in `Sp_{2h+2}(ℤ₂)`.

§3 disposes of the naive candidate, §4 solves (1)+(2) simultaneously and exactly, §5 solves (3).

---

## 3. Route (b): what the triple commutator does and does not obstruct

### 3.1 The naive candidate, reproduced by machine

With `a ↦ a·v₁`, `u₁ ↦ σ·u₁` and everything else fixed (S2.4 §6.4), the free-group computation
gives, letter for letter,

```
Φ(P)  =  W · [a,σ]^{v₁} · [[σ,v₁], u₁] · [u₁,v₁] · (rest)
```

— **byte-identical to the memo's display**, and

* `Φ(P) ≠ P`;
* `Φ(P)` is **not conjugate to `P`** (checked by cyclic reduction), so the naive candidate does not
  descend to `D_P` at all — not even up to an inner twist. Composing with `inn_g` replaces `Φ(P)`
  by `Φ(P)^g` and cannot repair non-conjugacy.

### 3.2 Diagnosis: two independent defects, only one of them degree 3

Reading the display, the naive candidate has **two** defects:

* a **conjugator mismatch**: `W` is untouched while `[a,σ]` acquires the conjugator `v₁`, so even
  without the commutator residue the relator is not of the matched-conjugator form
  `P ↦ P^g` (MC1 §5.1);
* the **triple commutator** `[[σ,v₁],u₁]`, degree 3 in the Zassenhaus filtration, which is what
  S2.4 §6.4 and MC1 §5.3 identify.

The two are not independent evidence for one obstruction; they are two symptoms of the same wrong
ansatz. Both vanish for the corrected substitution of §4, which is *not* the naive one composed
with anything frame-trivial: it replaces the correction word `v₁` by a **conjugate of `v₁`**
(namely `(v_j^{-1})^{u_j}` moved by `σ` and by the intervening handle block) and replaces
`σ` in `u₁ ↦ σu₁` by a *word of length 9*. That is why the search that found it had to range over
all reduced words, not over the memo's ansatz family.

**Answer to spike question (b):** the obstruction obstructs the naive candidate only. It is not a
degree-3 obstruction to the *lift*, and nothing in the Zassenhaus filtration has to be corrected.

---

## 4. Route (a): the construction, exactly

### 4.1 The mixing automorphism

Fix `h`, a handle index `j`, and set

```
ζ_j  :=  ∏_{i<j} [u_i, v_i]                      (the intervening handle block; ζ_0 = 1)
δ_j  :=  σ · ζ_j · (v_j)^{u_j} · ζ_j⁻¹           (a word of class σ̄ + v̄_j)
```

Define `Φ_j` on the free (pro-2) generators by

```
Φ_j(a)    =  a^σ · δ_j⁻¹
Φ_j(u_j)  =  u_j · ( σ⁻¹ · [a,σ] )^{ζ_j} · (v_j⁻¹)^{u_j}
Φ_j(x)    =  x        for x ∈ { x₀, σ, v_j } ∪ { u_i, v_i : i ≠ j }
```

Then, **as an identity of reduced words in the free group**:

```
Φ_j(W) = W        Φ_j(S) = S        Φ_j(P) = P .
```

At `h = 1`, `j = 0` this is, in full,

```
Φ(a)  =  a · σ · u⁻¹ v⁻¹ u · σ⁻¹                         (length 6)
Φ(u)  =  u · σ⁻¹ · a⁻¹ σ⁻¹ a σ · u⁻¹ v⁻¹ u               (length 9)
```

after absorbing the harmless `T_σ`-factor (`a ↦ σa`, §5.1). Compare the naive candidate
`a ↦ a·v`, `u ↦ σ·u`: the correction words are `σ v^{u} σ⁻¹`-type conjugates, not the bare
letters, and it is exactly that replacement that cancels the triple commutator.

### 4.2 It is an automorphism, with an explicit inverse

Nielsen reduction of the image tuple `(Φ(a), σ, Φ(u), v)` terminates in 12 steps at a tuple of
length-one words, so the images are a **free basis**; back-substitution gives the inverse
explicitly:

```
Φ⁻¹(a)  =  σ⁻¹ a σ · u⁻¹ v u · σ⁻¹ a⁻¹ σ · a
Φ⁻¹(u)  =  v u · σ⁻¹ a⁻¹ σ a σ
Φ⁻¹(σ) = σ ,  Φ⁻¹(v) = v ,  Φ⁻¹(x₀) = x₀
```

and both composites are the identity **on the nose in the free group** (not merely modulo
`⟨⟨P⟩⟩`), with `Φ⁻¹(P) = P`. This matters for Lean: the two-sided inverse is available *before*
descending to `D_P`, so the automorphism of `D_P` is assembled by the `thetaHom`/`thetaEquiv`
pattern (`GQ2/AnabelianBridge/Construction.lean:864/880/929`) with no relator-modulo bookkeeping.

### 4.3 Why the prefix `W` survives — the point of the construction

`Φ_j` moves only `a` and `u_j`. Neither occurs in `W = x₀^{σ²}·x₀`. So `Φ_j(W) = W` **literally**,
and `Φ_j(P) = Φ_j(W)·Φ_j(S) = W·S = P`.

That the *needed* elements can be chosen this way is not an accident, and it is the structural
content of the spike:

> `U_{σ̄,v̄_j}` **fixes `σ̄` and `v̄_j`** (both are isotropic for the cup form and orthogonal to
> each other), and moves only `ā` and `ū_j`. The two letters it must move, `a = x₁` and `u_j`, are
> precisely the two that do **not** occur in `W`. Geometrically: `δ_j` is a simple closed curve
> disjoint from `σ`, so the twist along it can be supported away from the loop `σ`.

S2.4 §6.6 Route (A) asked for the realizing automorphism to "move `σ` only inside `[F,F]`, and
that residue must be absorbed". The answer is sharper: **it need not move `σ` at all.**

### 4.4 The second Eichler family, and the other three families

Clearing `ν'` on the whole handle plane needs, per handle, a second element that clears the
`v̄_j`-coordinate. It is obtained from `Φ_j` by conjugating with the intra-handle `S`-move
(`SL₂` on `⟨ū_j,v̄_j⟩`, itself a product of the exact transvections of §5.1):

```
E'_j := τ_{u_j}(−1) ∘ ( S_j ∘ Φ_j ∘ S_j⁻¹ ) ,      S_j := τ_{v_j}(1) ∘ τ_{u_j}(−1) ∘ τ_{v_j}(1)
```

with frame action `ā ↦ ā − σ̄ + ū_j`, `v̄_j ↦ v̄_j − σ̄`, and `σ̄, ū_j` fixed. It is exact
(`E'_j(P) = P`) and fixes `W`. Explicitly at `h = 1`:

```
E'(a) = σ⁻¹ a σ u⁻¹ v⁻¹ u v u σ⁻¹        E'(v) = u⁻¹ v u σ⁻¹ a⁻¹ σ⁻¹ a σ u⁻¹ v⁻¹ u v
```

Conjugating instead with the **handle-0** `S`-move gives the family that fixes the *first* letter
of the surface handle pair and moves the second — the family the `M_α` core needs, because for `M`
it is `c` (not `d`) that occurs in the prefix. Explicitly, for
`P_M = a²[a,b]·c^{2^α}·[c,d]·∏_j[u_j,v_j]`:

```
Φ^M_j(d)    =  c · d · ζ_j · (v_j⁻¹)^{u_j} · ζ_j⁻¹
Φ^M_j(u_j)  =  u_j · ( c^d )^{ζ_j} · (v_j⁻¹)^{u_j}
```

fixing `a, b, c, v_j` and the other handles; `Φ^M_j(W_M) = W_M` and `Φ^M_j(P_M) = P_M`.

For `N_α`, `W_N = x₀^{2+2^α}·[x₀,x₁]` shares **no** letter with the surface part `[σ,x₂]·∏_j[u_j,v_j]`,
so both families apply and, with them, the whole boundary-fixing mapping class group of
`Σ_{h+1,1}`: `N` is the easy case, not the hard one.

### 4.5 Verification table

All rows are exact reduced-word identities in the free group, checked by an independent
word engine (`fg.py`; conjugacy by cyclic reduction, invertibility by Nielsen reduction).

| word | prefix `W` | shared letter | element | `Φ(W)=W` | `Φ(P)=P` | range checked |
|---|---|---|---|---|---|---|
| L collector / `L_tw` | `x₀^{σ²}x₀` | `σ` | `Φ_j`, `E_j`, `E'_j` | ✓ | ✓ | `h = 1,2,3,4`; every `j < h` |
| `N_α` | `x₀^{2+2^α}[x₀,x₁]` | — | `Φ_j` (`(σ,x₂)`-pair) | ✓ | ✓ | `h = 1,2,3`; `α = 1,2,3,4`; every `j` |
| `M_α` | `a²[a,b]c^{2^α}` | `c` | `Φ^M_j` | ✓ | ✓ | `h = 1,2,3`; `α = 2,3,4`; every `j` |
| naive candidate (§3) | — | — | `a↦av`, `u↦σu` | ✓ | ✗ (**not even conjugate**) | `h = 1` |

Invertibility: verified for `Φ` at `h=1` by Nielsen reduction with the inverse exhibited (§4.2);
`E_j`, `E'_j`, `Φ^M_j` are composites of `Φ_j` with the transvections of §5.1, hence invertible by
construction.

---

## 5. The frame action, and the 2-adic parameter

### 5.1 The exact transvections, with 2-adic exponents

Four one-line identities give exact automorphisms for **every `k ∈ ℤ₂`** (the exponent is a
`zpowZtwo`, and the identity holds because `y^k` commutes with `y`):

```
τ_σ(k)    : a   ↦ σ^k · a       [σ^k a, σ] = [σ^k,σ]^a [a,σ] = [a,σ]     fixes W ✓
τ_{v_j}(k): u_j ↦ v_j^k · u_j                                            fixes W ✓
τ_{u_j}(k): v_j ↦ u_j^k · v_j                                            fixes W ✓
τ_a(k)    : σ   ↦ a^k · σ                                    does NOT fix W  ✗ (L only)
```

These are MC1's S1 stratum (`[σ, x₂σ^k] = [σ,x₂]^{σ^k}`, MC1 §3.5), needing no axiom. `τ_a` is
unavailable for the L family because `σ` occurs in `W` — which is exactly why the construction of
§4 had to fix `σ`. Frame actions: `ā ↦ ā + kσ̄`; `ū_j ↦ ū_j + kv̄_j`; `v̄_j ↦ v̄_j + kū_j`.
The last two generate `SL₂(ℤ₂)` on each handle plane (elementary matrices generate `SL₂` over a
local ring).

### 5.2 Integer powers × unit rescalings exhaust `ℤ₂`

Put `E_j := τ_{v_j}(1) ∘ τ_σ(1) ∘ Φ_j`, the **pure Eichler element**, with frame action

```
ā ↦ ā − v̄_j ,   ū_j ↦ ū_j − σ̄ ,   σ̄, v̄_j, t, other handles fixed .
```

Its nilpotent part `N` satisfies `N² = 0`, so `E_j^n = 1 + nN` for `n ∈ ℤ`. Now conjugate by
`θ_w := diag(w, w⁻¹)` on `⟨ū_j, v̄_j⟩` — an element of `SL₂(ℤ₂)`, hence a product of the exact
transvections `τ_{u_j}, τ_{v_j}` of §5.1 with 2-adic exponents, for any `w ∈ ℤ₂ˣ`:

```
θ_w E_j θ_w⁻¹  :  ū_j ↦ ū_j − w⁻¹ σ̄ ,   ā ↦ ā − w⁻¹ v̄_j
```

(verified as a matrix identity for `w = 3,5,7,9`). Therefore

```
(θ_w E_j θ_w⁻¹)^n  :  ū_j ↦ ū_j − (n/w)·σ̄ ,   ā ↦ ā − (n/w)·v̄_j ,
```

and `{ n·w⁻¹ : n ∈ ℤ, w ∈ ℤ₂ˣ } = ℤ₂`, because every `x ∈ ℤ₂` is `2^{v(x)} · unit`. **Every 2-adic
coefficient is realized by an exact automorphism**, with the two coefficients automatically equal
(so the mod-2 cup condition `k ≡ k'` of §2 holds identically, for every `k`, not only for `k` odd).

This replaces the compactness argument one would otherwise reach for ("`A(P,h)` is closed because
`Aut(D_P)` is profinite, and `k ↦ 1+kN` is continuous"). That argument is also true, but it would
need `Aut` of a f.g. pro-2 group to be profinite, which is not in mathlib; §5.2 needs nothing
beyond `zpowZtwo` and `SL₂ = E₂` over `ℤ₂`.

### 5.3 The ν-clearing recipe

Write `Σ := ν'(σ̄) ∈ ℤ₂ˣ`. For each handle `j`, in this order:

1. apply `(θ_w E_j θ_w⁻¹)^n` with `n/w = ν'(ū_j)/Σ`  ⟹ `ν'(ū_j) = 0`; the only other value
   touched is `ν'(ā)`, which lies in `P_core`;
2. apply the `E'_j`-analogue with coefficient `ν'(v̄_j)/Σ`  ⟹ `ν'(v̄_j) = 0`; again the only other
   value touched is `ν'(ā)`, since `E'_j` fixes `ū_j` (so step 1 is not undone).

After `2h` steps `ν'|_{P_han} = 0`, and block (a) — the rank-three theorem — finishes on
`P_core`. This is S2.4 §6.4's plan verbatim, with every ingredient now constructed. Note that
the recipe is **stronger** than what S2.4 §6.4 needs: S2.4's single move requires `ν'(ū₁)` to be a
unit (so that `k` is odd), whereas the family of §5.2 handles every `ν'(ū_j) ∈ ℤ₂`.

---

## 6. Scope: the three families, and the two honest residues

### 6.1 The sufficient condition, stated once

> **Proposition (handle mixing).** Let `P = W · [y,z] · ∏_{j<h}[u_j,v_j]` in the free pro-2 group
> on `{letters of W} ∪ {y,z} ∪ {u_j,v_j}`, with `W` a word in letters disjoint from
> `{u_j,v_j}` and from **at least one** of `y, z`. Then for every `j` and every `k ∈ ℤ₂` the
> Eichler unipotents of the symplectic plane pair `(⟨ȳ,z̄⟩, ⟨ū_j,v̄_j⟩)` with parameter `k` are
> induced by continuous automorphisms of the presented pro-2 group `D_P`, constructed explicitly
> and fixing the relator on the nose.

`W` may contain the *other* one of `y,z` freely — that is the content of §4.3, and it is what
makes the type-L prefix `x₀^{σ²}x₀` harmless.

### 6.2 Where each family sits

| family | relator | `[y,z]` | `W`-disjoint letter | status |
|---|---|---|---|---|
| L collector, `L_tw` | `x₀^{σ²}x₀·[x₁,σ]·∏[u_j,v_j]` | `(x₁,σ)` | `x₁` ✓ | **covered** |
| `N_α` | `x₀^{2+2^α}[x₀,x₁]·[σ,x₂]·∏[u_j,v_j]` | `(σ,x₂)` | both ✓✓ | **covered** (full MCG available) |
| `M_α` | `a²[a,b]c^{2^α}·[c,d]·∏[u_j,v_j]` | `(c,d)` | `d` ✓ | **covered** |
| `L_sq` | `(x₀^σ)⁻¹x₀⁻³x₁²·(?)·∏[u_j,v_j]` | see §6.3 | — | **not settled** |

### 6.3 Residue 1 — the `L_sq` word

S2.4 §6.6 records the `L_sq` prefix as `(x₀^σ)⁻¹x₀⁻³x₁²`, and §6.2 records `t = −2x̄₀+x̄₁`,
`ā = x̄₀` for that core — i.e. the frame's hyperbolic plane is `⟨x̄₀, σ̄⟩` while the relator's
commutator factor is `[x₁,σ]`. Two readings are possible and the vendored material does not
decide between them:

* if the relator is `(x₀^σ)⁻¹x₀⁻³x₁²·[x₁,σ]·∏[u_j,v_j]`, the prefix contains **both** `x₁` and
  `σ`, so §6.1's hypothesis fails; moreover `x₁²[x₁,σ] = x₁·x₁^σ`, i.e. the commutator factor can
  be absorbed into the prefix and the surface part is then only `∏_j[u_j,v_j]` (genus `h`, no
  handle-0 plane at all). In that reading the construction of §4 does **not** apply, and the
  handle↔core mixing for `L_sq` needs a different device;
* if instead the `L_sq` core is `Aut(F)`-equivalent, by certified moves, to a word of the shape of
  §6.1 (which the frame data `⟨x̄₀,σ̄⟩ = 1` suggests), then it is covered — but that equivalence
  is exactly the change of variables the simplification campaign owns, not this ticket.

**Decision-relevant:** S2.4 §9 already prices `L_sq` as the expensive candidate (`C_mark = 3`, the
2-adic orientation computation on top of `hMix`). If R2 does not select `L_sq`, this residue costs
nothing. Owner question Q1.

### 6.4 Residue 2 — the M-side unit hypothesis

For L the clearing works because `ν'(σ̄)` is a unit (`ν'` is surjective on `ker χ`, S2.4 §6.4).
For `M_α` the available elements are the ones fixing `c`, so they shift the handle functional by
multiples of `ν'(c̄)` — the clearing therefore needs **`ν'(c̄) ∈ ℤ₂ˣ`** (the exact analogue). If
instead the unit sits on `d̄` and not on `c̄`, the required elements would have to move `c`, which
the `c^{2^α}` factor forbids, and `M` would fall back to the binder. The marked data for `M`
(`(C,I,λ,γ)`; MC1 §2.6, §5.3, and the compact-`M` change of variables that MC1 §7.2 reports as
absent from the vendored sources) is what decides this. **This is a data question, not a proof
question, and it is one line to check once F4/MC5 have the `M` ν-row.** Owner question Q2.

### 6.5 Bonus — MC1's core mixing for `N`

`N_α`'s relator is `x₀^{2+2^α} · ([x₀,x₁]·[σ,x₂]·∏_j[u_j,v_j])`: a **genus-`(2+h)` surface word**
times a power of `x₀`, and `x₀` is the *first* letter of the handle-0 pair. So §6.1 applies with
`[y,z] = [x₀,x₁]` and the `M`-form element, giving an exact automorphism at rank four (`h = 0`!):

```
x₁ ↦ x₀ · x₁ · (x₂⁻¹)^σ            σ ↦ σ · (x₀^{x₁}) · (x₂⁻¹)^σ            (x₀, x₂ fixed)
```

with `Φ(W_N) = W_N`, `Φ(P_N) = P_N`, verified for `α = 1,2,3` and `h = 0,1`. Frame action
`x̄₁ ↦ x̄₁ + t − x̄₂`, `σ̄ ↦ σ̄ + t − x̄₂` (`t = x̄₀`): this is a **core↔core mixing element**, i.e. an
instance of MC1 §5.3's `N5`/`N6` family (the `q`-direction), which MC1 §8 Decision 2 classifies as
S3 and prices at 2–4 k lines of levelwise machinery per core.

Two caveats, stated so this is not over-read: (i) only the `q`-direction is verified; the
`p`-direction (`x̄₁ ↦ x̄₁ + p σ̄`) needs the handle-0 `S`-move conjugate and is **not** checked
here; (ii) the same test on `M_α` **fails** — 24 ansatz forms, all inexact — because `c^{2^α}` sits
*between* `[a,b]` and `[c,d]` and the identity the construction rests on needs the two commutators
adjacent. So: promising for `N`, no evidence for `M`. Follow-up ticket in §7.

---

## 7. Verdict and plan

**Verdict: PROVED at the mathematical level (spike GREEN); PROVABLE-WITH-PLAN in Lean.**

What is proved, precisely: for the L collector/`L_tw`, `N_α` and `M_α` words, the handle↔core
mixing automorphisms that S2.4 §6.4's ν-correction consumes exist, are constructed explicitly,
fix the relator on the nose, are invertible with an explicit inverse, and are available with
arbitrary 2-adic parameters — with **no** new axiom, **no** Labute/levelwise machinery, and no
appeal to compactness of `Aut(D_P)`.

What is **not** proved: `HandleMixLift` as S2.4 §2.4 states it, i.e. a lift for *every* Smith–Witt
stabilizer element. Nothing consumes that, and V5 recommends restating the obligation in the
consumed form.

### Ticket list

| id | content | size | depends on |
|---|---|---|---|
| **HM1** | MC2 additions: `handleWord` splitting lemmas (`∏_{j<h} = ζ_j · [u_j,v_j] · rest`), the two commutator expansion identities `[xz,y]`, `[x,yz]`, and the exact-transvection lemmas `τ_σ(k)`, `τ_{u_j}(k)`, `τ_{v_j}(k)` for `k : ℤ_[2]` via `zpowZtwo` | ~250 ln | MC2 (landed) |
| **HM2** | `Φ_j` as a substitution + `Φ_j(P) = P` (the reduced-word identity of §4.1, `group`-provable once HM1's expansions are available) + the explicit inverse of §4.2 + `thetaEquiv`-pattern assembly into `ContinuousMulEquiv (D_P) (D_P)` | ~350 ln | HM1 |
| **HM3** | frame action of `Φ_j`, `E_j`, `E'_j`; `N² = 0`; `E_j^n = 1 + nN`; the `θ_w`-conjugation identity; the `SL₂ = E₂` over `ℤ₂` step | ~250 ln | HM2 |
| **HM4** | the ν-clearing (§5.3): `∀ ν' with ν'(σ̄) ∈ ℤ₂ˣ, ∃ φ ∈ A(P,h), (ν'∘φ)|_{P_han} = 0`; then the restated obligation `ν_P ∈ ν'·A(P,h)` as a **theorem**, and MC5's `hLift` field split three ways | ~300 ln | HM3, MC5 skeleton |
| **HM5** | the `M`/`N` instantiations (`Φ^M_j`, the `N` variant) — mechanical re-instantiation of HM2/HM3 | ~200 ln | HM2, HM3 |
| **HM6** *(bonus, separate)* | the `N` core-mixing element of §6.5 → does it discharge MC1 §8 Decision 2 for `N`? Check the `p`-direction; if green, `NMixHypothesis` becomes a theorem too | ~1 day spike | independent |

Total for HM1–HM5: **≈900–1400 lines**, entirely within the S1-style toolkit MC2 already has.
Compare MC1 §8's calibration for the levelwise alternative: 2–4 k lines per core with "unknown
risk", or 6–8 k lines per core for the full Decision 1(a) rebuild. The gap is the whole point of
the spike.

### Consequences

* **MC5.** `marked_matching_reduction`'s `hLift` antecedent splits into (S1 ∪ S2 families) +
  `MMixHypothesis` (core, MC1 Decision 2) + handle mixing (now a theorem). MC5 stops being
  conditional on the handle stratum. MC1 §4.2's "MC5's handle stability is **not** a formality" and
  §7.5 risk **R3** are both resolved in the affirmative direction: not a formality, but not a
  binder either.
* **WL / WC.** `marked_L_core_stabilize` and `marked_core_collector_and_twisted` (S2.4 §2.3) lose
  their `hMix` argument; `marked_square_core_stabilize` keeps it pending §6.3. The `1 / 1 / 3`
  column of the page is unaffected — this changes the *residual cost*, not the three-word gap.
* **S2.5 Flip A.** Unaffected: Flip A is about the **word** certificate (S2.4 §1's split, V2
  PROVED) and its soundness condition is `HandlesFresh`, not `HandleMixLift`. Flip A remains
  sound now, and still must add the freshness guard (S2.4 §7.1). Flip B remains **not** sound —
  gate C is about the marked core, and while §4–§5 remove the handle obstruction, the rank-three
  `C_mark` inputs (and, for `L_sq`, §6.3) are untouched by this memo.
* **Packet feedback** (S2.4 §6.5, MC1 §7.3). The packet's remark at `proof.tex:757` —
  "hyperbolic handles can then be added by standard Nielsen moves preserving their commutator
  product" — is still **incomplete as stated** (those moves are block (b), and Corollary 6.3.1
  stands). But the correct statement is now available and is *close* to the packet's: the handles
  are added by moves preserving the commutator product **plus one Dehn-twist-type move per handle
  that mixes it with the core**. That is a constructive amendment, not a gap report, and is much
  more useful to send to the packet's author than the bare finding was.

---

## 8. Method note (reproducibility)

The spike used a purpose-built free-group engine (reduced words as sign-tagged index tuples;
conjugacy by cyclic reduction; invertibility and inverse extraction by Nielsen reduction). The
searches were:

1. exhaustive over all reduced words `A` with `|A| ≤ 6` in `{a,σ,u,v}^{±1}`, solving
   `[A,σ]·[U,v] = [a,σ][u,v]` for `U` by the conjugacy equation `conj(v⁻¹, U) = X v⁻¹` (so `U` is
   unbounded). Result: 12 solutions, of which 11 are the transvection family `A = σ^k a` and
   **exactly one** is mixing — the element of §4.1;
2. targeted, for the `k`-parametrised families, the intervening-block conjugation, the second
   Eichler family, and the `M`/`N` instantiations.

Finding (1) is worth recording: within that radius the mixing solution is **unique**, which is why
the naive ansatz family could not contain it and why the negative result of S2.4 §6.4 was the
expected outcome of looking at short candidates of the wrong shape.

Scratch scripts are not committed (memo-only ticket); every identity in §4–§6 is a finite reduced-word
computation that HM1–HM3 will re-derive in Lean, where `group` plus the two expansion lemmas
discharge them without search.

---

## 9. Open questions for the owner

1. **`L_sq` (§6.3).** Which reading of the `L_sq` relator is correct, and is `L_sq` still a live
   R2 candidate? If R2 selects the collector or `L_tw`, this memo's plan is complete as written;
   if it selects `L_sq`, HM1–HM5 cover the handle block only after a change of variables that the
   simplification campaign owns.
2. **M's ν-row (§6.4).** Is `ν'(c̄)` a unit for the `M_α` marked data? This is the one input
   §5.3's recipe needs on the `M` side, and it interacts with the compact-`M` change of variables
   MC1 §7.2 reports as missing from the vendored sources (MC1 Q4).
3. **Restate or keep? (V5).** Authorise replacing the `HandleMixLift` binder by the consumed
   statement `ν_P ∈ ν'·A(P,h)` and discharging it (HM1–HM5), keeping §1's `def` as the fallback?
   The binder costs nothing to land either way, so this is a scheduling decision, not a risk one.
4. **HM6 (§6.5).** Authorise the one-day follow-up spike on `N`'s *core* mixing? A green result
   would turn MC1 §8 Decision 2 from "(B) binder now" into "(A) proved" for `N` — i.e. it would
   remove one of the two obligations the G-Lab sheet is about, at spike cost.
5. **Packet feedback (§7, MC1 Q5).** Send the constructive amendment (not the bare gap report) to
   the packet's author now?
