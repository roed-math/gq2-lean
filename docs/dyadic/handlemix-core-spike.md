# HM6 — the core↔core mixing spike: MC1 §5.3's S3 stratum, at rank four

**Ticket.** HM6, authorised by the owner from `handlemixlift-spike.md` §7 (ticket table) and Q4:
"the `N` core-mixing element of §6.5 → does it discharge MC1 §8 Decision 2 for `N`? Check the
`p`-direction; if green, `NMixHypothesis` becomes a theorem too". Bounded spike.

**Inputs.** `docs/dyadic/handlemixlift-spike.md` (the HM memo) §4, §5, §6.5, §8; MC1
(`docs/dyadic/mc-design.md`) §2.3–§2.4, §3.3–§3.4, §5.3, §8; the landed HM1–HM5 machinery
(`GQ2/Dyadic/MarkedCore/{Cores,HandleMix,HandleMixEquiv,HandleMixFrame,HandleMixClear,HandleMixInst}.lean`),
in particular `MCoreMixHypothesis`/`NCoreMixHypothesis` (`HandleMixClear.lean:1162,1171`).

**Conventions.** The repo's (`GQ2/Words.lean:56,59`): `x^g = conjP x g = g⁻¹ x g`,
`[x,y] = commP x y = x⁻¹y⁻¹xy`; hence `[xz,y] = [x,y]^z·[z,y]` and `[x,yz] = [x,z]·[x,y]^z`.
Letters are the repo's `Fin (coreRank h)` slots `0,1,2,3` — for `M_α` they are `(A,B,C₀,D)`
and for `N_α` they are `(x₀,x₁,σ,x₂)`; this memo writes both as `(a,b,c,d)`, so

```
mWord α a b c d = a² · [a,b] · c^{2^α} · [c,d]          (Cores.lean:118)
nWord α a b c d = a^{2+2^α} · [a,b] · [c,d]             (Cores.lean:123)
```

---

## 0. Headline verdicts

| # | verdict |
|---|---|
| **W1** | **The `N` side is GREEN, in both directions.** HM's §6.5 `q`-direction is reproduced and extended: both MC1 §3.4 families **N5 and N6** are realized by explicit continuous automorphisms of `D_N` that fix the relator **on the nose**, with explicit two-sided inverses, uniformly in `α` and in the number of handles `h`, **with arbitrary 2-adic parameter**, and with **no new axiom, no B8, no Labute input, no compactness of `Aut`**. Since `{N5, N6}` *is* MC1 §5.3's S3 stratum for `N`, this **discharges `NCoreMixHypothesis`** (§5.1). |
| **W2** | **The `M` side is GREEN too — HM §6.5's negative was an ansatz-shape artifact.** The 24 failed forms were all of the *`N6` shape* (move `b` and `c`), which genuinely cannot survive `c^{2^α}` (§4.3). The family MC1 §5.3 actually needs for `M` is **M5**, which has the *other* shape (move `b` and `d`), and that one goes through untouched: the twisting curve is disjoint from **both** letters that carry the non-commutator factors. Exact, α- and `h`-uniform, 2-adic, axiom-free (§3). This is the same lesson as HM's V2: the obstruction obstructed the candidate, not the lift. |
| **W3** | **One lemma covers everything.** For `P(m,K) = a^m·[a,b]·c^K·[c,d]` and **every** `m, K` the "move `b` and `d`" twist is exact; for `K = 0` the "move `b` and `c`" twist is exact as well. `M_α = P(2, 2^α)` and `N_α = P(2+2^α, 0)`, so M5, N5 and N6 are three instantiations of two general identities (§2). Verified for `m ≤ 18`, `K ≤ 16`, generic `(m,K)`, `h ≤ 3`, `α ≤ 5`, `k ∈ {−6,…,8}`. |
| **W4** | **The 2-adic parameter is free here, unlike the handle case.** Each family is a genuine **one-parameter group** `k ↦ T_k` with `T_k T_l = T_{k+l}`, `T_0 = id`, `T_k⁻¹ = T_{−k}`, given by inserting `γ^k` for a *fixed* word `γ` that the family fixes. So `k ∈ ℤ₂` is `zpowZtwo` verbatim (HM1's landed pattern) — **no `θ_w` conjugation, no `SL₂ = E₂`, no B8** (§3.4). |
| **W5** | **The `M` residue is characterised exactly, and it is not what HM guessed.** The three families the twist construction does *not* reach — **M4 (`β`), M6 (`c₁`), M7 (`d₁`)** — are precisely the ones that are **not symplectic over `ℤ₂`**; they satisfy only the mod-2 Witt condition (§4.2). No word-level twist can reach them, because every relator-preserving automorphism of a surface-type word lands in `Sp₄`. This is a structural statement, not a search result, and it is a *sharper* obstruction than the `c^{2^α}` adjacency story. |
| **W6** | **Verdict: `N` = PROVED; `M` = PROVED for the family MC5 consumes, GENUINELY-OPEN for the three non-symplectic families.** `NCoreMixHypothesis` is discharged; `MCoreMixHypothesis` is **weakened**, not discharged — with the residual stated exactly (§5.2). MC5's `ν`-correction on the `M` side needs only M5 (MC1 §5.3's own reading), so **MC5 is unaffected by the residue** given the unit hypothesis that `isUnit_nuM_dmC` already proves for the standard marking. |
| **W7** | **Lean: LANDED, 732 lines, `GQ2/Dyadic/MarkedCore/CoreMix.lean`.** All three automorphisms are in the repo as `ContinuousMulEquiv`s at arbitrary 2-adic parameter, relator-exact, with the `−k` member as a two-sided inverse in the free group. Zero sorries, `check_dyadic.sh` green, census 11, every declaration prints **std-3**. §6 records what remains (the `nuFrame` rows and the `A(P,h)` widening) and why. |

---

## 1. What the binder is, and what discharging it means

`HandleMixClear.lean:1162,1171` state the two obligations schematically over a set `S3` of frame
moves:

```lean
def MCoreMixHypothesis (α h : ℕ) (S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))) : Prop :=
  DmRealizesAll α h S3            -- ∀ F ∈ S3, ∃ Ψ : ContinuousMulEquiv (DM α h) (DM α h), DmRealizes α h Ψ F
def NCoreMixHypothesis (α h : ℕ) (S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))) : Prop :=
  DnRealizesAll α h S3
```

`S3` is a parameter because MC3/MC4 own the concrete stratum sets. MC1 §5.3 fixes them:

* **`N`**: `S3_N = ⟨N5, N6⟩` — the `p`- and `q`-directions of MC1 §3.4.
* **`M`**: `S3_M = ⟨M4, M5, M6, M7⟩` — `β`, the free part of `B_c`, `c₁`, `d₁` of MC1 §2.4.

So "discharging the binder" means: exhibit, for every generator of that stratum and every 2-adic
parameter, a continuous automorphism of the presented core inducing it on the frame. That is what
§3 does — completely for `N`, and for the M5 generator only on the `M` side.

---

## 2. The construction: two twist identities, and why they are one line each

### 2.1 The general relator shape

Both rank-four cores are instances of

```
P(m, K)  =  a^m · [a,b] · c^K · [c,d]          M_α = P(2, 2^α) ,   N_α = P(2+2^α, 0)
```

and the handle block `∏_{j<h}[u_j,v_j]` is appended on the right and is never touched by anything
below, so every statement is `h`-uniform for free.

### 2.2 The "move `b` and `d`" twist (M5 / N5 shape) — works for **every** `m, K`

```
ρ       :=  a^{-(m-1)} · P(m,K) · c^{-K}                    (class ā)
γ_b     :=  ρ · c                                           (class ā + c̄)
γ_d     :=  (γ_b)^{c^{K-1}}                                 (a conjugate of γ_b)

T_k :  a ↦ a ,  c ↦ c ,  b ↦ b·γ_b^k ,  d ↦ d·γ_d^k ,  handles fixed
```

Unwinding `ρ`, this is `ρ = a^b · [c,d]^{c^{-K}}`, i.e. `γ_b = a^b·[c,d]^{c^{-K}}·c`. At `K = 0`
(the `N` case) it is simply `γ_b = a^b·[c,d]·c` and `γ_d = c·a^b·[c,d]`.

> **Identity.** `P(m,K)(a, b·γ_b^k, c, d·γ_d^k) = P(m,K)(a,b,c,d)` for every `k`.

**Proof in one line.** Write `g := γ_d^k`, so `γ_b^k = g^{c^{K-1}}`. Everything reduces to the
observation that `γ_b = ρ·c` and `γ_d = c^{1-K}·ρ·c^{K}` are conjugate by `ρ` up to the central
`c`-power, i.e. conjugation by `ρ` carries `γ_d` to `γ_b`. Concretely, at `K = 0`:
`aS = a·[a,b][c,d] = a^b·[c,d] = ρ`, `γ_b = ρc`, `γ_d = cρ`, and
`(ρ)γ_d(ρ)⁻¹ = ρ·c·ρ·ρ⁻¹ = ρc = γ_b`. In Lean this is `simp only [commP, conjP]; group` after the
definitions are unfolded — no case split on `k`, no expansion lemmas.

**Two letters are fixed, and they are exactly the right two.** `T_k` fixes `a` and `c` *as
letters*. `a` is the letter of the prefix `a^m`, `c` the letter of the interior factor `c^K`. So
both non-commutator factors survive **literally**, whatever `m` and `K` are. This is the whole
point, and it is why the `c^{2^α}` factor is harmless for this shape.

Geometrically: `T_k` is (a product of three Dehn twists whose net effect is) the twist along a
simple closed curve `γ` in the class `ā + c̄`, and `⟨ā+c̄, ā⟩ = ⟨ā+c̄, c̄⟩ = 0`, so `γ` can be
band-summed off both `α_a` and `α_c`. A twist supported away from two loops fixes them.

### 2.3 The "move `b` and `c`" twist (N6 shape) — works **iff `K = 0`**

```
δ   :=  a^{-(m-1)} · P(m,0) · d^{-1}   =   a^b · (d^{-1})^c            (class ā − d̄)

T'_k :  a ↦ a ,  d ↦ d ,  b ↦ b·δ^k ,  c ↦ c·δ^k ,  handles fixed
```

> **Identity.** `[a, b·g]·[c·g, d] = a⁻¹·g⁻¹·(a^b·(d⁻¹)^c)·g·d` for **arbitrary** `g`.

That single identity is the whole proof: it is `simp only [commP, conjP]; group`, and then
`a⁻¹·δ·d = [a,b]·[c,d]` (another `group`), so taking `g = δ^k` and using `Commute (δ^k) δ` gives
`[a,b·δ^k]·[c·δ^k,d] = [a,b]·[c,d]`. Note the sandwich cancels for *any* `g` commuting with `δ`,
which is exactly why the parameter can be 2-adic.

This is HM §6.5's element: at `k = 1` it is `b ↦ a·b·(d⁻¹)^c`, `c ↦ c·(a^b)·(d⁻¹)^c`, byte-identical
to the memo's display, and it is `handleMixD`/`handleMixU` (`HandleMixEquiv.lean:166,169`) at
`z = 1` with the core pair `(a,b)` in the `(c,d)`-slot and `(c,d)` in the `(u,v)`-slot.

**Why `K ≠ 0` kills it.** `T'_k` moves the letter `c`, and `c` carries the interior factor `c^K`.
For `M_α` the image is not `P_M`, not conjugate to `P_M`, and the length blows up
(`|Φ(P)| = 26, 52, 128` against `|P| = 8, 10, 14` for `α = 1,2,3`). This is HM §6.5's caveat (ii),
confirmed — but see §4.3: it is a statement about *this shape only*.

### 2.4 Verification table

All rows are exact reduced-word identities in the free group, checked by an independent word engine
(reduced words as sign-tagged index tuples; conjugacy by cyclic reduction; invertibility by Nielsen
reduction with expression tracking, which also produced the inverses).

| family | word shape | core | `T_k(P) = P` | range checked |
|---|---|---|---|---|
| **N6** (`q`) | move `b`, `c` (§2.3) | `N_α` | ✓ | `α = 1..5`, `h = 0..3`, `k ∈ {−6,−3,−1,0,1,2,3,5,8}` (180/180) |
| **N5** (`p`) | move `b`, `d` (§2.2) | `N_α` | ✓ | same (180/180) |
| **M5** (`B_c`) | move `b`, `d` (§2.2) | `M_α` | ✓ | same (180/180) |
| generic | move `b`, `d` | `P(m,K)` | ✓ | `(m,K)` ∈ {(2,0),(2,2),(2,4),(2,8),(2,16),(4,0),(6,0),(10,0),(18,0),(3,5),(5,3)} |
| N6 shape on `M_α` | move `b`, `c` | `M_α` | ✗ (**not even conjugate**) | `α = 1,2,3` |

One-parameter-group law `T_k∘T_l = T_{k+l}`, `T_0 = id`, `T_k⁻¹ = T_{−k}`, and `T_k(γ) = γ`:
verified for all `k, l` in the range, both cores.

---

## 3. The frame action, the 2-adic parameter, and the reduction to MC1's families

### 3.1 Frame actions of the twists

Abelianising (every `conjP` collapses):

```
T_k   (move b,d) :   b̄ ↦ b̄ + k(ā + c̄) ,   d̄ ↦ d̄ + k(ā + c̄) ,   ā, c̄, handles fixed
T'_k  (move b,c) :   b̄ ↦ b̄ + k(ā − d̄) ,   c̄ ↦ c̄ + k(ā − d̄) ,   ā, d̄, handles fixed
```

Both nilpotent parts land in `⟨ā, c̄⟩` resp. `⟨ā, d̄⟩`, where they vanish, so `N² = 0` — the same
shape HM3 already formalises for the handle case (`frameNilpU`, `HandleMixFrame.lean:637`).

### 3.2 Isolating MC1's pure families

The twists carry S1 shears along; MC1's families are recovered by composing with the elementary
Nielsen lifts, all of which are **exact** on the rank-four cores (one-line commutator identities,
axiom-free, and available with 2-adic exponents):

```
τ_a(k) : b ↦ a^k·b     [a, a^k b] = [a,b]·[a,a^k]^b = [a,b]        (MC1 M1 / N1)
τ_c(k) : d ↦ c^k·d     [c, c^k d] = [c,d]·[c,c^k]^d = [c,d]        (MC1 M2 / N2)
τ_d(k) : c ↦ d^k·c     [d^k c, d] = [d^k,d]^c·[c,d] = [c,d]        (MC1 N3; N only — it moves c)
```

Exactness verified for `α ≤ 4`, `h ≤ 2`, `k ∈ {−3,−1,1,2,5}` (60/60 each). Then

```
pure N6(q)  =  τ_a(−q) ∘ τ_d(q) ∘ T'_q          frame:  b̄ ↦ b̄ − q·d̄ ,  c̄ ↦ c̄ + q·ā ,  d̄ fixed
pure N5(p)  =  τ_a(−p) ∘ τ_c(−p) ∘ T_p          frame:  b̄ ↦ b̄ + p·c̄ ,  d̄ ↦ d̄ + p·ā ,  c̄ fixed
pure M5(B_c)=  τ_a(−B_c) ∘ τ_c(−B_c) ∘ T_{B_c}  frame:  b̄ ↦ b̄ + B_c·c̄ , d̄ ↦ d̄ + B_c·ā , c̄ fixed
```

each verified exact on the real relator (`α = 3`, `h = 2`, parameters `1,2,3,5`). The coupled
`t`-shifts MC1's tables record (`σ ↦ x₀^q σ` for N6, `D ↦ t^{B_c}D` for M5) come out **automatically**:
`t = ā` for `N` and `t = Ā + mC̄₀` for `M` is 2-torsion in the frame, so `q·ā = (q mod 2)·t`, and
MC1 §2.3's coupling ("the `C̄₀`-component of `φ(B̄)` ≡ the `t`-component of `φ(D̄)` mod 2") holds
identically, for every parameter, not only for odd ones.

`τ_d` is **not** available on `M` (it moves `c`, which carries `c^{2^α}`), which is why `M` has no
`S`-move on the `(C̄₀, D̄)` plane. That is not a loss: MC1 §2.3 shows `St_M` has **no** `SL₂` there
either (`φ(C̄₀)` is forbidden a `D̄`-component, because `χ̄(D̄) = u` has infinite order). Tool and
target disappear together.

### 3.3 The character conditions hold, and this is the M/N asymmetry's real cause

`χ_M = (1,−1,1,u)` and `χ_N = (1,v,1,1)` (MC1 §2.2(i), §3.2(i)). Checking `χ̄∘φ = χ̄`:

* `M5`: `χ(φ(B)) = χ(B)χ(C₀) = −1` ✓; `χ(φ(D)) = χ(D)χ(A) = u` ✓.
* `N5`, `N6`: every letter moved is χ-trivial or picks up χ-trivial factors ✓.
* the **`N6`-shaped element on `M`** would need `φ(C̄₀) = C̄₀ + Ā − D̄`, giving `χ = u⁻¹ ≠ 1` ✗.

So the `N6` shape is excluded on the `M` side twice over — by `c^{2^α}` at the word level and by
`χ(D) = u` at the frame level. It was never a candidate.

### 3.4 Arbitrary 2-adic parameters, for free

Each family is `T_k(x) = x·γ^k` on two letters, with **`γ` fixed by the family**
(`T_k(γ_b) = γ_b`, `T_k(γ_d) = γ_d`, `T'_k(δ) = δ`; verified for all tested `k`). Hence

```
T_k ∘ T_l = T_{k+l} ,     T_0 = id ,     T_k⁻¹ = T_{−k}
```

and the only thing needed for `k ∈ ℤ₂` is that `γ^k` makes sense and commutes with `γ` — which is
`zpowZtwo` plus `Commute.zpowZtwo_self`, exactly HM1's landed pattern for the handle transvections
(HM memo §5.1). **This is strictly cheaper than the handle case**, which needed the `θ_w`
conjugation and `SL₂(ℤ₂) = E₂(ℤ₂)` (HM memo §5.2) to reach general 2-adic coefficients. Here the
word itself is `k`-parametrised.

Consequence worth stating plainly: **no B8, no compactness of `Aut(D_P)`, no Labute/levelwise
input, and no new axiom.** Census stays at 11.

### 3.5 Explicit inverses

Nielsen reduction of each image tuple terminates at a basis, and back-substitution gives the
inverse in closed form. For the two generators (at `k = 1`, `K = 0`, the `N` normalisation):

```
T'  :  b ↦ a·b·(d⁻¹)^c                 T'⁻¹ :  b ↦ b·(d⁻¹)^c·(a⁻¹)^b  … = b·δ⁻¹
       c ↦ c·(a^b)·(d⁻¹)^c                     c ↦ c·δ⁻¹
T   :  b ↦ b·(a^b·[c,d]·c)                T⁻¹ :  b ↦ b·γ_b⁻¹
       d ↦ d·(c·a^b·[c,d])                      d ↦ d·γ_d⁻¹
```

i.e. the inverse is the `k = −1` member, on the nose, and both composites are the identity **in the
free group**, not merely modulo `⟨⟨P⟩⟩`. That is what HM2's `thetaEquiv`-pattern assembly wants
(HM memo §4.2), and it is why the Lean cost in §6 is low.

---

## 4. The `M` residue, characterised

### 4.1 What is left

MC1 §2.4's S3 list for `M` is `{M4 (β), M5 (B_c), M6 (c₁), M7 (d₁)}`. §3 proves **M5**. The
other three are **not** reached, and not by accident.

### 4.2 The exact obstruction: they are not symplectic

Give `ℤ₂⁴ = ⟨ā,b̄,c̄,d̄⟩` the symplectic form `⟨ā,b̄⟩ = ⟨c̄,d̄⟩ = 1`, all other pairings `0` — the
form the relator's commutator part carries. Then, computed directly:

| family | frame action | symplectic over `ℤ₂`? |
|---|---|---|
| **M5** (`B_c`) | `b̄ ↦ b̄ + B_c c̄`, `d̄ ↦ d̄ + B_c ā` | **yes** |
| **N5** (`p`) | `b̄ ↦ b̄ + p σ̄`, `x̄₂ ↦ x̄₂ + p x̄₀` | **yes** |
| **N6** (`q`) | `b̄ ↦ b̄ − q x̄₂`, `σ̄ ↦ σ̄ + q x̄₀` | **yes** |
| **M4** (`β`) | `B̄ ↦ β B̄` | no — `⟨φĀ,φB̄⟩ = β ≠ 1` |
| **M6** (`c₁`) | `C̄₀ ↦ C̄₀ + 2c₁ B̄` | no — `⟨φĀ,φC̄₀⟩ = 2c₁ ≠ 0` |
| **M7** (`d₁`) | `D̄ ↦ D̄ + 2d₁ B̄` | no — `⟨φĀ,φD̄⟩ = 2d₁ ≠ 0` |
| **M3/N4** (`γ`) | `C̄₀ ↦ γ C̄₀` | no (this is S2 = B8, already handled) |

`St_M`'s Witt condition is only **mod 2** (`φ̄ ∈ O(G_M)`, `G_M` over `𝔽₂`), so `St_M` genuinely
contains these non-symplectic elements — the factor `2` in `2c₁`, `2d₁` is precisely the mod-2
Witt condition being satisfied while the integral form is not.

> **The characterisation.** Any automorphism of the free group preserving a relator whose
> commutator part is a surface word induces a **symplectic** map on `H₁`. The twist construction
> therefore reaches exactly `S3 ∩ Sp₄`, which is all of `S3_N` and exactly the `M5` generator of
> `S3_M`. **`M4`, `M6`, `M7` are outside the reach of *any* relator-fixing word automorphism**,
> not merely outside this ansatz.

This upgrades HM §6.5's "24 ansatz forms failed" from a search result to a theorem-shaped
statement, and it relocates the obstruction: it is **not** `c^{2^α}` (§4.3), it is the failure of
integral symplecticity.

### 4.3 Correction to HM §6.5's caveat (ii)

HM §6.5 reports: "the same test on `M_α` **fails** — 24 ansatz forms, all inexact — because
`c^{2^α}` sits *between* `[a,b]` and `[c,d]` and the identity the construction rests on needs the
two commutators adjacent. So: promising for `N`, no evidence for `M`."

Both halves need amending.

* The **diagnosis is right for the shape that was tried**: the `N6` shape (move `b` and `c`) does
  need adjacency, does move the letter `c`, and does die on `c^{2^α}` — §2.3 and the last row of
  §2.4 reconfirm it, including non-conjugacy.
* The **conclusion is wrong**: the family `M` needs is not the `N6` shape. MC1 §5.3's own reading —
  "`M`: … needs `β` (M4) or the free part of `B_c` (M5)" — points at **M5**, whose shape moves `b`
  and `d` and fixes `c`. That shape never touches `c^{2^α}`, and it is exact (§2.2). The
  adjacency requirement is a property of the *other* family.
* Structurally: `a²` and `c^{2^α}` sit on the letters `a` and `c`, and the M5 twist fixes **both**.
  The curve it twists along has class `ā + c̄`, which pairs to zero with both `ā` and `c̄`.

This is HM's own **V2** lesson repeated one level down: the obstruction obstructed the candidate,
not the lift. Worth flagging when the packet feedback of HM §7 goes out.

### 4.4 Is the residue needed?

* **For MC5's `ν`-correction: no.** MC1 §5.3 states the requirement as
  `(ν'∘φ)(B̄) = β·ν'(B̄) + B_c·ν'(C̄₀) = ε2^{r−1}`, solvable with `β = 1` and
  `B_c = (ε2^{r−1} − ν'(B̄))/ν'(C̄₀)` whenever `ν'(C̄₀) ∈ ℤ₂ˣ` — and §3.4 supplies exactly that
  `B_c ∈ ℤ₂`. The unit hypothesis is HM memo §6.4's residue 2, already a theorem for the standard
  marking (`isUnit_nuM_dmC`, `HandleMixClear.lean:1066`) and a data question for the transported
  `ν'` (HM Q2, still open — see §7).
* **For `hLift` as literally quantified (`∀ φ ∈ St_M`): yes.** The completeness argument of
  MC1 §2.4 multiplies successively by `Σ_γ, Σ_β, Y_c, Z_d, X_b, Λ_k, E_e`; without M4/M6/M7 the
  residue is not the identity. So `MCoreMixHypothesis` stays as a binder with a *smaller* content.

---

## 5. G-Lab consequence, per binder

### 5.1 `NCoreMixHypothesis` — **DISCHARGED** (mathematically; one mechanical Lean step left)

`S3_N = ⟨N5, N6⟩` and both are theorems, for every `α`, every `h`, and every 2-adic parameter. The
automorphisms are landed (`dnCoreMixPEquiv`, `dnCoreMixQEquiv`, §6.1); what remains between them
and the literal binder is HM6e/HM6f of §6.2 — the ν-frame rows and the `A(P,h)` widening, both
mechanical. MC1 §8 **Decision 2 moves from "(B) binder now" to "(A) proved" for `N`** — at spike
cost, not at the 2–4 k-line levelwise cost the sheet prices. `NLiftSplit` then loses a field: with
`nLiftSplit_handle` (HM5, landed) and this, only `NNielsenScalingHypothesis` (S1 ∪ S2, of which S1
is axiom-free and S2 is B8) remains, and MC4's own S1 lemmas discharge most of that too.

### 5.2 `MCoreMixHypothesis` — **WEAKENED**, residual stated exactly

Split `S3_M = ⟨M5⟩ ⊔ ⟨M4, M6, M7⟩`. The first factor is a theorem (`dmCoreMixEquiv`, §6.1, plus
HM6e/HM6f). The residual binder is `MCoreMixHypothesis α h ⟨M4, M6, M7⟩` — **the non-symplectic
directions**.
Two things travel with it:

1. it is **not consumed by MC5's `ν`-correction** (§4.4), so MC5 can be stated against the M5
   instance alone and stays unconditional in the S3 direction;
2. it is **not reachable by any relator-preserving word automorphism** (§4.2), so the levelwise /
   graded-Lie route of MC1 §8 Decision 2(A) is the only route to it — the spike does **not**
   reduce its price, and it should keep the "unknown risk" label. If MC3 restates `hLift` in the
   consumed form (the analogue of HM's V5), the residue disappears from the consumers entirely.

### 5.3 Census, axioms, print

`def`-shaped hypotheses are invisible to `AxiomLedger`; the new theorems use no axiom beyond the
standard three. **Census stays at 11.** No B8 dependency is added by this memo (contrast MC1 §5.2,
where S2 needs it).

---

## 6. Lean: what landed, and what remains

### 6.1 Landed — `GQ2/Dyadic/MarkedCore/CoreMix.lean` (732 lines, 0 sorries, std-3)

The construction re-uses HM2's assembly shape (`dmMixEquiv`/`dnMixEquiv`,
`HandleMixEquiv.lean:688,780`) with a different marking update: HM2 updates core slot `3` and a
handle slot; HM6 updates two **core** slots (`1,3` for the M5/N5 shape, `1,2` for N6). The handle
block is therefore never touched, and every statement is `h`-uniform for free.

| § | content |
|---|---|
| **§1** | `hm6MixBD`, `hm6MixBC` and the two relator identities `hm6_relator_mixBD`, `hm6_relator_mixBC` — stated for an **arbitrary** inserted `g` commuting with the twisting curve, with **no hypothesis** on the prefix `w` or the interior factor `z`. Proof: one `Commute` cancellation plus `simp only [commP, conjP]; group`. Naturality and abelian collapse alongside; `hm6Mix*_mix*` are the "curve fixed by its own family" lemmas. |
| **§2** | the three `zpowZtwo` families — `hm6CurveM` (M5), `hm6CurveNp` (N5), `hm6CurveNq` (N6) — with `hm6_mWord_curveM`, `hm6_nWord_curveNp`, `hm6_nWord_curveNq` at arbitrary `k : ℤ_[2]`, and the one-parameter-group laws. |
| **§3** | `hm6UpdateBD`/`hm6UpdateBC` (two-slot core updates, with the six value lemmas each) and the three markings, giving `mRelWord_hm6MarkM`, `nRelWord_hm6MarkNp`, `nRelWord_hm6MarkNq` — **`Φ(P) = P` on the full relator, handles included**. Inverses (`hm6Mark*_neg`, `hm6Mark*_neg'`) and naturality. |
| **§4** | `dmCoreMixEquiv α h k`, `dnCoreMixPEquiv α h k`, `dnCoreMixQEquiv α h k` : `ContinuousMulEquiv` on the presented cores, with the generator rows recording which letters are fixed. |

Gates: `bash scripts/check_dyadic.sh` green (census 11, zero sorries, all axioms in place);
`lake build GQ2.Dyadic.MarkedCore.CoreMix` green; `#print axioms` on all eleven headline
declarations gives `[propext, Classical.choice, Quot.sound]` — **no `sorryAx`, no campaign axiom,
no B8**.

**Not** added to `GQ2.lean`: MC3/MC4 are editing that file in parallel and HM6 does not own it, so
the one-line `import GQ2.Dyadic.MarkedCore.CoreMix` is the integrator's. Until it is added the
module is outside the default `lake build` target (it is built explicitly, as above).

### 6.2 Remaining — the two steps to the binder itself

| id | content | size |
|---|---|---|
| **HM6e** | the `nuFrame` rows: `nuFrame f (fun i => dnCoreMixQEquiv α h k (dnGen α h i)) = F (nuFrame f (dnGen α h))` for the three families, with `F` the frame endomorphisms of §3.1. This is HM3's `nuFrame_tau_*` pattern (`HandleMixClear.lean:869 ff.`) re-run on two core slots; the abelian-collapse lemmas §1 already lands are the input. | ~200 ln |
| **HM6f** | widen `dmClearAuts`/`dnClearAuts` (`HandleMixClear.lean:836,843`) by the three new generator families, re-prove the four landed handle rows against the widened set (`Submonoid.closure` is monotone, so this is `Submonoid.closure_mono` plus reindexing the four `Set.mem_union` witnesses), and conclude `NCoreMixHypothesis α h ⟨N5,N6⟩` and `MCoreMixHypothesis α h ⟨M5⟩`. **This edits a file HM6 does not own**; it is a small, mechanical, owner-schedulable change. | ~150 ln |

The reason HM6f is needed at all is worth recording: `DmRealizes`/`DnRealizes`
(`HandleMixClear.lean:854,861`) bundle "acts as `F` on the ν-frame" **with** "lies in
`Submonoid.closure (d?ClearAuts α h)`", and `d?ClearAuts` is the *handle* generating set. That was
the right packaging for HM4/HM5, whose whole point was that the clearing correction stays inside
`A(P,h)`; it is too narrow for the core stratum, where the realizing automorphism is by
construction a new generator. Either widen the set (HM6f) or split the two conjuncts. **Flagging
this is itself a deliverable of the spike** — MC3/MC4 would have hit it.

**Ordering note.** MC3/MC4 are editing `M.lean`/`N.lean` in the same namespace in parallel;
`CoreMix.lean` is a fresh file and touches nothing they own. The frame-move sets are HM6's own
definitions; when MC3/MC4 pin down `S3`, the two should be shown equal (a one-line `Set`
extensionality, MC3/MC4's to write).

---

## 7. Owner questions

1. **Schedule HM6e/HM6f (§6.2)?** The three automorphisms are landed and axiom-clean; the two
   remaining steps are the ν-frame rows (~200 ln, in `CoreMix.lean`, HM6 could own it) and the
   `A(P,h)` widening (~150 ln, in `HandleMixClear.lean`, which HM6 does **not** own — see §6.2 for
   why the landed `DnRealizes` packaging is too narrow for the core stratum). Also: the one-line
   `import GQ2.Dyadic.MarkedCore.CoreMix` in `GQ2.lean`, deliberately not made here because MC3/MC4
   are editing that file.
2. **Restate `hLift` for `M`?** §5.2(2): if MC3 states the `M` obligation in the form MC5 actually
   consumes (M5 + S1 + S2, not `∀ φ ∈ St_M`), then `MCoreMixHypothesis` disappears as well and the
   `M` lane has no S3 residue at all. This is the exact analogue of HM's V5, which the owner has
   already seen; it is a scoping decision, not a mathematical one.
3. **HM Q2 is now the binding question on the `M` side.** With M5 proved, the *only* input MC5's
   `M` row still needs is `ν'(C̄₀) ∈ ℤ₂ˣ` for the transported `ν'`. That is HM memo §6.4 /
   MC1 Q4's compact-`M` change of variables, still reported absent from the vendored sources.
4. **Packet feedback.** §4.3 corrects a claim this campaign itself made one ticket ago. If the HM
   §7 amendment is sent, this should go with it: the M-side twist exists, and the earlier negative
   was a shape artifact.
5. **M4/M6/M7 (§4.2).** Record the non-symplecticity finding as the standing obstruction for the
   `M` residue and keep MC1 §8 Decision 2(A)'s price unchanged for it? The spike gives no reduction
   there, and it now has a reason rather than a failed search.

---

## 8. Method note (reproducibility)

Same engine as the HM spike (reduced words as sign-tagged index tuples; conjugacy by cyclic
reduction), extended with (i) substitution/composition on markings, (ii) Nielsen reduction with
expression tracking, which extracts inverses rather than merely certifying that they exist, and
(iii) the conjugacy-equation solver of HM §8: given images of `a, b, c`, solve `[c', d'] = T` for
`d'` by `conj(c', d') = c'·T`, so `d'` is unbounded and only the *other* images need enumerating.

The search that found the `M` element was that solver over all reduced `w` with `|w| ≤ 5` in
`b ↦ b·w`, `a` and `c` fixed, against the surface word `[a,b][c,d]`. It returns **8** solutions, of
which 7 are the `τ_a` family and **exactly one** is mixing — the element of §2.2. As in HM §8, the
mixing solution is *unique* within the radius; the reason the earlier pass missed it is that it
enumerated the wrong pair of moved letters, not that it looked too narrowly.

A wider sweep (1 459 200 candidates: `a` fixed, `b ↦ b·w` with `|w| ≤ 4`, `c ↦ c·v` with `|v| ≤ 3`,
`d` solved, tested against the **full** `M_α` relator with α-uniformity check) returned only the
`τ_a` family. That sweep's radius does **not** contain the §2.2 element (`|γ_b| = 6` already at
`α = 1`), so it is **not** evidence about M4/M6/M7; §4.2's symplectic argument is, and it is
independent of any search.

Scratch scripts are not committed (memo ticket); every identity in §2–§4 is a finite reduced-word
computation that HM6a–HM6c re-derives in Lean, where `group` discharges it without search.
