# MC-VAR — adjudication of the cup-isometry variance between MC3 (`M.lean`) and MC4 (`N.lean`)

**Ticket.** MC-VAR, dispatched by the orchestrator after MC3 and MC4 each reported that the
*other* ticket's cup-isometry variance destroys a family it needs. MC5 consumes both, so the
question had to be settled from first principles before anything downstream moves. Worked alone
in `~/claude/gq2-dyadic-mc` on branch `dyadic-mcvar`.

**Inputs.** `GQ2/Dyadic/MarkedCore/M.lean` (MC3) §4; `GQ2/Dyadic/MarkedCore/N.lean` (MC4) §4;
the cup semantics in `GQ2/Dyadic/MarkedCore/Cores.lean` §6 (`IsCupCocycle`, `mWord_centLift_fib`,
`nWord_centLift_fib`, `mRelWord_centLift_fib`); the rank-three precedent
`GQ2/Dyadic/SqCore/Rank3.lean` (`sqCore_cupGram`) and `GQ2/Roe/DRDemushkin.lean` (`drCup_*`);
MC1 (`docs/dyadic/mc-design.md`) §2.2–§2.4, §3.2–§3.4.

**Deliverables.** This memo, plus `GQ2/Dyadic/MarkedCore/Variance.lean` (0 sorries, std-3,
census 11, `check_dyadic.sh` green, `lake build GQ2` green). **No edit to `M.lean` or `N.lean`.**

---

## 0. Verdict

> **(a) DUAL ENCODINGS — both files are correct, and their two clauses are literally the same
> equation.** There is no variance disagreement. `M.lean` stores a frame endomorphism with its
> **images in the rows**; `N.lean` stores it with its **images in the columns**; the two matrices
> are transposes of each other, and each file pairs its own layout with the transpose that makes
> `A·G·Aᵀ = G` come out. Nothing needs repairing in either file's mathematics.

Supporting verdicts:

| # | verdict |
|---|---|
| **V1** | The condition "`ξ` preserves the mod-2 cup form", derived from the repo's own cup semantics, is `A·G·Aᵀ = G` where `A` is the **column-layout** matrix of `ξ` on `H₁` (equivalently `M̄ᵀ·G·M̄ = G` for the row-layout `M̄ = Aᵀ`). This is `N.lean`'s clause verbatim on `NRows.mat`, and `M.lean`'s clause verbatim on `mFrameMatrix`. |
| **V2** | **The ticket's premise was wrong on one point**: `nMatOf`'s **columns**, not its rows, hold the images. `NRows.mat R i j = nMod2 (R.col j) i` — see §2. That single misreading is the whole of the apparent conflict. |
| **V3** | **MC3's counterexample claim is TRUE** in MC3's layout (Lean: `mFrameMatrix_flip_forces_tau`), and **MC4's counterexample claim is TRUE** in MC4's layout (Lean: `nMatOf_transpose_cup_forces_tau`). Translated into the other layout, each becomes the other, verbatim: they are one counterexample, stated twice. |
| **V4** | The two variances are nonetheless genuinely different *conditions* — `G⁻¹ ≠ G` — so the layout has to be **recorded**, not guessed. Lean-checked witness: `nMatOf_famN1_variance_differs`. |
| **V5** | The crown-jewel cross-check: at a classified `M`-parameter, `(mFrameMatrix B ξ)ᵀ` is **literally an `N.lean` `nMatOf`** (Lean: `mFrameMatrix_transpose_eq_nMatOf`), with `M`-parameters mapping onto `N`-parameters. The two tickets classified transposed pictures of the same `𝔽₂` object. |
| **V6** | The only defect is **prose**: each file's variance note says "the transpose side" / "the row side" relative to its own `M̄`, without naming its layout, so the two notes read as contradicting each other. Docs-only follow-up, deliberately **not** applied here (see §6). |

---

## 1. What the cup form eats, from the repo's own semantics

The question "which matrix equation says `ξ` preserves the cup form" only has an answer once one
knows what the Gram is a Gram *of*. `Cores.lean` fixes it, and it is not a matter of taste.

A cup cocycle is, by `Cores.lean:1333–1336`, one of the shape `κ(a, b) = ⟨v, a⟩·⟨w, b⟩` for
**covectors** `v, w`. MC2's Gram computations then evaluate the relator in the corresponding
central extension:

```
mRelWord_centLift_fib   (Cores.lean:1435)
nRelWord_centLift_fib   (Cores.lean:1455)
   fib = κ(m₀,m₀) + (κ(m₀,m₁) + κ(m₁,m₀)) + (κ(m₂,m₃) + κ(m₃,m₂)) + Σ_handles
```

With `κ(a,b) = ⟨v,a⟩⟨w,b⟩` and `m_i` the mod-2 generator basis, `⟨v, m_i⟩ = v_i`, so

```
fib = v₀w₀ + v₀w₁ + v₁w₀ + v₂w₃ + v₃w₂   (+ handles)
```

which is **exactly** `N.lean`'s `nCupForm v w` (`N.lean:849`). So:

* `nCupForm` takes two **`H¹` covectors in the dual basis** and returns their cup pairing;
* `nGram i j = nCupForm δᵢ δⱼ = ⟨xᵢ*, xⱼ*⟩` is the Gram **in the dual basis** — as
  `Rank3.lean:209` already says for `sqCore_cupGram` ("in the dual basis `(σ*, x₀*, x₁*)` of
  `H¹(D_sq, 𝔽₂)`"), and as `N.lean:841` says for `nGram`;
* `nCupForm_eq_gram` (`N.lean:854`) certifies that the closed form is that Gram's bilinear form.
  This is a *theorem in the repo*, so the identification is not an assumption of this memo.

`mGram` (`M.lean:806`) is the same matrix (`Variance.lean`: `mGram_eq_nGram`, by `rfl`) and, by
MC2's `mWord_centLift_fib`/`nWord_centLift_fib`, has the same provenance in the `M`-basis.

### The forced variance

Let `V = H₁` with basis `e₀…e₃` and `V* = H¹` with dual basis `x₀*…x₃*`. Let `φ` be a continuous
automorphism, `φ̄` its action on `V`, and write the **column layout**

```
φ̄(e_j) = Σ_i A_{ij} e_i .
```

Then `φ*(x_i*) = x_i* ∘ φ̄` has `φ*(x_i*)(e_j) = A_{ij}`, i.e.

```
φ*(x_i*) = Σ_j A_{ij} x_j*      — the coordinate vector of φ*(x_i*) is ROW i of A.
```

Preservation of the cup form is `⟨φ*x_i*, φ*x_j*⟩ = ⟨x_i*, x_j*⟩`, i.e.

```
Σ_{k,l} A_{ik} G_{kl} A_{jl} = G_{ij}      ⟺      A · G · Aᵀ = G.                        (★)
```

Equivalently, with the **row layout** `M̄ = Aᵀ` (rows = images on `H₁`), `(★)` reads
`M̄ᵀ · G · M̄ = G`. Both files assert `(★)`.

---

## 2. The two layouts, side by side

This is the decisive pair of definitions. Read them together and the discrepancy evaporates.

**MC3 — `M.lean:827–835`, rows hold images:**

```lean
noncomputable def mFrameMatrix (B : MDecomposition α) (ξ : …) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun i j => mRedTwo (toAdd (B.e (ξ (mFrameBasis α i)))) j
```

Row `i` is the coordinate vector of `ξ(eᵢ)`. So `mFrameMatrix = Aᵀ`, and `M.lean`'s clause
(`IsMStabilizer`, `M.lean:857–862`)

```lean
(mFrameMatrix B ξ).transpose * mGram * mFrameMatrix B ξ = mGram
```

is `(Aᵀ)ᵀ·G·Aᵀ = A·G·Aᵀ = G` — i.e. `(★)`. ✔

**MC4 — `N.lean:829–839`, columns hold images:**

```lean
noncomputable def NRows.col (R : NRows) : Fin 4 → NVec := ![(1, 0, 0, 0), R.x1, R.sigma, R.x2]
noncomputable def NRows.mat (R : NRows) (i j : Fin 4) : ZMod 2 := nMod2 (R.col j) i
```

`R.mat i j` is the `i`-th coordinate of the image of the `j`-th basis vector — the file's own
docstring says so in as many words. So `NRows.mat = A`, and `N.lean`'s clause
(`NRows.IsCupIsometry`, `N.lean:858–861`)

```lean
∀ i j, nCupForm (R.mat i) (R.mat j) = nGram i j
```

is `A·G·Aᵀ = G` — i.e. `(★)`, and moreover it is `(★)` in its most *semantic* form: by §1, row `i`
of `A` **is** the coordinate vector of `φ*(x_i*)`, so the clause literally says
"`⟨φ*x_i*, φ*x_j*⟩ = ⟨x_i*, x_j*⟩`". ✔

**Consequence.** The ticket's framing — "`nMatOf`'s rows also hold images" — is false;
`nMatOf`'s *columns* do. Column `1` of `nMatOf τ τσ τx p q g₁ g₂ h₁ h₂` is `(τ, 1, p, q)ᵀ`, which
is `NStabParam.rows.x1 = (τ, 1, p, q)` reduced mod 2 (`N.lean:920–923, 972–977`). That is the
entire content of the "discrepancy".

### The dictionary, in Lean

`Variance.lean` states it twice, once for each direction:

```lean
theorem mCupIsometry_iff_nCupForm (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    M.transpose * mGram * M = mGram ↔ ∀ i j, nCupForm (M.transpose i) (M.transpose j) = nGram i j

theorem nCupForm_iff_mul_transpose (A : Matrix (Fin 4) (Fin 4) (ZMod 2)) :
    (∀ i j, nCupForm (A i) (A j) = nGram i j) ↔ A * mGram * A.transpose = mGram
```

plus `nRows_isCupIsometry_iff` / `nRows_isCupIsometry_iff_mStyle`, which put `N.lean`'s
`NRows.IsCupIsometry` into `M.lean`'s matrix vocabulary and back.

---

## 3. The two counterexample claims: both true, and both the same one

Write the classified `M`-side closed form in `M.lean`'s layout (`MStabParam.Realizes`,
`M.lean:884–889`, plus the forced `t`-row `mXi_fixes_t`), with `b = B_c mod 2` and `ē = e mod 2`
— `β` and `γ` are units so their parities are `1`, and the `B̄`-components of `φ(C̄₀)`, `φ(D̄)` are
even so theirs are `0`:

```
              t   B̄   C̄₀   D̄
    φ(t)   [  1   0    0    0 ]
M̄ = φ(B̄)  [  τ   1    b    0 ]         (Variance.lean: mFrameMatrix_of_realizes)
    φ(C̄₀) [  0   0    1    0 ]
    φ(D̄)  [  b   0    ē    1 ]
```

Its transpose is an `N.lean` `nMatOf` on the nose:

```
M̄ᵀ = nMatOf τ 0 b b 0 1 ē 0 1
                                       (Variance.lean: mFrameMatrix_transpose_eq_nMatOf)
```

i.e. `(τ, τ_σ, τ_{x₂}, p, q, g₁, g₂, h₁, h₂) = (τ, 0, b, b, 0, 1, ē, 0, 1)`. The `N`-side
admissibility conditions of `nCup_iff_mod2` (`N.lean:963`) then read

```
det ḡ  = g₁h₂ + g₂h₁ = 1·1 + ē·0 = 1        ← M.lean's "γ is a unit"
p      = τ_{x₂}g₁ + τ_σ g₂ :  b = b·1 + 0·ē  ← M.lean's Witt coupling  t-comp of φ(D̄) = B_c mod 2
q      = τ_{x₂}h₁ + τ_σ h₂ :  0 = b·0 + 0·1  ← M.lean's "t-comp of φ(C̄₀) = 0"
```

— all three hold, **for every `τ`**. So `τ` is free (Lean: `mFrameMatrix_cupIsometry`), which is
what family M1 (`Λ_k : B ↦ A^k·B`, `mFamM1`, lifted by the axiom-free `mLambdaEquiv`,
`M.lean:1140, 1451`) needs, since `(mFamM1 α k).tau = k mod 2` (Lean: `mFamM1_tau`).

**MC3's claim.** Flip the variance in `M.lean`'s layout — `M̄·G·M̄ᵀ = G` — and entry `(0,1)`
becomes `nCupForm(row₀, row₁) = 1·τ + 1·1 = τ + 1`, which must equal `G₀₁ = 1`. Hence `τ = 0`,
and M1 survives only at even `k`. **CONFIRMED**, Lean-checked:
`mFrameMatrix_flip_forces_tau`.

**MC4's claim.** Flip the variance in `N.lean`'s layout — `Aᵀ·G·A = G` — and the same entry
`(0,1)` pairs column `0` of `nMatOf` with column `1`, i.e. `(1,0,0,0)` with `(τ,1,p,q)`, giving
`τ + 1 = 1`. Hence `τ = 0`, and N1 (`dnTauBEquiv`, exact and ν-invisible, `N.lean:560, 1663`)
dies. **CONFIRMED**, Lean-checked: `nMatOf_transpose_cup_forces_tau`, with the concrete
refutation `nMatOf_famN1_transpose_not_cupIsometry`.

**Do the claims survive translation?** Yes — into *each other*. Under `M̄ = Aᵀ`, MC3's flipped
condition `M̄·G·M̄ᵀ = G` *is* MC4's flipped condition `Aᵀ·G·A = G`, and the entry that kills `τ` is
`(0,1)` in both. The two tickets found the same obstruction, on the same `𝔽₂` matrix shape, at
the same entry, killing the same parameter — M1's `τ` and N1's `τ` are the same slot of the same
`nMatOf`. Neither report contradicts the other; each was describing the flip of its own layout.

**Why the flip is a real (wrong) alternative.** `G` is symmetric, but for symmetric invertible
`G` one has `Xᵀ G X = G ⟺ X G⁻¹ Xᵀ = G⁻¹`, so the flipped set equals `O(G)` only when `G⁻¹ = G`.
Here `G² = [[0,1,0,0],[1,1,0,0],[0,0,1,0],[0,0,0,1]] ≠ I`, so `G⁻¹ ≠ G` and the two conditions
really do cut out different sets. The Lean-checked witness is

```lean
theorem nMatOf_famN1_variance_differs :
    A * mGram * Aᵀ = mGram ∧ Aᵀ * mGram * A ≠ mGram      -- A = nMatOf 1 0 0 0 0 1 0 0 1
```

so the adjudication is not a distinction without a difference: it had to be settled.

---

## 4. `Variance.lean` — what landed

`GQ2/Dyadic/MarkedCore/Variance.lean`, 0 sorries, every declaration **std-3**, no new axiom,
census unchanged at 11.

| declaration | content |
|---|---|
| `mGram_eq_nGram` | `mGram = Matrix.of nGram` (`rfl`) — one Gram, two names |
| `nCupForm_transpose_eq` | `nCupForm (Mᵀ i) (Mᵀ j) = (Mᵀ·G·M) i j` — the bridge identity |
| `mCupIsometry_iff_nCupForm` | **the dictionary**, `M`-side reading |
| `nCupForm_iff_mul_transpose` | **the dictionary**, `N`-side reading |
| `nRows_isCupIsometry_iff` | `N.lean`'s clause as a matrix equation |
| `nRows_isCupIsometry_iff_mStyle` | `N.lean`'s clause = `M.lean`'s clause on the transpose |
| `mFrameMatrix_of_realizes` | the four rows of `M.lean`'s frame matrix at a classified parameter |
| `mFrameMatrix_transpose_eq_nMatOf` | **`M̄ᵀ` is an `N.lean` `nMatOf`** — the cross-file identification |
| `mFrameMatrix_cupIsometry` | soundness in `M.lean`'s variance, `τ` free |
| `mFrameMatrix_flip_forces_tau` | MC3's counterexample claim, verified |
| `mFamM1_tau` | `(mFamM1 α k).tau = k mod 2` |
| `nMatOf_famN1_cupIsometry` | N1 is an isometry in `N.lean`'s variance, every `τ` |
| `nMatOf_transpose_cup_forces_tau` | MC4's counterexample claim, verified |
| `nMatOf_famN1_transpose_not_cupIsometry` | the concrete refutation at `τ = 1` |
| `nMatOf_famN1_variance_differs` | the two variances are different conditions |

Notable: `mFrameMatrix_cupIsometry` — the *converse* of the Witt half of
`mStabilizer_classification`, which `M.lean` does not state — is obtained by pushing the
`M`-side matrix through the dictionary into `N.lean`'s `𝔽₂` decision procedure `nCup_iff_mod2`.
So the two tickets' machinery composes already, and the `M`-side never needs its own `2⁹`
kernel check.

**Registration.** `GQ2.lean` is *not* edited (ticket constraint), so `Variance.lean` is not yet
in the root import list. The orchestrator should add
`import GQ2.Dyadic.MarkedCore.Variance` after the `M`/`N` lines (cf. commit `026ef18`, which
registered `M` the same way) when merging this lane.

---

## 5. What MC5 must do

1. **Treat the two `Prop`s as interchangeable, via `Variance.lean`.** `IsMStabilizer`'s cup
   clause and `NRows.IsCupIsometry` are the same condition; `mCupIsometry_iff_nCupForm` /
   `nCupForm_iff_mul_transpose` / `nRows_isCupIsometry_iff_mStyle` move a hypothesis between the
   two vocabularies without re-deriving anything. Neither ticket's classification needs changing,
   and no `M`/`N` statement needs re-proving.

2. **Never move a *matrix* between the files without transposing it.** The `Prop`s agree; the
   matrices do not. The layout table:

   | object | layout / side |
   |---|---|
   | `mFrameMatrix B ξ` (`M.lean:827`) | rows = images; `H₁`, row-vector action |
   | `NRows.mat R`, `nMatOf` (`N.lean:839, 957`) | columns = images; `H₁`, column-vector action |
   | `MStabParam.act` (`M.lean:1077`) | acts on `H₁` frame coordinate vectors |
   | `mFrameLambda`, `frameTauD` (`M.lean:1405`, HM3) | act on `H¹` ν-frame vectors |
   | `NStabParam.nuAction`, `nCoreMat T` (`N.lean:1710, 1462`) | act on `H¹` ν-frame vectors, hence `T = gᵀ` |

   Both files carry **both** sides: the classification side is `H₁` (`mFrameMatrix`,
   `MStabParam.act`; `NRows.mat`, `nMatOf`) and the lifting side is `H¹` (`nuFrame` and the
   `mFrameLambda` / `nuAction` / `nCoreMat` family). The trap for MC5 is pairing an `H₁` matrix
   with an `H¹` one — e.g. reading `MStabParam.act` against `NStabParam.nuAction` — which drops a
   transpose. This is *not* an error in either file: `nuAction`'s `nCoreMat P.g.transpose` is
   correct as written, and `N.lean:1706–1709` documents exactly why ("a frame *vector* is the
   tuple of a character's values on the marked letters").

3. **Use `mFrameMatrix_transpose_eq_nMatOf` as the cross-core parameter dictionary** when the two
   classifications have to be compared: `M`'s `(τ, B_c mod 2, γ, e mod 2)` are `N`'s
   `(τ, τ_{x₂} = p, det ḡ = 1, g₂)`, with `M`'s Witt coupling literally `N`'s `couple_p`.

---

## 6. The one thing that *should* change (docs-only; NOT applied here)

Both files' variance notes are correct but under-specified, and that is what produced the
false alarm:

* `M.lean:67–71` (recorded finding 1) and `M.lean:770–777` (the §4 preamble) say the isometry is
  "`M̄ᵀ·G_M·M̄`, not `M̄·G_M·M̄ᵀ`" and instruct MC4 to "use the same side", **without saying that
  `M.lean`'s `M̄` has images in the rows**.
* `N.lean:38–39` and `N.lean:858–860` say the isometry is "`M̄·G_N·M̄ᵀ`" and that "the isometry
  condition is on the rows of `M̄`", **without saying that `N.lean`'s `M̄` has images in the
  columns** (the `NRows.mat` docstring does say it, one section away).

Read with the layouts, the two notes agree. Read without them, they contradict. The fix is
one clause in each docstring — no statement, proof, or definition changes:

* in `M.lean` §4's preamble: "on the mod-2 frame matrix `M̄` (**rows = images of the frame
  basis**)" — this phrase is *already there* at `M.lean:772`; what is missing is the corresponding
  warning that `N.lean`'s `M̄` is the transpose, so "the same side" means "the same condition",
  not "the same formula". Recommended replacement for finding 1's last sentence: *"MC4 uses the
  transposed layout (images in columns) and therefore states the same condition as
  `M̄·G_N·M̄ᵀ = G_N`; see `Variance.lean`."*
* in `N.lean` §4's `NRows.IsCupIsometry` docstring: add "(**`M̄ = NRows.mat` has the images in its
  columns**, so this is `M.lean`'s `M̄ᵀ·G·M̄ = G` on the transposed matrix — `Variance.lean`)".

Both files are closed, so this is left as a separate owner-visible docs ticket. It is cosmetic:
`Variance.lean` already carries the machine-checked statement that the two are the same, and no
consumer is at risk once it cites that file.

---

## 7. Provenance

Every claim above is either a definition quoted verbatim with a file:line, or a theorem in
`GQ2/Dyadic/MarkedCore/Variance.lean`. Nothing in this memo rests on either ticket's report.
Gates at the time of writing: `lake build GQ2` green (3419 jobs), `lake build
GQ2.Dyadic.MarkedCore.Variance` green, `scripts/check_dyadic.sh` green (axiom census 11, no
`sorry`, no `native_decide`, 5 capstones at the expected census set), and every declaration of
`Variance.lean` prints `[propext, Classical.choice, Quot.sound]`.
