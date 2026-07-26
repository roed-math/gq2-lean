# SL-campaign: discharging SL1/SL2 (owner go-ahead 2026-07-26)

Owner (in-session, after the GL-campaign closed): "Go ahead with SL1/SL2."  The four
remaining `StageLemma.lean` sorries: `stageSL1R0/R2` (reachability), `stageSL2R0/R2`
(digit adjustment).  Orchestrator design session 2026-07-26; harnesses in the session
scratchpad (`sl1_hunt.py`, `sl1_hunt2.py`, `sl1_fun.py`, building on the GL-campaign's
`span_model.py`).

## 1. SL2 — design COMPLETE (and a correction to the 2026-07-26 L4c annotations)

### 1.1 The twisted-slot digit is AUTOMATIC — L4c's refutation used the wrong modulus

L4c annotated `labute-l1-design.md` §3 item 5: "applying χ_{k+1} to δ(T) = 1 gives
χ(A)²χ(S)⁴ = 1 in (ZMod 2^{k+1})ˣ, which is vacuous … needs a relator identity one level
higher".  **The lift to the group repairs this.**  The corrected triple `T'` lives in
`Q_{k+1}`; its relator clause `d0Word(T') = 1` says the GROUP word `d0Word(t₀,t₁,t₂)`
(any lifts `tᵢ`) lies in `λ_{k+1}(D_R)`.  The repo's exact depth lemma
`χ(λ_j) ⊆ 1 + 2^{j+1}ℤ₂` (j ≥ 2; `twoCentralSeries_units_le` shape, the
`chiLevel_lambdaImage_pred` mechanism) at `j = k+1` therefore gives the relation **at
modulus `2^{k+2}`, from level-(k+1) data only**:

    χ(t₀)²·χ(t₁)⁴ ∈ 1 + 2^{k+2}ℤ₂        (r0; commutator dies in ℤ₂ˣ)

Writing `χ(t₀) = −(1+2^k α₀)`, `χ(t₁) = 1+2^k α₁`: the left side is
`1 + 2^{k+1}α₀ mod 2^{k+2}` (the ⁴-slot enters at `2^{k+2}`, the `2^{2k}`-terms die for
k ≥ 2), so `α₀ ≡ 0 (2)` — i.e. `χ(t₀) ≡ −1 mod 2^{k+1}`, exactly the level-(k+1)
χ-clause for slot 0, **with no digit adjustment needed and no Q_{k+2} input**.  Mirror
(r2): the relation is `χ(t₂)²·χ(t₁)⁻⁴ ∈ 1+2^{k+2}` and the exact target identity is
`X⁻⁴·Y² = 1` (from `Y = −X²`); slot 2 (the twisted `y`-slot) is automatic.  Both
target-relations hold EXACTLY in ℤ₂ˣ: `(−1)²·1⁴ = 1` and `X⁻⁴Y² = 1`.

### 1.2 The two free digits: explicit kernel witnesses = powers of the canonical lifts

The d̄-slots bracket against the canonical lifts themselves
(`dbarWordR0 (canonLift T₀) (canonLift T₁) (canonLift T₂) w` has bracket factors
`[w₁, t̄₂]` and `[w₂, t̄₁]`), so modifications that are powers of the lifts kill their own
brackets **definitionally**:

- direction 1 (r0; χ-values of the triple ≈ targets `(−1, 1, η)` mod `2^k`):
  * `w = ![1, t̄₂^{2^{k-2}}, 1]`:  `d̄(w) = [t̄₂-power, t̄₂] = 1`; moves the slot-1 digit by
    the k-digit of `χ(t̄₂)^{2^{k-2}} ≈ η^{2^{k-2}}`, which is **1** since
    `v₂(η−1) = 2` ⇒ `v₂(η^{2^m}−1) = m+2` (LTE), at `m = k−2` giving exactly `k`.
    Move `(1,0)`.
  * `w = ![1, v, v]`, `v = (t̄₁·t̄₂)^{2^{k-2}}`:  `d̄(w) = [v,t̄₂]·[v,t̄₁] = commP v (t̄₁t̄₂)
    ·(central rearrangement) = 1` (v is a power of `t̄₁t̄₂`); digit contribution
    `(1·η)^{2^{k-2}}`-digit = 1 to BOTH slots.  Move `(1,1)`.
  * `(1,0)` and `(1,1)` span `𝔽₂²`; choose `w ∈ {1, move₁, move₂, move₁·move₂-slotwise}`
    per the discrepancy pair.  (If composing two moves, either prove the small
    `dbarWord` multiplicativity-in-`w` lemma — same GL-A calculus, corrections die for
    k ≥ 3 — or use the single combined triple `![1, u·v, v]` and expand directly.)
- direction 2 (r2; targets `(S, X, Y)`):  even easier — `v₂(S−1) = v₂(X−1) = 2` exactly
  (S ≡ 13, X ≡ 5 mod 16), so the SINGLE-lift-power witnesses `![t̄₁^{2^{k-2}},1,1]`
  (kills `[w₀,t̄₁]`, moves slot-0 by 1) and `![1,t̄₀^{2^{k-2}},1]` (kills `[w₁,t̄₀]`,
  moves slot-1 by 1) give `(1,0)` and `(0,1)` directly.

Deviation slack: `w_i ∈ lambdaImage (k−1) (k+1)` via the `2^{k-2}`-power membership
(GL-B's `pow_two_pow_mem_lambdaImage` shape); the χ-value of a lift is the target times
`(1 + 2^k·dev)` and the junk enters the `2^{k-2}`-power at `2^{2k-2} ≥ 2^{k+1}` — the
witness digits are deviation-independent.

### 1.3 SL2 assembly checklist (per direction)

Given `hT : T ∈ sPR0 k`, `hδ : defectR0 k T = 1`: choose `w` per §1.2 against the two
digit discrepancies of `canonLift T` (they are well-defined: lift ambiguity is
`zLayer k` with `χ(λ_k) ⊆ 1+2^{k+1}`).  Then:
- membership: §1.2;
- `d̄(w) = 1`: §1.2 (definitional kills + centrality);
- relator clause at k+1: `d0Word(canonLift T · w) = δ(T)·d̄(w) = 1` (L4c's shift
  identity `d0Word_mul_lambdaImage` — private in StageLemma, restate);
- generation: `closure_range_mul_eq_top_of_mem_lambdaImage_two` (public);
- χ-clause at k+1: slots 1,2 by the witness digits (LTE valuations + `chiLevel`
  multiplicativity); slot 0 by §1.1.
Needed new small lemmas: LTE (`v₂(u^{2^m}−1) = v₂(u−1)+m` for `v₂(u−1) ≥ 2`; induction
via `u^{2^{m+1}}−1 = (u^{2^m}−1)(u^{2^m}+1)`, second factor v₂ = 1), the three exact
valuations `v₂(η−1) = v₂(X−1) = v₂(S−1) = 2`, the two exact target-relations, and the
digit bookkeeping through `chiLevel`/`chiTargetR0/R2` (`ZMod (2^k)ˣ` casts — the
`units_map_castHom_toZModPow` machinery is already in Levelwise).

## 2. SL1 — mechanism FOUND at k = 3; uniformity validation dispatched

Harness (faithful: tower dims 10/20/44 reproduced; spike dichotomy reproduced — P-good
seeds give `δ ∈ ⟨Im d̄ ∪ R_k⟩`, P-violating give `δ ∉`):

- Model: `Z_k(D) = Z_k(F₃)/R_k`, `R_k` = the relator layer (all π/ad-compositions of the
  presenting relator to level k) in Magnus coordinates; δ computed by explicit
  descent-correction (multiply by relator atoms level by level).
- **The two coker functionals at k = 3 (dir 1, letters (s,x,y)) have support, in the
  PBW/Lyndon dual basis:**
  * `φ₀` ↔ `{π²s, π[s,y], [[s,y],y]}` — the s-rooted y-column; values: tails ↦ (1,0);
  * `φ₁` ↔ `{π²x, π[x,y], [[x,y],y]}` — the x-rooted y-column; tails ↦ (1,1);
  * both kill `Im d̄ + R₃` and both kill `δ(good seeds)`.
  Conjecture (to validate): at level k the pair is the height-graded z-rooted y-column
  `{π^{k-1-m}·(ad y)^m(z)}_{m=0..k-1}`, z ∈ {s, x} — i.e. the Magnus digit sum along the
  words `z·y^m` — crossed-derivation (χ-twisted Fox) data along the y-direction, the
  `ker(ab)`-sensitive functionals the 2026-07-26 refutation demanded.  GL-D's
  `coord/zCoord` machinery expresses exactly these.
- Lean shape (draft): define φ on `Z_k(D)` via free preimages (the λ-verbal surjection
  `Z_k(F₃) ↠ Z_k(D)`, span_descent machinery); well-definedness = φ kills the relator
  layer (a Magnus-ideal valuation statement about `μ(r)−1` on y-parabolic words);
  `φ(Im d̄_T) = 0` (per-atom valuation computation); `φ(tails) ≠ 0` completes coker-2;
  `φ(δ(T)) = 0` from the χ-clause — the ONE step whose uniform identity is not yet
  derived (empirically true; the numerics worker's regression will exhibit the
  relation before Lean work starts).

Open items (SL1-N ticket): (i) confirm the functional support pattern at k = 4, 5 both
directions (needs greedy triple-refinement in the harness — correct T level-by-level
using the solved modification + §1.2 digit moves, reproducing the spike's P-guided
greedy); (ii) sample many `sPR0(k)`-triples and regress `φ(δ(T))` against the χ-digit
data of T to exhibit the pinning identity; (iii) P-violating controls at k = 4.

## 3. Tickets

| id | scope | model | files |
|---|---|---|---|
| SL0 | this design + harness + memo (orchestrator) | fable | memo, scratchpad |
| SL2-L | fill `stageSL2R0/R2` per §1 | opus | `GQ2/Roe/Labute/StageLemma.lean` (sole owner while running) |
| SL1-N | numerics: §2 open items, report `sl1-numerics.md` | opus | scratchpad + `docs/orchestration/sl1-numerics.md` |
| SL1-L | fill `stageSL1R0/R2` (dispatch after SL1-N + orchestrator design pass) | opus | StageLemma (after SL2-L lands) |

House rules as in the GL-campaign: path-limited commits, no board edits by workers, no
`check_axioms.sh`/`atlas-audit.md` edits, no lean-lsp file tools (wrong root), frozen
statements, no new axioms, no native_decide.
