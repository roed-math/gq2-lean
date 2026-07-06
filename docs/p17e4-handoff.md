# P-17e4 handoff — Lemma 6.11 reduced to a single-involution counting bound

**Owner history:** P-15f1 (file created) → P-17e4 (this work). **Date:** 2026-07-06.
**File:** `GQ2/RegularSummand.lean` (tracked, in the sorry allowlist).
**State:** compiles green; **exactly one `sorry`** remains (`involution_fixedPoints_sq_le`).

This file is self-contained: everything needed to continue P-17e4 is here or in the two
cross-referenced committed docs. No session scratchpad or chat context is required.

---

## 1. What P-17e4 is

`lemma_6_11` (paper §6.3, pp. 29–30) — *a ramified simple faithful 2-torsion module `V` over
the tame image is an equivariant split summand of a regular `𝔽₂[C]`-module* — is a **sorried
paper node** (allowlisted, not an axiom; assembled from Clifford + Higman, no single-citation
leaf). Discharging its one `sorry` removes `sorryAx` from the whole f1 dimension-count chain
(`equivariant_lift_of_regular_summand` → `lemma_6_17_dim`) with zero consumer churn — the
consumers already reference the sorried `lemma_6_11` and inherit `sorryAx` until it lands.

## 2. The single remaining `sorry`

```
theorem involution_fixedPoints_sq_le {C} [Group C] [TopologicalSpace C] [Finite C]
    {V} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ h : C, ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v) (P : Sylow 2 C)
    (g₀ : ↥(P : Subgroup C)) (hg : ∀ x : ↥(P : Subgroup C), x ∈ Subgroup.zpowers g₀)
    (s : ℕ) (hs : Nat.card ↥(P : Subgroup C) = 2 ^ s) :
    Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2 ≤ Nat.card V
```

**In words:** the involution `ω = g₀^{2^{s-1}}` of the cyclic Sylow-2 subgroup acts freely
enough on `V`: its fixed space is at most half, `#V^ω · #V^ω ≤ #V`. (The reverse `#V ≤ #V^ω²`
is automatic from concavity, so this forces `dim V^ω = dim V / 2`, i.e. `ω` acts **freely** as
an involution — the `p=2` elementary-abelian / Chouinard leaf.)

**Everything above it is proved** (see §3). This is now the *only* obstruction.

### Discharge plan (𝔽₂-rational — a recorded deviation from the paper, which uses 𝔽̄₂)

The paper (pp. 29–30) proves freeness over the whole cyclic 2-group by a weight-orbit
argument over an algebraic closure `𝔽̄₂` + faithfully-flat projectivity descent. We have
**reduced to the single-involution case**, whose descent is only quadratic. Route:

1. `𝔽₂[⟨cτ⟩]` is **étale** (odd order ⇒ separable), so `V|_{⟨cτ⟩}` splits along factor
   fields `𝔽₂ ⊆ K_i`. The trivial factor is absent: `V^{⟨cτ⟩} = 0`
   (proved: `fixedPoints_tame_inertia_eq_zero`). Simplicity + cyclicity of `⟨cτ⟩`
   (its subgroups are characteristic, so `C` permutes the factors transitively) force a
   **single `C`-orbit of factors, all faithful**.
2. **O₂-linchpin (where faithfulness enters — Remark 6.12):** if `ω` acted `K`-linearly on a
   factor it would centralize `⟨cτ⟩`; then the normal closure of `⟨ω⟩` would be an abelian
   normal subgroup with nontrivial `O₂`, which acts *trivially* on the simple char-2 module
   `V` by `FoxH.lemma_5_12` — contradicting `hfaith`. Hence `ω` acts **semilinearly through a
   nontrivial (order-2) Frobenius power** of `K_i`.
3. A semilinear involution on a finite field `K` (Frobenius `x ↦ x^{√|K|}` over the fixed
   subfield `K₀`, `[K:K₀]=2`) has fixed space exactly `dim_{𝔽₂} K / 2` — **additive Hilbert 90
   / normal-basis** for the degree-2 extension. Summing over the `C`-orbit of factors gives
   `dim V^ω = dim V / 2`, hence `#V^ω² = #V ≥` the bound.

Inputs a future session must build from scratch (finite-field linear algebra, **no** Clifford
induction, **no** `𝔽̄₂` base change): primitive idempotents of `𝔽₂[C_m]` (m odd) splitting
`V|_{⟨cτ⟩}`; the single-orbit/faithfulness argument of step 1–2 (uses the proved
`fixedPoints_tame_inertia_eq_zero` and `FoxH.lemma_5_12`); the quadratic semilinear
fixed-point count of step 3.

## 3. Proved architecture (all std-3 = `[propext, Classical.choice, Quot.sound]`, sorry-free)

The chain `lemma_6_11 ⇐ … ⇐ involution_fixedPoints_sq_le`, top (consumer) to bottom (leaf):

- `lemma_6_11` — assembled: Sylow-2 `P`, `Sylow.not_dvd_index` gives odd index, then the
  relative trace + `sylow_split_pair_of_ramified`.
- `sylow_split_pair_of_ramified` — `j := φ`, `q := φ⁻¹` from the freeness `≃+`.
- `sylow_free_of_ramified` — freeness `V|_P ≃+ 𝔽₂[P]^r`, from `free_of_card_fixedPoints_pow_le`
  (cyclic Sylow via `isCyclic_of_isPGroup_two_of_tame`) + the counting bound.
- `card_fixedPoints_pow_le_of_ramified` — the counting bound `#V^P^{|P|} ≤ #V`, **proved from
  the leaf** via the elementary-abelian reduction below.
- `card_fixedPoints_pow_le_of_half` — **the reduction**: given `#V^ω² ≤ #V` (the leaf), yields
  `#V^P^{|P|} ≤ #V`. Wires the involution bound to `b k := dim ker(nuOp g₀)^k` via
  card↔finrank (`Module.card_eq_pow_finrank`, `ZMod.card`), `b(2^s) = dim V`
  (`nuOp_pow_card_eq_zero`), and freshman `nuOp(g₀^{2^t}) = (nuOp g₀)^{2^t}`.

Supporting lemmas (all proved this session unless noted):

- **Counting criterion** `free_of_card_fixedPoints_pow_le` (+ engine `free_of_card_aux`,
  step `split_off_block`): over a cyclic 2-group, `#V^P^{|P|} ≤ #V` ⟹ `V ≃+ 𝔽₂[P]^r`
  equivariantly. Constructive: `split_off_block` peels one free rank-1 block via the explicit
  geometric-series inverse of the convolution `T = 1 + (μ+1)B`.
- **Concavity** `finrank_ker_pow_succ` (`dim ker νᵏ⁺¹ = dim ker νᵏ + dim(im νᵏ ⊓ ker ν)`) and
  `finrank_ker_pow_concave` (increment antitone via `finrank_mono` on `im νᵏ⁺¹ ≤ im νᵏ`).
- **Numeric core** `seq_double_le` (concavity ⇒ `b(2m) ≤ 2 b m`) and `seq_first_increment_le`
  (`2 b m = b(2m)` ⇒ all increments equal ⇒ `2m·b 1 = b(2m)`); pure ℕ, via
  `Finset.sum_eq_sum_iff_of_le` + antitone squeeze.
- **Char-2 ring helpers** `add_pow_two_pow_of_two_eq_zero` (freshman `(A+B)^{2^k}=A^{2^k}+B^{2^k}`),
  `geom_sum_two_pow_of_two_eq_zero`, `geom_inverse_of_nilpotent`, `finConsAddEquiv`.
- **Operators** `genOp`, `genOp_pow`, `nuOp`, `end_two_eq_zero`, `nuOp_pow_card_eq_zero`,
  `sum_smul_eq_nuOp_pow`, `card_fixedPoints_eq_card_ker_nuOp`, `card_ker_pow_le`.
- **Kernel toolbox** (earlier P-17e4) `quotient_zpowers_isCyclic_of_tame`,
  `isCyclic_of_isPGroup_two_of_tame` (Sylow-2 of a tame-generated group is cyclic),
  `fixedPoints_tame_inertia_eq_zero` (`V^{⟨cτ⟩}=0` on a ramified simple module).
- **Relative trace** `regular_summand_of_subgroup_summand` (odd-index `H/P` averaging, the
  "Sylow criterion for modular projectivity", `ρ∘ι = [C:P]·id = id`).
- **Consequence** `equivariant_lift_of_regular_summand` (the `Hom(V,−)`-exactness deep-count
  input; sorry-free from the summand package, carries `sorryAx` only via a `lemma_6_11`
  consumer).

## 4. Verify (from repo root `~/claude/gq2-lean`)

```
lake build                                    # whole library green (~8679 jobs)
lake env lean <scratch with #print axioms>    # see below
./scripts/check_axioms.sh                      # census 15, allowlist, no native_decide
```

Axiom flow (verified 2026-07-06): the reduction is Ax ∅
```
#print axioms GQ2.finrank_ker_pow_concave        -- [propext, Classical.choice, Quot.sound]
#print axioms GQ2.card_fixedPoints_pow_le_of_half -- [propext, Classical.choice, Quot.sound]
#print axioms GQ2.lemma_6_11                      -- +sorryAx, only via involution_fixedPoints_sq_le
```

## 5. Gotchas banked (this file's idioms)

- Bare `nuOp`/`genOp` in a `have`/`show` **type** need an explicit `: Module.End (ZMod 2) V`
  ascription — otherwise `V` is a metavariable and the `SMulCommClass P (ZMod 2) V` instance
  search gets stuck.
- `omega` refuses nonlinear `2^s * b 1` vs `b 1 * 2^s` — `rw [mul_comm]` first.
- `k+1+1` vs `k+2` are different atoms to `omega`/`rw` — normalise with `show … from rfl`.
- `Fin.cons` on a constant family needs `(α := fun _ => M)` at every use.
- `decide` / numeral `rw` on `(2 : ZMod 2)` or `(2 : Module.End (ZMod 2) M)`: hoist to a
  top-level `have` first (polymorphic `one_add_one_eq_two` catches the wrong `2`).
- A single `rw [AddEquiv.apply_symm_apply]` rewrites *all* identical occurrences.

## 6. Cross-references (committed)

- `docs/tickets.md` — board row **P-17e4** (full status, all increments, gotchas).
- `docs/p17e-kappa0-scoping.md` — Griess-falsity of the general κ⁰ statement, the Option-A′
  restatement, and Addenda 1–2 (the counting-criterion and involution reductions).

## 7. Shared-worktree note

`GQ2/RegularSummand.lean` is now **committed** (was riding the working tree per the batch
convention; committed for handoff durability at the user's request). Its 17-module import
closure contains none of the sibling sessions' in-flight files, so it builds against HEAD.
Other uncommitted working-tree changes in this shared worktree (`SectionNine.lean`,
`LocalKummer.lean`, `HilbertLedger.lean`, `SectionEight.lean`, `WordCoh2.lean`, `GQ2.lean`,
various `docs/*` and untracked `GQ2/*.lean`) belong to **other** parallel sessions — do not
commit or revert them.

## 8. Downstream / adjacent

- `lemma_6_11`'s consumer is `equivariant_lift_of_regular_summand` → the f1 deep-count
  (`lemma_6_17_dim` lower bound `#X₊ ≥ 2^m`), tracked under the P-15f / P-17i chain.
- **e5 design flag (open):** `kappa0_exists`'s `htame` supplies an abstract `(s,t)`, but
  `lemma_6_11` wants `c : ContinuousMonoidHom Ttame C`. The P-17e5 assembly needs the
  finite-presentation → marking bridge (Ttame universal property) or a statement alignment.
