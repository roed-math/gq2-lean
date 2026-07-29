# AX5 — ramified-simple projectivity: try-prove-first verdict

**Ticket:** AX5 (lane AX, board [`tickets.md`](tickets.md); plan [`plan.md`](plan.md) §4 row AX5).
**Packet row:** §12 local-inputs table, *Projectivity* — "A faithful ramified simple tame
`𝔽₂[H]`-module is projective, so isotypic functors and inflation–restriction are exact",
formal destination `RamifiedSimple.projective`. Draft §8 status item 3 ("the modular
projectivity criterion for a module free over a Sylow subgroup").

---

## 0. Verdict

**PROVABLE — no axiom. AX5 closes as a theorem ticket; census delta `+0`.**

The statement is *already a sorry-free, axiom-free theorem in this repository* for `q = 2`:
`GQ2.lemma_6_11_of_tame_pair` (`GQ2/RegularSummand/Involution.lean:706`), the head of a
self-contained 2 200-line finite-representation-theory development
(`GQ2/RegularSummand/{Trace,Freeness,Involution,Lifting}.lean`) whose `#print axioms` is
`[propext, Classical.choice, Quot.sound]`. The ℚ₂ path never had a projectivity axiom.

The *only* place the whole chain touches `q = 2` is the hypothesis
`hrel : sg⁻¹ * t * sg = t ^ 2`, and every one of its uses is a call to one of two leaf lemmas
producing **(i)** `(Subgroup.zpowers t).Normal` and **(ii)** `Odd (orderOf t)`. Replacing that
hypothesis by those two facts generalises the entire chain **with no change to a single proof
body**. This was verified, not estimated: a scratch build with the hypothesis swapped applied
mechanically to all nine affected declarations, plus ~55 lines of new general-`q` leaf lemmas,
compiles clean — 0 errors, 0 sorries — and

```
'GQ2.lemma_6_11_of_tame_pair_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
```

where `lemma_6_11_of_tame_pair_pow` is the general-`q_K = 2^f` statement the dyadic campaign
needs. Estimated remaining work: **one opus dispatch, ≈ 1–2 h** (new file ≈ 110 lines + a
20-line hypothesis swap in two frozen ℚ₂ files, guarded by name-preserving wrappers).

---

## 1. The exact statement the campaign needs (task 1)

### 1.1 What the packet's two clauses actually cash out to

The packet sells projectivity as one row with two consequences. In the formalization they are
*different* obligations with *different* discharges, and only one of them is a projectivity fact:

| packet clause | formal consumer | discharged by |
|---|---|---|
| "inflation–restriction is exact" (injective half, `H¹(H,V) = 0`) | `LocalKummer.InflationVanishes` (`GQ2/LocalKummer.lean:304`) | **not projectivity** — coprime averaging over the odd normal inertia, `inflationVanishes_of_oddNormal` (`:493`), `inflationVanishes_ramifiedTame` (`:587`) |
| "inflation–restriction is exact" (surjective half, `H²(H,V) = 0`) | `LocalKummer.FamiliesExtend` (`:898`) | **projectivity** — `Shapiro.familiesExtend_of_package` (`GQ2/Shapiro/Extend.lean:271`) consumes the regular-summand package |
| "isotypic functors are exact" (`Hom_H(V^∨, −)`-exactness) | `HomCounting.card_equivHoms_of_exact` (`GQ2/HomCounting.lean:132`, surjectivity step at `:152`) | **projectivity** — `equivariant_lift_of_regular_summand` (`GQ2/RegularSummand/Lifting.lean:82`) |

The `LocalKummer.lean:361` file comment is explicit and correct: *"`InflationVanishes`
(= `H¹(H_V,V) = 0` content) is **not** a projectivity fact"*. LG4 must not spend an axiom on it;
it needs `(I ◁ H odd, V^I = 0)` only, both of which the ramified-simple hypotheses give
(`fixedByNormal_eq_bot`, `odd_orderOf_tameInertia`, `tameInertia_normal`).

### 1.2 The minimal statement

The minimal thing LG4 (packet Def. 6.11 items (1) and (3)) invokes is the **split-summand shape**,
not the word "projective":

> `V` is an equivariant split summand of a regular module `𝔽₂[H]^N`
> (i.e. `∃ N (ι : V →+ 𝔽₂[H]^N) (r : 𝔽₂[H]^N →+ V)`, both `H`-equivariant, with `r ∘ ι = id`).

This is *equivalent* to `Module.Projective (MonoidAlgebra (ZMod 2) H) V` but strictly better for
Lean: the regular module is spelled `Fin N → H → ZMod 2` with the left-translation action written
inline, so no `MonoidAlgebra`-module instance, no scalar-tower diamond, and the two consumers
above use `(ι, r)` directly. **Keep this shape.** The general-`K` statement is the same with
`H = ` the finite tame image at `q_K = 2^f`:

```lean
theorem lemma_6_11_of_tame_pair_pow {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} {f : ℕ} (hf : 1 ≤ f)
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ (2 ^ f))
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v
```

`hgen`/`hrel` say "`C` is a finite tame image at `q = 2^f`" without mentioning `T_q`; the
`F3`-facing wrapper taking a `ContinuousMonoidHom (T_q) C` is a two-line corollary (the `q = 2`
precedent is `lemma_6_11` at `Involution.lean:738`, whose body is `tame_rel_image`-then-apply).

*Over-generality is free here*: the proved core needs only `⟨t⟩ ◁ C` **odd** with `C = ⟨sg,t⟩`;
`q` never appears. `hf : 1 ≤ f` is used only to know `2^f` is even and nonzero.

---

## 2. Status in the repository (why this is nearly free)

`GQ2/RegularSummand.lean` (umbrella docstring) is the paper node Lemma 6.11 = packet's
`RamifiedSimple.projective`. Architecture, all axiom-free:

1. **Sylow-2 is cyclic** — `isCyclic_of_isPGroup_two_of_tame` (`Trace.lean:206`): `P ∩ ⟨t⟩ = 1`
   (odd order) so `P` embeds in the cyclic quotient `C/⟨t⟩` (`quotient_zpowers_isCyclic_of_tame`,
   `Trace.lean:181`).
2. **`V|_P` is free** — `sylow_free_of_ramified_of_tame_pair` (`Involution.lean:653`), via the
   constructive counting criterion `free_of_card_fixedPoints_pow_le` (`Freeness.lean:822`;
   `#V^P ^ |P| ≤ #V` ⟹ free, geometric-series retraction, no structure theorem),
   Jordan-block concavity `card_fixedPoints_pow_le_of_half` (`Freeness.lean:842`) reducing to the
   single involution `ω = g₀^{2^{s−1}}`, and `involution_fixedPoints_sq_le_of_tame_pair`
   (`Involution.lean:415`) proving `#V^ω ^ 2 ≤ #V` by an explicit **𝔽₂-rational trace element**
   (a recorded deviation from the paper's `𝔽̄₂` weight-orbit argument: no base change, no
   idempotents, no semilinear algebra).
3. **Odd-index relative trace** — `regular_summand_of_subgroup_summand` (`Trace.lean:81`):
   `[C : P]` odd, so in char 2 the relative trace hits the identity (`odd_nsmul_eq_self`,
   **no division** — this is why mathlib's Maschke cannot be used, see §5).

The linchpin where *faithful* + *ramified* are consumed is
`two_torsion_of_centralizer_eq_one` (`Involution.lean:171`): the centralizer `C_C(⟨t⟩)` contains
the central `⟨t⟩` with cyclic quotient, hence is abelian, hence its 2-torsion is a normal
2-subgroup, which acts trivially on the simple `V` and dies by faithfulness. (Remark 6.12's
counterexample is recorded in the file: `C₃ ⋊ C₄` acting through `S₃` on `𝔽₄` is ramified simple
but *not* faithful, and its central `C₂` fixes everything.) Independent check while writing this
memo: the classical Clifford-theoretic route (Sylow-free permutation of the `T`-eigenspaces over
a splitting field, `O₂(H) = 1` from faithfulness, `C_H(T)` odd) gives the same theorem and the
same place for the hypotheses — the repo's route is the same mathematics done `𝔽₂`-rationally.

Consumers already wired (all would inherit the general-`q` version verbatim):
`DimAssembly.lean:239,272`, `DimClose.lean:88`, `KappaNormalForm.lean:1218`,
`RegularIsometry.lean` (upgrade to an isometry), `HomCounting.lean:152`,
`Shapiro/Extend.lean:271`.

---

## 3. What changes for general `q_K = 2^f` (the measured diff)

Every occurrence of `hrel` in the chain (`grep -c hrel GQ2/RegularSummand/{Trace,Involution}.lean`
= 5 + 21 = 26 lines, across nine declarations) is one of: the binder itself, a recursive
pass-through, or one of exactly **two** derivations —

```lean
Tame.zpowers_normal_of_tame hgen hrel      -- (Subgroup.zpowers t).Normal
Tame.tame_odd_order (orderOf_pos sg).ne' hrel   -- Odd (orderOf t)
```

Nothing else in 1 000 lines of proof body knows about `q`. In particular the `q` that appears
*inside* `involution_fixedPoints_sq_le_of_tame_pair` is the conjugation exponent of the
involution `ω` (derived from normality of `⟨t⟩`), **not** the relation exponent — that argument is
already exponent-generic.

### 3.1 Spike result (task 3)

Scratch file (not in the repo):
`…/scratchpad/ax5_spike.lean`, 922 lines = the `KernelToolbox` section of `Trace.lean` + the
whole `Involution.lean` chain, copied **verbatim** except for the mechanical substitution

| from | to |
|---|---|
| `(hrel : sg⁻¹ * t * sg = t ^ 2)` | `(hTnorm : (Subgroup.zpowers t).Normal) (hTodd : Odd (orderOf t))` |
| `Tame.zpowers_normal_of_tame hgen hrel` | `hTnorm` |
| `Tame.tame_odd_order (orderOf_pos sg).ne' hrel` | `hTodd` |
| `… hgen hrel …` (call sites) | `… hgen hTnorm hTodd …` |

plus the four new general-`q` leaves of §4.1 and the entry point of §1.2. Checked with
`cd ~/claude/gq2-lean && lake env lean <scratch>`:

* **0 errors, 0 sorries** (warnings only: three declarations no longer reference `hTodd`/`hgen`
  — see §4.3);
* `#print axioms GQ2.lemma_6_11_of_tame_pair_pow` = `[propext, Classical.choice, Quot.sound]`;
* the `q = 2` back-compat wrapper (old statement, unchanged) also compiles and prints std-3.

So the general-`q` theorem is **proved today**, modulo landing it in the repo in a form the
freeze (plan A6) allows.

---

## 4. The deliverable (ready-to-land text)

### 4.1 New file `GQ2/Dyadic/Projectivity.lean` — leaf lemmas, verified

These are new mathematics for the campaign (the finite-image half of packet Lem. 3.1/3.2 at
general `q`); the text below is exactly what typechecked.

```lean
variable {G : Type*} [Group G]

/-- Iterated conjugation at a general exponent: `(sⁿ)⁻¹ t sⁿ = t^(qⁿ)`. -/
theorem conj_pow_iterate_pow {s t : G} {q : ℕ} (h : s⁻¹ * t * s = t ^ q) :
    ∀ n : ℕ, (s ^ n)⁻¹ * t * s ^ n = t ^ (q ^ n) := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    have step : (s ^ (k + 1))⁻¹ * t * s ^ (k + 1)
        = (s ^ k)⁻¹ * (s⁻¹ * t * s) * s ^ k := by group
    rw [step, h]
    have conj_q : (s ^ k)⁻¹ * t ^ q * s ^ k = ((s ^ k)⁻¹ * t * s ^ k) ^ q := by
      have hc := conj_pow (a := (s ^ k)⁻¹) (b := t) (i := q)
      simpa using hc.symm
    rw [conj_q, ih, ← pow_mul, ← pow_succ]

/-- **Packet Lem. 3.1 at general `q` (finite image).** If `⟨s,t⟩` is finite with `s⁻¹ t s = t^q`
and `q` is even and nonzero (in particular `q = q_K = 2^f`, `f ≥ 1`), then `t` has odd order. -/
theorem tame_odd_order_pow {s t : G} {q : ℕ} (hs : orderOf s ≠ 0) (hq0 : q ≠ 0) (hq : Even q)
    (h : s⁻¹ * t * s = t ^ q) : Odd (orderOf t) := by
  set k := orderOf s with hk
  have hconj := conj_pow_iterate_pow h k
  rw [pow_orderOf_eq_one] at hconj
  simp only [inv_one, one_mul, mul_one] at hconj
  have hpos : 1 ≤ q ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hq0)
  have hone : t ^ (q ^ k - 1) = 1 := by
    rw [← mul_left_inj t, one_mul, ← pow_succ, Nat.sub_add_cancel hpos, ← hconj]
  have hdvd : orderOf t ∣ q ^ k - 1 := orderOf_dvd_of_pow_eq_one hone
  rcases Nat.even_or_odd (orderOf t) with he | ho
  · exfalso
    have hd1 : (2 : ℕ) ∣ q ^ k - 1 := he.two_dvd.trans hdvd
    have h2q : (2 : ℕ) ∣ q ^ k := (Even.two_dvd hq).trans (dvd_pow_self q hs)
    omega
  · exact ho

/-- `⟨t^q⟩ = ⟨t⟩` when `q` is prime to `orderOf t`. -/
theorem zpowers_pow_eq_of_coprime {t : G} {q : ℕ} (hcop : Nat.Coprime q (orderOf t)) :
    Subgroup.zpowers (t ^ q) = Subgroup.zpowers t := by
  refine le_antisymm (Subgroup.zpowers_le.2 (Subgroup.pow_mem _ (Subgroup.mem_zpowers t) q))
    (Subgroup.zpowers_le.2 ?_)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]; exact hm⟩

/-- **Packet Lem. 3.2 at general `q` (finite image).** `⟨t⟩ ◁ ⟨s,t⟩` whenever `s⁻¹ t s = t^q`.
No hypothesis on `q` is needed: conjugation is an automorphism, so `t ↦ t^q` is injective on
`⟨t⟩`, which already forces `gcd(q, orderOf t) = 1`. -/
theorem tame_zpowers_normal_pow {s t : G} [Finite G] {q : ℕ}
    (hgen : Subgroup.closure {s, t} = ⊤) (h : s⁻¹ * t * s = t ^ q) :
    (Subgroup.zpowers t).Normal := by
  have hcop : Nat.Coprime q (orderOf t) := by
    have hsc : SemiconjBy s⁻¹ t (t ^ q) := by
      show s⁻¹ * t = t ^ q * s⁻¹
      rw [← h]; group
    have hconj : orderOf t = orderOf (t ^ q) := hsc.orderOf_eq
    rw [orderOf_pow t] at hconj
    have hpos : 0 < orderOf t := orderOf_pos t
    have hgpos : 0 < Nat.gcd (orderOf t) q :=
      Nat.pos_of_ne_zero fun h0 => by rw [Nat.gcd_eq_zero_iff] at h0; omega
    have : Nat.gcd (orderOf t) q = 1 := by
      by_contra hne
      have h1 : 1 < Nat.gcd (orderOf t) q := by omega
      have hlt := Nat.div_lt_self hpos h1
      omega
    exact Nat.coprime_comm.mp this
  have hmaps : (Subgroup.zpowers t).map (MulAut.conj s⁻¹).toMonoidHom = Subgroup.zpowers t := by
    have hc : (MulAut.conj s⁻¹).toMonoidHom t = t ^ q := by
      show s⁻¹ * t * s⁻¹⁻¹ = t ^ q
      rw [inv_inv]; exact h
    rw [MonoidHom.map_zpowers, hc]; exact zpowers_pow_eq_of_coprime hcop
  have hs_norm : s ∈ Subgroup.normalizer (Subgroup.zpowers t) := by
    have hinv := Subgroup.mem_normalizer_iff_map_conj_eq.mpr hmaps
    simpa using Subgroup.inv_mem _ hinv
  have ht_norm : t ∈ Subgroup.normalizer (Subgroup.zpowers t) :=
    Subgroup.le_normalizer (Subgroup.mem_zpowers t)
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  exacts [SetLike.mem_coe.2 hs_norm, SetLike.mem_coe.2 ht_norm]
```

and the entry point (statement in §1.2), whose proof is:

```lean
  have heven : Even (2 ^ f) := by
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    exact ⟨2 ^ f', by rw [pow_succ]; ring⟩
  exact lemma_6_11_of_odd_normal hgen (tame_zpowers_normal_pow hgen hrel)
    (tame_odd_order_pow (orderOf_pos sg).ne' (pow_ne_zero _ two_ne_zero) heven hrel)
    hV2 hfaith hsimple hram
```

### 4.2 In-place edit to two frozen ℚ₂ files (needs orchestrator sign-off, plan A6)

`lemma_6_11_of_odd_normal` is the hypothesis-generalised core. It cannot live in
`GQ2/Dyadic/Projectivity.lean` (that would invert the dependency: the ℚ₂ chain would have to
import `Dyadic`). Recommended landing — **purely additive at the call-site level**:

* In `GQ2/RegularSummand/Trace.lean` and `GQ2/RegularSummand/Involution.lean`, rename the nine
  `hrel`-taking declarations to `…_of_odd_normal`, swap the binder
  `(hrel : sg⁻¹ * t * sg = t ^ 2)` → `(hTnorm : (Subgroup.zpowers t).Normal) (hTodd : Odd (orderOf t))`,
  delete the two `have`s that derived them, and thread the new binders. **No proof body changes**
  (verified in §3.1).
* Re-add, under the *old* names and with the *old* statements, one-line `q = 2` wrappers for the
  two declarations referenced outside `GQ2/RegularSummand/`:
  `lemma_6_11_of_tame_pair` (4 call sites: `DimAssembly.lean:239,272`, `DimClose.lean:88`,
  `KappaNormalForm.lean:1218`) and `two_torsion_of_centralizer_eq_one`
  (1 call site: `KappaNormalForm.lean:1267`). Bodies:
  `… hgen (Tame.zpowers_normal_of_tame hgen hrel) (Tame.tame_odd_order (orderOf_pos sg).ne' hrel) …`.
  The remaining seven names have no external references (checked: `formalization.yaml`,
  `docs/**`, `scripts/**` mention none of them).
* `lemma_6_11` (the `Ttame` marking wrapper, `Involution.lean:738`) keeps its statement verbatim.

Net effect on the ℚ₂ path: statements of every externally-visible name are byte-identical, so
`scripts/check_axioms.sh` check 5 (capstone axiom prints) cannot move. Diff ≈ 20 changed lines
+ ≈ 25 added wrapper lines across the two files.

**Fallback if the owner declines any edit to frozen files:** copy the 922-line generalised chain
into `GQ2/Dyadic/Projectivity.lean` (this is literally the spike file). It compiles as-is and is
axiom-clean, but duplicates ~900 lines of proof that must then be maintained twice. Recommended
only if the freeze is treated as absolute.

### 4.3 Housekeeping in the follow-up ticket

Three declarations stop using some binders after the swap (Lean linter warnings; the repo's
standard is zero warnings):

| declaration | keeps |
|---|---|
| `fixedPoints_tame_inertia_eq_zero` (`Trace.lean:233`) | `hTnorm` only (drop `hgen`, `hTodd`; also `omit [Finite C]`) |
| `fixedPoints_zpowers_tame_eq_zero` (`Involution.lean:65`) | `hTnorm` only (drop `hgen`, `hTodd`; also `omit [Finite C]`) |
| `two_torsion_of_centralizer_eq_one` (`Involution.lean:171`) | `hgen`, `hTnorm` (drop `hTodd`; also `omit [Finite C]`) |

---

## 5. Mathlib inventory (task 2)

Mathlib pin: `lakefile.toml` rev `3a81e194…`, toolchain v4.31.0-rc2.

**Present and usable**

| what | exact name | module |
|---|---|---|
| projectivity API | `Module.Projective`, `Module.Projective.of_free`, `Module.Projective.of_split`, `Module.Projective.of_lifting_property{,',''}`, `Module.Projective.directSum` | `Mathlib.Algebra.Module.Projective` |
| semisimple ⇒ projective | `Module.projective_of_isSemisimpleRing` (alias `Module.projective_of_semisimple_ring`) | `Mathlib.RingTheory.SimpleModule.InjectiveProjective` |
| Maschke (invertible order) | `LinearMap.equivariantProjection`, `LinearMap.equivariantProjection_condition`, `MonoidAlgebra.exists_leftInverse_of_injective`, `MonoidAlgebra.Submodule.exists_isCompl`, `instance : IsSemisimpleModule k[G] V`, `instance : IsSemisimpleRing k[G]` (all under `[Field k] [Finite G] [NeZero (Nat.card G : k)]`) | `Mathlib.RepresentationTheory.Maschke` |
| every rep projective when `|G|` invertible | `Rep.instProjective`, `FDRep.instProjectiveOfNeZeroCastCard` | `Mathlib.RepresentationTheory.FinGroupCharZero` |
| restriction preserves projectives | `Rep.instPreservesProjectiveObjectsActionModuleCatSubtypeMemSubgroupResSubtype` (`(Action.res _ S.subtype).PreservesProjectiveObjects`) | `Mathlib.RepresentationTheory.Coinduced` |
| induction/coinduction + adjunctions | `Rep.ind`, `Rep.indResAdjunction`, `Rep.coind`, `Rep.resCoindAdjunction`, `Rep.resIndAdjunction`, `Rep.coindResAdjunction`, `Rep.indCoindIso` (finite index) | `Mathlib.RepresentationTheory.{Induced,Coinduced,FiniteIndex}` |
| untwisting the regular module | `Rep.leftRegularTensorTrivialIsoFree : leftRegular k G ⊗ trivial k G (α →₀ k) ≅ free k G α` | `Mathlib.RepresentationTheory.Rep.Basic:920` |
| Shapiro, group cohomology | `groupCohomology.*`, `Mathlib.RepresentationTheory.Homological.GroupCohomology.{Shapiro,FiniteCyclic,LongExactSequence}`, `isZero_groupCohomology_succ_of_subsingleton` | — |
| Sylow, `IsPGroup` | `Sylow`, `Sylow.not_dvd_index`, `IsPGroup.exists_card_eq` | `Mathlib.GroupTheory.Sylow` |

**Absent (searched: grep over mathlib + the vendored `ClassFieldTheory` package for
`Higman`/`relative projectiv`/`relatively projective`/`Clifford theory`/`vertex of a module`
— zero hits; plus `leansearch` and `leanfinder` semantic queries)**

* **Higman's criterion / relative projectivity / relative trace `Tr_H^G`** — nothing. This is the
  step the repo supplies itself as `regular_summand_of_subgroup_summand` (`Trace.lean:81`).
* **Rim's theorem** ("`M` projective over `𝔽_p[P]`, `P` Sylow ⟹ `M` projective") — nothing;
  the converse direction (restriction preserves projectives) is the only one mathlib has.
* **Vertices, sources, Green correspondence, blocks/defect** — nothing.
* **Clifford theory** (isotypic decomposition under a normal subgroup, stabilizers, induction
  from the stabilizer) — nothing.
* **Modular (char `p ∣ |G|`) representation theory generally** — nothing beyond the semisimple
  case.

**Why mathlib's Maschke cannot be used here.** `LinearMap.equivariantProjection` averages with
`1/|G|` and requires `IsUnit (Fintype.card G : k)`. Our `|C|` is even and `k = 𝔽₂`. The repo's
`regular_summand_of_subgroup_summand` is the char-`p` relative version: it sums over a
transversal of an **odd-index** subgroup and uses `odd_nsmul_eq_self` — no division anywhere.
The same trick appears in `LocalKummer.inflationVanishes_of_oddNormal`.

**Verdict on a mathlib-native route.** Building Higman + Clifford from mathlib primitives
(Rep-category adjunctions and `leftRegularTensorTrivialIsoFree` make the "summand of a free
module" bookkeeping feasible) is a genuine 1 000–2 000-line project, and would still need the
`V|_P`-freeness input. The repo's existing elementary route is strictly cheaper and is already
done. **Do not re-derive via mathlib.**

---

## 6. Follow-up ticket spec

> **AX5-a — general-`q` ramified-simple projectivity (`Lemma 6.11` at `q_K = 2^f`)**
> **model** opus · **files owned** `GQ2/Dyadic/Projectivity.lean` (new), plus the approved
> in-place edits to `GQ2/RegularSummand/Trace.lean`, `GQ2/RegularSummand/Involution.lean`
> · **depends on** owner/orchestrator approval of the §4.2 edit list (nothing else; no F-lane
> dependency — the `T_q`-marking corollary can be added later by F3 or by this ticket once
> `GQ2/Dyadic/TameBoundary.lean` exists) · **est.** 1–2 h.
>
> Content: (a) the four leaves of §4.1 + `lemma_6_11_of_tame_pair_pow` in the new file;
> (b) the §4.2 hypothesis swap + two name-preserving wrappers + the §4.3 binder cleanups;
> (c) acceptance: full `lake build` green, `scripts/check_axioms.sh` clean (check 5 capstone
> prints unchanged), `#print axioms GQ2.Dyadic.lemma_6_11_of_tame_pair_pow` = std-3, zero
> warnings, `SORRY_ALLOWLIST` untouched, `EXPECTED_AXIOMS` untouched.
>
> Cross-lane notes: F3 should reuse `tame_odd_order_pow`/`tame_zpowers_normal_pow` for the
> finite-image half of packet Lem. 3.1/3.2 rather than reproving them (the profinite `T_q`
> statements remain F3's). LG4 consumes the output as a plain theorem — **no hypothesis binder,
> no `DeepUnitPackage` field** for projectivity.

Naming: keep `GQ2.Dyadic` namespace for the new file; the packet's `RamifiedSimple.projective`
row in any trust-boundary table should be marked **"proved, not assumed"** when AS5 writes
`docs/dyadic/literature-axioms-dyadic.md`.

---

## 7. Decomposition: what is mathlib-free vs new (task 4, tradeoff view)

| sub-lemma | source | cost |
|---|---|---|
| Sylow-2 of a tame image is cyclic | repo `isCyclic_of_isPGroup_two_of_tame` | done, `q`-free after swap |
| `V^{⟨t⟩} = 0` for ramified simple | repo `fixedPoints_{tame_inertia,zpowers_tame}_eq_zero` | done, `q`-free after swap |
| no central 2-torsion (`O₂ = 1` linchpin) | repo `two_torsion_of_centralizer_eq_one` | done, `q`-free after swap |
| `#V^ω ^ 2 ≤ #V` (involution bound, 𝔽₂-rational trace element) | repo `involution_fixedPoints_sq_le_of_tame_pair` | done, already exponent-generic |
| Jordan concavity ⇒ `#V^P ^ |P| ≤ #V` | repo `card_fixedPoints_pow_le_of_half` | done, `q`-free |
| counting criterion ⇒ `V|_P` free | repo `free_of_card_fixedPoints_pow_le` | done, `q`-free |
| Higman/Rim odd-index relative trace | repo `regular_summand_of_subgroup_summand` | done, `q`-free (**not in mathlib**) |
| `Hom(V,−)`-exactness consequence | repo `equivariant_lift_of_regular_summand` | done, `q`-free |
| tame inertia odd at general `q` | **new**, §4.1 `tame_odd_order_pow` | ✓ typechecked |
| `⟨t⟩ ◁ C` at general `q` | **new**, §4.1 `tame_zpowers_normal_pow` | ✓ typechecked |
| general-`q` entry point | **new**, §1.2 | ✓ typechecked |

Nothing on this list needs mathlib machinery that does not exist; the only mathlib-shaped gaps
(Higman, Clifford) were already routed around by the ℚ₂ development.

---

## 8. If the owner wants an axiom anyway

Not recommended, and not needed — but for completeness: an axiom here would have had to read

```lean
axiom ramifiedSimple_projective {C : Type} [Group C] [Finite C] … : (split-summand statement)
```

i.e. it would assume a statement that is *provable in this repository today*. That conflicts with
the axiom-hygiene rule recorded in `GQ2/Foundations/Axioms.lean`: "Each axiom represents a
**published mathematical input** used by the paper; the paper-specific propositions and theorems
are proved elsewhere in the library" — and Lemma 6.11 is by the repo's own note (`RegularSummand.lean:26`)
*not* a single published theorem but the paper's own assembly of Clifford + Higman. It would
also land in the weakest of the file's three faithfulness classes ("composite project
interfaces", alongside B3c/B8/B11a), and the campaign's own precedent runs the other way: five
former axioms (B7', B11b, B12, B13, and effectively B9) were discharged as same-name theorems,
census 15 → 9. Census would go **9 → 10** for no reason.
Citations one would have used, for the record — usable in the new file's docstring:

* D. G. Higman, *Modules with a group of operators*, Duke Math. J. **21** (1954), 369–376
  (relative projectivity / the trace criterion). Already cited in `GQ2/RegularSummand.lean:26`.
  Journal/volume/year/pages: **UNVERIFIED** at page level here (no network access in this
  ticket); the repo has carried this citation since the ℚ₂ campaign.
* A. H. Clifford, *Representations induced in an invariant subgroup*, Ann. of Math. (2) **38**
  (1937), 533–550. Same status (**UNVERIFIED** at page level).
* D. S. Rim, *Modules over finite groups*, Ann. of Math. (2) **69** (1959), 700–712 —
  **UNVERIFIED**; the standard reference for "projective over a Sylow ⟹ projective", but the
  precise theorem number was not checkable here.
* C. W. Curtis and I. Reiner, *Methods of Representation Theory* I, §19 (relative projectivity;
  Higman's criterion is in the 19.x range) — **UNVERIFIED theorem number**; the AX5 brief's
  suggested "Thm 19.2" could not be confirmed. Do not cite a number without page-checking.

Since AX5 lands as a theorem, none of these enters the trust boundary; they belong in the
new file's docstring as attribution only, matching `GQ2/RegularSummand.lean`'s existing note
that "no single literature theorem states it — the paper assembles it from Clifford and Higman
plus elementary facts".

---

## 9. Open questions for the orchestrator / owner

1. **Approve the §4.2 in-place edit** to `GQ2/RegularSummand/{Trace,Involution}.lean` (plan A6
   requires a design memo to list the edits — this section is that list), or choose the §4.2
   fallback (duplicate the 922-line chain into `GQ2/Dyadic/Projectivity.lean`).
2. **Ownership of the two tame leaves**: this memo puts `tame_odd_order_pow` /
   `tame_zpowers_normal_pow` in `GQ2/Dyadic/Projectivity.lean` (they are finite-image facts).
   F3's `GQ2/Dyadic/TameBoundary.lean` proves the *profinite* `T_q` analogues (packet Lem. 3.1/3.2)
   and should import rather than duplicate. Orchestrator to confirm the direction.
3. **LG4 briefing correction**: the packet row "…so isotypic functors *and inflation–restriction*
   are exact" over-attributes. LG4's `InflationVanishes` analogue must be retyped from
   `GQ2/LocalKummer.lean:493/587` (coprime averaging over odd inertia), whose ℚ₂ bricks
   `odd_orderOf_tameInertia` (`:382`) and `tameInertia_normal` (`:409`) hard-code the `q = 2`
   relation via `tame_relation` — they need the same two leaves of §4.1. That is a *second*
   consumer of this ticket's output, currently unlisted on the board.
4. **AX5's board row** should lose its "(+`GQ2/Dyadic/Projectivity.lean` if proved)" conditional
   and become a plain theorem ticket; the AX-lane census-flip protocol (`b9a-tickets.md`
   checklist, `EXPECTED_AXIOMS` bump, `docs/literature-axioms.md` row) **does not apply** —
   nothing to flip.
