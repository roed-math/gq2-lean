# P-13 note: the §5.13 normal-form / §5.15 duality statements need the pro-2 wild-core hypothesis

**Date**: 2026-07-04 · **Found by**: P-13 (building the §5.1 ledger) · **Status**: Pro2Core fix
**APPLIED** (commit `431cdff`); a **second, deeper tameness requirement** surfaced while proving —
see §7.  §§1–6 record the original (now-fixed) gap; §7 is the update.

## 1. The gap

The sorried statements `lemma_5_13_split`, `lemma_5_13_ramified`, `lemma_5_13_pairing_split`,
`lemma_5_13_pairing_ramified`, and `prop_5_15` (`GQ2/FoxHeisenberg.lean`) are **not provable from
their current hypotheses**.  They assume the tame-inertia condition (`htau : ∀ v, τ • v = v` for the
split case, resp. `V^T = 0` for the ramified case) but **omit the input that the marked wild
subgroup `⟨⟨x₀, x₁⟩⟩` acts trivially on the module** — the paper gets this from Lemma 5.12 applied
to the pro-2 core, and it is load-bearing for both the normal form and the wild Fox row.

Paper Lemma 5.13 is stated for a *"nontrivial simple **tame** `𝔽₂[C]`-module"*; "tame" is precisely
"the wild subgroup acts trivially", which the paper secures via Lemma 5.12 (simple char-2 modules
are tame) using that `⟨⟨x₀, x₁⟩⟩` is a 2-group (the admissibility clause `Pro2Core`).  That clause
never reaches the repo's `lemma_5_13_*` / `prop_5_15` signatures.

## 2. Concrete witness (airtight, for the split case)

`d⁰ t v = ![σ•v − v, τ•v − v, x₀•v − v, x₁•v − v]` (`FoxHeisenberg.d0`).  The `B¹`-half of
`lemma_5_13_split` claims

```
y ∈ B1w t  ↔  ∃ v, y = ![t.σ • v - v, 0, 0, 0].
```

Left-to-right forces, for every `v`, the 3rd and 4th coordinates of `d⁰ t v` to vanish:
`x₀ • v − v = 0` and `x₁ • v − v = 0`, i.e. **`x₀` and `x₁` act trivially on `V`**.  The hypothesis
`htau` gives only the 2nd coordinate (`τ • v − v = 0`).  Nothing in `(ht, hw, hV₂, hsimple, htau)`
forces `x₀` trivial — e.g. `C = S₃`, `V =` the 2-dimensional simple `𝔽₂[S₃]`-module, `x₀ =` a
3-cycle acts with order 3 — so the `↔` fails there.  (The `Z¹`-half fails for the same reason via
the wild row; see §3.)

## 3. Why the wild row needs it too

The `Z¹ = ker d¹` description uses Lemma 5.5's wild row `L_w = P·b + (P + S⁻¹)·d`.  Deriving that
closed form is the paper's Lemma 5.3(i) ("the first derivative of `h₀` is that of `x₀²`, namely
zero"), whose proof needs the wild generators to act trivially on the simple factor (Lemma 5.3
preamble: *"the marked wild subgroup acts trivially on every simple factor"*).  Without it, `h₀`'s
first derivative is not zero and the wild row is not `P·b + (P + S⁻¹)·d`.

By contrast the **tame row is unconditional**: from the proved `d1Fun_tame`, in the split case
(`htau`, `hV₂`) it collapses to `(d1Fun t x).1 = σ⁻¹ • x 1`, giving the `x 1 = 0` clause with no
wild-core input.  So exactly the wild/coboundary content is what needs the extra hypothesis.

## 4. Recommended fix

Add the admissibility clause to the leaf lemmas and to `prop_5_15`:

```
(hcore : t.Pro2Core)      -- IsPGroup 2 (Subgroup.normalClosure {t.x₀, t.x₁})
```

and derive trivial wild action from the **already-proved** `lemma_5_12`, instantiated at
`L = Subgroup.normalClosure {t.x₀, t.x₁}` (normal by construction; a 2-group by `hcore`; contains
`x₀, x₁`):

```
have hx : ∀ v : V, t.x₀ • v = v ∧ t.x₁ • v = v := …  -- lemma_5_12 hV₂ hsimple L L.normal hcore
```

For the general (non-simple) `prop_5_15`, `hcore` is a property of the marking `t` alone, so it
covers every simple subquotient in the composition-series dévissage — one hypothesis suffices.

*Lighter alternative*: assume the conclusion directly, `(hx : ∀ v, t.x₀ • v = v ∧ t.x₁ • v = v)`,
skipping the `lemma_5_12` hop.  More elementary, but less faithful to the admissibility data and it
does not advertise *why* the module is tame.

## 5. Ripple effects (why this is a user decision, not an overnight edit)

* `lemma_5_13_*` are **leaf** lemmas — unreferenced elsewhere — so free to re-sign.
* `prop_5_15` is consumed by the **proved** `cor_5_17_card` (`GQ2/FoxHeisenberg.lean:1674`).  Adding
  a hypothesis to `prop_5_15` forces `cor_5_17_card` (and, transitively, its own consumers) to
  supply it.  In the real assembly the marking is `Admissible`, which *includes* `Pro2Core`, so the
  data exists upstream; it just has to be threaded.  That signature change should be made
  deliberately with the §9 assembly (P-17) in view.

## 6. What is already unblocked

The §5.1 engine that these lemmas consume is landed and needs **none** of the above (commits on
`P-13`):

* `WordLift.pow_u` / `pow_g` — norm-of-power (the "norm projector" `P`);
* Lemma 5.2 — `classTwoCore`, `classTwoIdentity`, `classTwoIdentity_id` (the `h₀`-shadow engine);
* `HeisLift.commP_z_fiber` — the Heisenberg commutator symplectic `B`-form (Lemma 5.14's
  `[d₀,z₀]` contribution).

Once the hypothesis question in §4 is settled, the wild-row closed form (Lemma 5.5) and the
Hessian (Lemma 5.14) can be assembled from these plus the proved `lemma_5_12`.

## 7. Update (commit `431cdff`): fix applied, and a deeper tameness requirement

**Applied.** The §4 fix is in: `wild_acts_trivially` is proved (std-3), and `(hcore : t.Pro2Core)`
— plus the previously-missing `(hsimple : IsSimpleModTwo C V)` on the two pairing lemmas, and
`(hσ : ∃ v, t.σ • v ≠ v)` on `lemma_5_13_split` — is threaded through the 5.13 family, `prop_5_15`,
and the proved `cor_5_17_card`.  `lake build GQ2.FoxHeisenberg` green.

**Deeper finding — σ-tameness (`U = σ₂` trivial) is also required, and is a *further* input.**
Probing the proofs shows the paper's phrase "simple **tame** module" silently includes a condition
that neither `htau` nor `Pro2Core` provides: **σ's 2-primary part `U = σ₂` (`Marking.sigma2`) must
act trivially on `V`.**

* *Needed for truth, not just proof.*  `lemma_5_13_pairing_split` claims `mixedB = λ(c)`.  The `h₀`
  contribution collapses to `λ(c)` (via `classTwoIdentity`, i.e. `h₀ ↦ x₀²`) exactly when
  `g₀ = σ₂²` acts trivially on the coefficient group — i.e. `U` trivial.  On a simple module where
  `U` acts nontrivially, `h₀ ≠ x₀²` and the pairing differs.  The split normal form routes through
  the same `h₀`-shadow (Lemma 5.3(i): first derivative of `h₀` is zero), so it needs it too.
* *Not a consequence of simplicity.*  A general element's 2-part **can** act nontrivially on a
  simple `𝔽₂[C]`-module — e.g. `C = S₃ ≅ GL₂(𝔽₂)`, where an involution acts with order 2 on the
  2-dimensional simple module.  So "U trivial" is the genuine **tameness of σ** (arithmetically: σ
  is Frobenius and σ₂ lies in wild inertia), an input, not a theorem.  My earlier §2 analysis caught
  the *wild-core* half of tameness (x₀, x₁) but not this σ₂ half.
* *Recommended.*  Model "tame module" as a single clause that the full wild inertia — containing
  `x₀, x₁` **and** `σ₂` — acts trivially: e.g. add `(hU : ∀ v, t.sigma2 • v = v)` alongside
  `hcore`, or introduce a unified `IsTameModule t V` predicate bundling `htau`/`hcore`/`hU`.  This
  ties into how §9 supplies tameness from the arithmetic (P-17), so it is left as a deliberate
  design choice rather than picked here.

**Remaining proof machinery** (once tameness is fully modelled):

* *Wild row (Lemma 5.5)* — expand `wildValue.u` in `WordLift V C` via the landed `WordLift.pow_u`.
  With `σ₂, τ, x₀, x₁` all acting trivially, every ω₂-norm collapses to its mod-2 exponent
  (`WordLift.pow_u` with `g • v = v` ⇒ `∑ = k • v`), and the only surviving action is the `S⁻¹`
  from `x₁^σ` — giving `L_w = P·b + (P + S⁻¹)·d`.  Then `x 3 = 0` from `1 + S⁻¹` invertible
  (`hσ` + simplicity, via `V^S = V^C = 0`).
* *Hessian (Lemma 5.14)* — `wildValue.z` on x₀-supported reps: `h₀ ↦ λ(c)` (`classTwoIdentity`) plus
  the `[d₀,z₀]` symplectic term (`HeisLift.commP_z_fiber`); the latter vanishes in the split case
  since `P + 1 = 0` in char 2.
* *prop_5_16* needs axioms **B6/B7** (local Tate duality).  `Foundations/Axioms.lean` is frozen
  (no new axioms), so 5.16 stays sorried **by construction** — not a P-13 proof gap.
