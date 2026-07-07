# P-15f handoff — Lemma 6.17 (`lemma_6_17_dim` / `lemma_6_17_vanish`) and the P-15f6 count

**Read this first** to continue P-15f without prior session context.  Everything here is in the
repo; nothing depends on session memory.  All declarations named below are **`#print axioms` ⊆
std-3** (`propext, Classical.choice, Quot.sound`) unless a B-axiom is explicitly noted, and the
whole library builds green (`lake build`, guard `scripts/check_axioms.sh` green, census 15).
`lemma_6_11`'s `sorryAx` enters **only** at the eventual f8 splice (see §6), never in the bricks
below.

The umbrella `lemma_6_17_dim` (`#X₊² = #H¹`) and `lemma_6_17_vanish` (`Q⁰_loc|X₊ = 0`) live in
`GQ2/SectionSix.lean` as `sorry`s; their machinery is **downstream** in `GQ2/LocalKummer.lean`
etc., so closure needs a statement-move (the 6.18ram pattern — see §6).

---

## 1. What is landed (all std-3, in the repo)

### The (94) arithmetic leaf — PROVED, no new axiom  (`GQ2/HilbertLedger.lean`, Tier 5)
The paper's eq. (94) Hilbert-symbol orthogonality is **not** a numbered theorem in any provided
text (FV Ch. VII §4 has only Exercises 4c/5b; O'Meara §63 assembles it), so per the user's
"no exercise-grade axioms" directive it was **proved**:
* `normForm_mul`, `normForm_inv`, `normForm_of_deep`, `normForm_neg_one_of_deep` — **std-3
  sorry-free**: a deep unit is a value of `x² − a·y²` (Brahmagupta composition + a contraction
  descent ending in the Local Square Theorem `sq_of_near_one`).
* `cup_deep_deep`, `cup_deep_neg_one`, `cup_deep_self` — **std-3 ∪ {B11a}** (`= deep ⟂ deep`,
  `deep ⟂ −1`).  `cup_of_normForm` was sharpened to consume `hilbertSymbol_normCriterion_finiteDyadic`
  (B11a) directly, so B11b is out of every downstream trace.
* Reference (line-verified against `references/`): the sharp filtration-orthogonality is FV
  *Local Fields and their Extensions* Ch. VII §4 (Ex. 4c/5b, `p>2` phrasing; §4 proves the
  underlying explicit formula for `p=2` too) and the framework theorem FV Ch. IV §5 Thm (5.2).
  See `docs/p15f1-axiom-proposal.md` §4.3.

### The deepClasses ↔ kummerClassK bridge  (`GQ2/LocalKummer.lean`)
* `deepClass_eq_kummerClassK` (**std-3**) — over a finite `k`, a deep class in
  `H¹(G_k,𝔽₂)` is `kummerClassK k a` for a genuine deep unit `a`.  Uses
  `InfiniteGalois.fixedField_fixingSubgroup` (`IsGalois ℚ_[2] ℚ̄₂` is inferred free) +
  `kummerCocycleFun_neg`.
* `cup_deepClasses` (**std-3 ∪ {B11a}**) — the (94) orthogonality in `deepClasses` vocabulary
  (the shared f1-isotropy / f2-orbit leaf).
* `norm_sub_one_lt_of_isDeepUnit` — `IsDeepUnit N A ⟹ ‖A−1‖ < ‖2‖`.

### Corestriction descends to H²  (`GQ2/CorestrictionCohomology.lean`)
* `lTrans_mul` — the transversal 1-cocycle identity, **general (no normality)**.
* `cor2Fun_dOne` — `cor²(δ¹c) = δ¹(cor¹ c)`: corestriction commutes with the differential.
  The cochain heart of the f2 per-orbit vanishing (`H2ofFun(cor2Fun(cup))` → 0 once the scalar
  cup does).  *Continuity* → B2-membership is still needed for the full H²-vanishing (a small
  step, deferred).

### The P-15f6 counting stack  (see §2 for the architecture)
* **f5 — `GQ2/HomCounting.lean`** (all std-3): `equivHoms C V W : AddSubgroup (V →+ W)`,
  `postCompHom`, `card_ker_postCompHom`, **`card_equivHoms_of_exact`** (the multiplicativity
  `#Hom_C(V,W) = #Hom_C(V,W')·#Hom_C(V,W'')` over an equivariant SES, surjectivity from the
  banked `equivariant_lift_of_regular_summand`), `card_equivHoms_of_subsingleton`,
  `card_equivHoms_congr`.
* **f6 brick i — `GQ2/KummerFiltration.lean`** (all std-3): `kummerDepth k π j`
  (`kummerClassK`-image of `depthUnits j`, an `AddSubgroup`), `kummerDepth_antitone`,
  `kummerDepth_eq_bot` (dies at `j ≥ 2e+1` — the f5-iteration endpoint), and
  **`coe_kummerDepth_deep`** (`(kummerDepth k π (e+1) : Set) = deepClasses k.fixingSubgroup`).
  B13 data (`π∈k`, `‖2‖=‖π‖^e`, discreteness) enter as hypotheses; file is axiom-free.
* **f6 brick ii — `GQ2/LocalKummer.lean` `ConjAction` section** (all std-3): the `conjAct`
  algebra (`conjMap_mul`, `conjAct_add`, `conjAct_zero`, `conjAct_comp`, `conjAct_one`,
  `conjAct_inner`, `conjAct_ker`) and **`conjModule ρ hρsurj : DistribMulAction C (H¹(N,𝔽₂))`**
  (`c•ξ := conjAct ρ (surjInv c) ξ`; `@[reducible]`, `letI`'d) + `conjModule_smul_of_lift`.
* **f6 brick iii-a — `GQ2/AdmissibleCount.lean`** (all std-3): `dualModule : DistribMulAction C
  (V →+ 𝔽₂)` (`(c•φ)v = φ(c⁻¹•v)`), `fam_equivariant`, **`admissibleFamEquiv : AdmissibleFam ρ ≃
  equivHoms C (V→+𝔽₂) (H¹(N))`**, `card_admissibleFam_eq` (`#AdmissibleFam = #equivHoms`).
* **f6 brick iii-b (PARTIAL) — `GQ2/AdmissibleCount.lean`**: `deepClassesSubgroup N :
  AddSubgroup (H¹(N,𝔽₂))` (deepClasses closed under 0/+/neg) and `kcf_conj`
  (`κ_β(g⁻¹ng)=κ_{g·β}(n)`).  **Blocked** — see §4.

---

## 2. Architecture: the balance route (why the full graded count is NOT needed)

Paper §6.3 p.34 proves the **dimension** clause (f1) by the **graded route** (NOT isotropy):
`H¹(ℚ₂,V) ≅ Hom_{H_V}(V^∨, M_K)`, `Hom(V^∨,−)` exact (Lemma 6.11), Hilbert duality pairs depth
`j`↔`2e−j`, self-duality `V≅V^∨` ⟹ equal multiplicities, middle `j=e` empty (Lemma 6.10).

**Key simplification (this session).** `dim_deepPart_of_balance` (banked, `LocalKummer`) needs
only the **balance** `#X₊ = #(H¹/X₊)`.  Via **one** f5 exactness step on the SES
`0 → deepClasses → H¹(N) → H¹(N)/deepClasses → 0` (`deepClasses = kummerDepth(e+1)`, brick i),
the balance reduces to the **duality** `#Hom(V^∨,U_{e+1}) = #Hom(V^∨,M_K/U_{e+1})`.  So the
full `DeepKummerData` graded `card_fam`/`card_deepFam`/(93) machinery is **unnecessary**; the
duality is exactly **f7**.

The connecting count identities (all banked):
```
#AdmissibleFam = #equivHoms C V^∨ (H¹N)        -- card_admissibleFam_eq  (brick iii-a)
#AdmissibleFam = #H¹(ℚ₂,V)                     -- card_H1_eq_card_fam    (needs hinf/hext)
#deepPart      = #{deep families}              -- card_deepPart_eq_card_deepFam
```
`hinf`/`hext` are dischargeable: `inflationVanishes_ramifiedTame` + `familiesExtend_of_card_le`
(both banked; need `hsurj`/`hgen` profinite plumbing).

---

## 3. The remaining f6 assembly (mechanical once §4 is unblocked)

1. **`conjAct_deepClasses`** — the `conjModule`-invariance of `deepClasses`.  Math is done:
   `conjAct ρ g [κ_β] = [κ_{g·β}]` (via `conjAct_h1ofFun` + `kcf_conj`), and `g·A` is a deep
   unit (`ker ρ` normal ⟹ `g·A` stays `N`-fixed; `‖g·b‖ = ‖b‖ < 1` by `GQ2.norm_galois`).
   **Only the §4 instance issue blocks it.**
2. **Subgroup / quotient `C`-actions**: give `↥(deepClassesSubgroup)` the restricted `conjModule`
   action (from `conjAct_deepClasses`) and `H¹(N)⧸deepClassesSubgroup` the induced action —
   these are f5's `W'` and `W''`.
3. **One `card_equivHoms_of_exact`** on that SES (`j` = inclusion, `π` = `QuotientAddGroup.mk`,
   `hexact`, `hπsurj`; the regular-summand package for `V^∨` comes from `lemma_6_11` at `V^∨` —
   this is where `sorryAx` will enter at f8, not before).
4. **Deep-families bridge**: `{ξ : AdmissibleFam // ∀φ, ξ.fam φ ∈ deepClasses} ≃ equivHoms C V^∨
   (deepClassesSubgroup)`, giving `#{deep families} = #equivHoms(V^∨, deep)`.
5. **Assemble**: steps 3–4 + `card_admissibleFam_eq` + `card_deepPart_eq_card_deepFam` + Lagrange
   ⟹ `balance ⟺ duality`.  Hand the duality to **f7**; the DeepKummerData/statement-move is **f8**.

Estimate: ~120 instance-heavy lines, gated on §4.

---

## 4. ⚠ THE CURRENT GATE: the `AbsGalQ2` / `Kummer.GaloisGroup ℚ_[2]` instance bridge

`AbsGalQ2` and `Kummer.GaloisGroup ℚ_[2]` are the **same type** (`Kummer.lean:322`,
`GaloisGroup ℚ_[2] = Field.absoluteGaloisGroup ℚ_[2] := rfl`) but carry **different `Group`
instances**: `Field.instGroupAbsoluteGaloisGroup` vs `AlgEquiv.aut`.  Consequences that blocked
`conjAct_deepClasses`:
* `deepClasses`, `conjMap`, and the `•`-action on `ℚ̄₂` are all stated in the **`GaloisGroup`**
  view; `ρ.toMonoidHom.ker : Subgroup AbsGalQ2` is in the **`AbsGalQ2`** view.
* `g • x` for `g : AbsGalQ2`, `x : ℚ̄₂` fails **`HSMul` synthesis** (the field action is
  registered only on `GaloisGroup`).  Making `g : Kummer.GaloisGroup ℚ_[2]` fixes the action but
  then `rw [conjAct_h1ofFun …]` produces an **ill-typed motive at `instances` transparency** on
  the `… ∈ deepClasses ρ.ker` membership (the `Subgroup`-instance mismatch on `ρ.ker`), and
  `conj_mem_ker`/`hgAfix` mix `m : AbsGalQ2` with `g : GaloisGroup` in `g⁻¹*m*g`.

**Note**: `deepClass_eq_kummerClassK`, `deepClassesSubgroup`, and `kcf_conj` all compile fine —
they don't cross the boundary the same way (`deepClassesSubgroup` is stated over a general
`N : Subgroup (Kummer.GaloisGroup ℚ_[2])`; `kcf_conj` is pure `GaloisGroup`).  The boundary bites
only when a lemma **simultaneously** touches `conjAct ρ g` (needs `g : AbsGalQ2`) and `g • (A:ℚ̄₂)`
(needs `g : GaloisGroup`).

**Resolution ideas** (pick one; likely recurs, so worth a small standalone brick):
* A `change`/transport lemma exhibiting `ρ.toMonoidHom.ker` in the `Kummer.GaloisGroup ℚ_[2]`
  view (an `AddSubgroup`/type identity), so `deepClasses`/`conjAct` see one consistent instance.
* Or restate `conjAct_deepClasses` **entirely** in `GaloisGroup` vocabulary, bridging
  `conj_mem_ker` (whose `ρ` is `AbsGalQ2`) once at the boundary.
* Or add `AbsGalQ2`-side `HSMul`/`MulAction` on `ℚ̄₂` + `map_inv`/etc. simp lemmas so both views
  reduce; check whether `Field.instGroupAbsoluteGaloisGroup` and `AlgEquiv.aut` are
  `@[reducible]`-defeq (if so, a targeted `set_option … reducible` in the proof may suffice).

---

## 5. Lean gotchas banked this effort (save the next session time)

* **Instance diamonds**: Mathlib's trivial *codomain* action `DistribMulAction M (A →+ B)`
  clashes with `dualModule` (the intended dual action) — `letI` beats it.  `DomMulAct` (`Mᵈᵐᵃ`)
  is Mathlib's domain action but indexed by `Cᵈᵐᵃ ≠ C`, so it doesn't fit `equivHoms C`.
* **`•` (letI instance) vs `.toSMul.smul` (explicit)** do **not** `rw`-match across a `letI`
  diamond.  Prove such equalities by a **`calc` through defeq** (e.g. `ρg • x = conjAct ρ
  (surjInv(ρg)) x` is `rfl` by `conjModule` def) + `conjAct_ker`, not `rw [show …] at h`.
* A class-typed `def` (a `DistribMulAction`/`MulAction`) must be **`@[reducible]`** (`conjModule`,
  `dualModule`).
* `add_right_eq_self`/`self_eq_add_right` were renamed out — use `add_left_cancel`.
* `push_cast; ring` FAILS on `AbsGalQ2` (a group, not a ring) — use `group`, or
  `simp only [Subgroup.coe_mul, Subgroup.coe_inv]` for subgroup-product coercions.
* Two `h1_add_self`: `GQ2.DeepPart.h1_add_self` (for `V`) vs `GQ2.h1_add_self` (for `ZMod 2`) —
  qualify.  `H1ofFun_add`, `kummerRestrict_mem_Z1` live in `GQ2.DeepPart`.
* `kcf`'s `if` needs `classical` in scope before `simp only [kummerCocycleFun]`.
* Bridging `conjAct` to `H1comap` for free additivity does **not** work cleanly
  (`QuotientAddGroup.map_mk` won't match `H1mk = mk'`; `continuous_id` coercion mismatch) — use
  the direct route via banked `H1ofFun_add`.

---

## 6. Pointers to the rest of P-15f

* **f1 (`lemma_6_17_dim`)** — the **dim clause uses the graded route, NOT isotropy** (route
  correction, `docs/p15f1-dimcount-scoping.md`).  Split into P-15f5 (✅ DONE = the f5 engine),
  P-15f6 (this doc), P-15f7 (the duality + `hmid` via Lemma 6.10), P-15f8 (DeepKummerData
  assembly + the statement-move splice: statement is upstream in `SectionSix`, machinery
  downstream in `LocalKummer` — move the statement out or reroute `DeepPart.prop_6_18_ramified`'s
  citation, à la the 6.18ram pattern).
* **f2 (`lemma_6_17_vanish`)** — the **monomial expansion** (`docs/p15f2-scoping.md`).  6.14,
  6.15 (free+square+**involution**, all banked/sorry-free in `ShapiroLedger`), 6.16, the (94)
  leaves, the deepClasses bridge, and `cor2Fun_dOne` are in place.  Remaining: the regular-module
  `q∘p` orbit decomposition + the continuity → B2 step.
* **Lemma 6.11 (P-17e4, `GQ2/RegularSummand.lean`)** — **NOT discharged**: `#print axioms
  GQ2.lemma_6_11` still shows `sorryAx`.  P-17e4 *assembled* it from the odd-index Sylow relative
  trace and reduced the sorry to a single kernel `sylow_free_of_ramified` (`V|_P ≃+ 𝔽₂[P]^r`
  equivariantly — the pp. 29–30 weight-orbit freeness).  P-15f4 is a merge-pointer to P-17e4.
* Axiom census is **15**; f6/f7 may need a user-approved B13-(F2) or FV-Thm-(5.2) leaf (flagged
  in the P-15f6/f7 board rows) — **do not add axioms without approval**.

---

## 7. Session update — the §4 gate is RESOLVED; the **f6 assembly is COMPLETE** (branch `p15f6-conjact-deepclasses`)

This session **broke the §4 gate AND completed the entire f6 assembly** (steps 1–5).  All new
declarations are **`#print axioms` = std-3** (`GQ2.AdmissibleCount` builds green, sorry-free).
Work is on branch **`p15f6-conjact-deepclasses`** (not merged to master).  The f6 output is
**`card_deepPart_sq_of_duality : #X₊² = #H¹(ℚ₂,V)`** from the duality (f7) + package (f8) +
`hinf`/`hext` (banked) — see the "Step 3 + step 5 — DONE" subsection below.

### Landed (all std-3, in `GQ2/AdmissibleCount.lean`)
* **`conjAct_deepClasses`** (§3 step 1 / the §4 gate) — `conjModule`-invariance of `deepClasses`.
* **`conjActHom`, `conjModuleDeep`** (§3 step 2) — the restricted `conjModule` action on
  `↥(deepClassesSubgroup (ker ρ))` (f5's `W'`).
* **`conjActQuotHom`, `conjActQuotHom_mk`, `conjModuleQuot`** (§3 step 2) — the induced action on
  `H¹(N) ⧸ deepClassesSubgroup` (f5's `W''`), via `QuotientAddGroup.map`.
* **`deepFamEquiv`, `card_deepFam_eq`** (§3 step 4) — `#{deep families} = #equivHoms C V^∨
  deepClassesSubgroup`.  Together with the pre-existing `card_admissibleFam_eq` this gives two of
  the three counts for the balance⟺duality reduction.

### The §4-gate technique (reuse it — the view mismatch recurs on EVERYTHING touching `ρ.ker`)
`AbsGalQ2` (`= Field.absoluteGaloisGroup ℚ_[2]`, a semireducible `def`) and
`Kummer.GaloisGroup ℚ_[2]` (`= ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂`, a reducible `abbrev`) are the SAME type but their
`Group` instances (`Field.instGroupAbsoluteGaloisGroup` vs `AlgEquiv.aut`) are defeq only at
`.default`, **NOT at `instances` transparency**.  Consequences and the fixes that WORK:
1. **field action `g • x` on `ℚ̄₂` fails `HSMul` synthesis for `g : AbsGalQ2`** (instance search
   won't unfold the `def`).  → **Take `g : Kummer.GaloisGroup ℚ_[2]`** (the reducible view);
   `conjAct ρ g` / `conj_mem_ker ρ g` still accept it by defeq.
2. **`rw` under `∈ deepClasses ρ.ker` fails the motive check** (forces the `AlgEquiv.aut` view). →
   **Build the deep-class witness with `refine ⟨…⟩` FIRST** (elaborated at `.default`), so the
   `conjAct_h1ofFun` rewrite lands on a plain `H1`-equation goal, never under `∈ deepClasses`.
3. **any `rw` touching `conjAct ρ g` needs `g : AbsGalQ2` in the motive but `g • β` needs
   `GaloisGroup`** — irreconcilable in one `rw`. → **use a `calc` (pure `Eq.trans`, no motive)**;
   prove `_mk`-style computation rules as **terms** (`QuotientAddGroup.map_mk _ _ … a`), not `rw`.
4. after a `congr`/`simp` leaves a stray `conjActHom`, **`show … = conjAct …`** to defeq-convert
   before `rw [← conjAct_comp]`.

### Step 3 (the `U_{e+1}` SES count) + step 5 (assembly) — DONE (the f6 assembly is COMPLETE)
The step-3 blocker (nested `.Normal`/`HAdd` resolution failing under the `ρ.ker` view clash — it
resolves at top level, `example … := inferInstance` compiles, but NOT in the position
`card_equivHoms_of_exact` needs it; `set Deep`/`haveI` did not fix it) was **cracked by an abstract
helper**:
* **`card_equivHoms_quotient_ses`** — the inclusion/quotient SES count stated over a **plain fvar**
  `Deep : AddSubgroup A` (A a finite 2-torsion `C`-module).  Over fvars, `Deep.Normal` and the
  quotient's `AddCommGroup`/`Finite` resolve cleanly (NO coercion, no view clash), so
  `card_equivHoms_of_exact` applies.  This IS the view-normalization brick §4 asked for.
* **`card_equivHoms_deepSES`** — instantiates it at `A := H¹(N)`, `Deep := deepClassesSubgroup (ker ρ)`,
  passing the `conjModule` actions as **NAMED instance args** (`(instA := conjModule …)`,
  `(instDeep := conjModuleDeep …)`, `(instQuot := conjModuleQuot …)`) so no resolution against the
  view-clashed types is attempted.  Yields `#Hom_C(V^∨,H¹N) = #Hom_C(V^∨,deep)·#Hom_C(V^∨,quot)`.
  KEY IDIOM: **name the instance binders in the abstract lemma, pass them explicitly at the
  concrete call** — this is the general recipe for any `deepClassesSubgroup`-typed instance arg.
* **`card_deepPart_sq_of_duality`** (step 5, the **f6 output**) — chains everything:
  `#H¹(ℚ₂,V) = #AdmissibleFam = #equivHoms(V^∨,H¹N) = #equivHoms(V^∨,deep)·#equivHoms(V^∨,quot)`
  [SES], `#deepPart = #deepFam = #equivHoms(V^∨,deep)`, and `hduality : #equivHoms(V^∨,deep) =
  #equivHoms(V^∨,quot)` collapses the product to a square ⟹ **`#deepPart² = #H¹(ℚ₂,V)`**.

All std-3, `GQ2.AdmissibleCount` builds green.  **What remains is NOT f6** — it's the three inputs
to `card_deepPart_sq_of_duality`: `hduality` (**f7** — graded Hilbert duality / self-duality
`V ≅ V^∨`), the `V^∨` regular-summand package (**f8** — `lemma_6_11`), and `hinf`/`hext` (banked:
`inflationVanishes_ramifiedTame` + `familiesExtend_of_card_le`).  Feed those and `lemma_6_17_dim`
closes via the 6.18ram statement-move.

---

## 8. P-15f7 session update — the ABSTRACT LAYER IS COMPLETE (`GQ2/DeepDuality.lean`, all std-3)

**Claimed + built by Fable, 2026-07-06, branch `p15f6-conjact-deepclasses`.**  f7's deliverable
is the f6 capstone's `hduality`; `GQ2/DeepDuality.lean` (registered in `GQ2.lean`) delivers it
**abstractly, with every arithmetic input as a hypothesis** — census untouched.

### The minimal route (a strict simplification of the paper's p. 34 computation)

Discovered at design time: the full graded (93) computation and the per-level (94) sharpness
are NOT needed.  With `P := Deep^⊥` (w.r.t. one invariant nondegenerate pairing `B` on
`M = H¹(N,𝔽₂)`) the chain

`#Hom(U, M/Deep) =[Hom-symmetry] #Hom(M/Deep, U) =[eU] #Hom(M/Deep, U^∨) =[curry]
#Hom(U, (M/Deep)^∨) =[ann(Deep) ≅ (M/Deep)^∨] #Hom(U, P) =[f6 SES at Deep ≤ P]
#Hom(U, Deep)·#Hom(U, P/Deep) =[inertia-kill on P/Deep ⊆ E/Deep] #Hom(U, Deep)`

needs exactly: **(H2)** `B` nondegenerate; **(H3)** `Deep ≤ Deep^⊥` (banked Tier-5!);
**(H4)** ONE sharp instance `Deep^⊥ ≤ E` (= (94)@(e+1)-⊆, `E` = `U_e`-classes `‖A−1‖ ≤ ‖2‖`,
π-free); **(H5)** conjugates of `t₀` (the inertia image) act trivially on `E/Deep` (Lemma
6.10's content; `e` odd + tame inertia order `e` in the paper).

### What is in `DeepDuality.lean` (all `#print axioms` = exactly std-3)

* §A `stabSubAction`/`stabQuotHom`(+`_mk`)/`stabQuotAction` — generic restricted/quotient
  actions on a `C`-stable `AddSubgroup` (abstract twins of f6's `conjModuleDeep`/`Quot`).
* §B `card_equivHoms_eq_one_of_conjSmulTrivial` — `t₀` nontrivial on simple `U` + all
  conjugates `d t₀ d⁻¹` trivial on `T` ⟹ `#Hom_C(U,T) = 1` (the closure
  `⟨(dt₀d⁻¹)u − u⟩` is `C`-stable ≠ ⊥ ⟹ ⊤; equivariant maps kill it).
* §C `equivHomsCurry`/`card_equivHoms_curry` — `#Hom(U, W^∨) = #Hom(W, U^∨)` (`dualModule`
  duals; `AddMonoidHom.flip`).
* §prod `card_equivHoms_prod_target`/`_source`, `card_equivHoms_congr_source`.
* §𝔽₂ `exists_functional_ne_zero` (local copy — avoids the heavy `LocalLiftingDuality`
  import chain), `dualHom_surjective_of_injective` (via
  `LinearMap.exists_leftInverse_of_injective` over `ZMod 2`).
* §eval `precompHom`(+equivariance), `evalDualHom`, `evalDualEquiv` (double-dual iso:
  separation + `card_addHom_zmod2` twice) + equivariance.
* §split `splitProdEquiv` (split pair ⟹ `W ≃+ U × ker ρ`, equivariant), `ker_stable`,
  `exists_section_of_epi` (lift `id` via banked `equivariant_lift_of_regular_summand`),
  `exists_retraction_of_mono` (dualize; `precompHom f` onto; lift `id_{U^∨}` with the
  `eU`-transported package; pull back through `evalDualEquiv` — `ρ∘f = id` via
  `evalU`-injectivity).
* §D **`card_equivHoms_comm`** — THE Hom-symmetry `#Hom_C(U,W) = #Hom_C(W,U)` for `U`
  simple/nontrivial/self-dual/packaged: strong induction on `#W` (∀-type-quantified aux),
  nonzero hom either direction ⟹ split `W ≅ U × K` (mono: kernel simple-kill;
  epi: range simple-kill), both counts factor, recurse (`2#K ≤ #W`).  This is the precise
  content of the paper's "self-duality ⟹ equal multiplicities".
* §E `pairPerp`(+`mem`/stability), `perpEquivDualQuot` (`ann(S) ≅ (M/S)^∨`; surjectivity =
  nondegeneracy count via `card_addHom_zmod2`) + `_mk` + equivariance.
* §F **`card_equivHoms_deep_eq_quot`** — the abstract `hduality`, hypotheses (H2)–(H5) + the
  `U`-side package/self-duality + `instDeep`/`instQ` as NAMED instance binders with
  `hjeq`/`hπeq` compatibility (the f6 idiom, so instantiation at `conjModuleDeep`/`Quot` is
  substitution).

### Remaining for f7 (the instantiation surface) — ⚠ THE LEAF DECISION LIVES HERE

Instantiate at `M := H¹(N,𝔽₂)` (`conjModule`), `U := V^∨` (`dualModule`),
`Deep := deepClassesSubgroup`, `E := midClassesSubgroup` (define: `IsMidUnit` = the
`IsDeepUnit` idiom with `‖b‖ ≤ 1`, i.e. `U_e` in π-free norm vocabulary), `t₀ := (lift of
c tameTau)`.  Obligations:
1. `midClassesSubgroup` + `conjAct_midClasses` — mechanical mirrors of the deep versions
   (AdmissibleCount.lean), ≤ for <.
2. `ht₀U` — from 6.17's `hram : ∃ v, c tameTau • v ≠ v` transported to `V^∨` along the
   self-duality (or dualized directly: inertia nontrivial on `V ⟺ V^∨`).
3. `eU`/`heU` — from the invariant form: `v ↦ polar q v ·` (6.17's `(q,hq,hns,hinv)`
   package; `polarMuDual` is the `MuDual` flavor — an `(V →+ ZMod 2)`-flavored twin is a
   short build; bijective by `hns` + `card_addHom_zmod2`).
4. the package `(ι,r,…)` for `V^∨` — f8's `lemma_6_11` output (same hypothesis as everywhere;
   `sorryAx` enters only there).
5. **(H5)/hmid** — `conjAct_mid_sub_mem_deep`: for `g` residue-trivial on `K` (norm form:
   `∀ x` `N`-fixed with `‖x‖ ≤ 1`, `‖g•x − x‖ < 1`) and `ξ` a mid class,
   `conjAct ρ g ξ − ξ ∈ deepClassesSubgroup`.  DERIVABLE, no leaf: with `A = 1+2b` mid,
   `(g•A)/A = 1 + 2(g•b−b)/A` is DEEP by the inertia condition at `x := b`; class algebra
   via `kcf_mul_of_fixed` + the root-factoring trick of `deepClass_eq_kummerClassK`
   (`(β−δA)(β+δA) = 0`).  Then the conjugates-form follows since the residue-trivial set is
   conjugation-stable (`norm_galois`).  What remains ARITHMETIC here: `t₀`'s lifts are
   residue-trivial on `K` (tame inertia acts trivially on the residue field — needs the
   `BoundaryMaps`/`hfac` unpacking; possibly `e`-odd/tameness of `K/ℚ₂` enters HERE, as in
   the paper's 6.10).
6. **(H2) `hBnd` + (H4) `hsharp` — ✅ leaf decision RESOLVED (user-approved 2026-07-07,
   `docs/p15f7-axiom-proposal.md`; executed same day):**
   * `B` + `hBnd`: **B6 was base-generalized in place** (census-neutral, B9/B11 pattern) —
     `axiom tateDualityAt (G) … (hloc : IsLocalDualizingGroup G n) : TateDualityG G n` for
     `G` a finite-index local Galois group (`GQ2/TateDuality.lean` now has the
     group-parametric `MuDual`-action/`TateDualityG`/`IsLocalDualizingGroup`; the old
     `tateDuality` is re-derived as the `G_ℚ₂`-member `def`, so consumers are unchanged and
     axiom traces show `tateDualityAt`; `AxiomLedger` B6 entry swapped; NSW (7.2.6) covers
     arbitrary `p`-adic `k` verbatim).  At `K`: `B := inv_K ∘ cup` with `(1,1)`-perfectness =
     (H2); invariance is FREE (`Aut(ℤ/2) = 1` + cochain-level cup conj-equivariance, provable
     in-repo).  Instantiation needs the `G_K`-side `IsLocalDualizingGroup` witness (subgroup
     inclusion of `ker ρ`, finite index from `[K:ℚ₂] < ∞`) — plumbing, no leaf.  Symbol-side
     classical cross-refs (recorded in `literature-axioms.md`): FV IV §5 Prop (5.1)(1)(5)(6)(9),
     Corollary p. 145, Thm (5.2); O'Meara ITQF 63:13.
   * `hsharp` (`Deep^⊥ ≤ E` = (94)@(e+1)-⊆): **prove in-repo (approved plan of record)** —
     the counting route: `#Deep^⊥ = #M/#Deep` (perp machinery banked in `DeepDuality.lean`) +
     the isotropy instance `(U_e, U_{e+1}) = 1` (extend the Tier-5 Brahmagupta/contraction
     descent from deep×deep to base `a ∈ U_e`; budget `j + e ≥ 2e+1`, still at the
     `sq_of_near_one` threshold) + `#E/#Deep = 2^f` (B13 `card_gr` at `i = e` + the
     odd-depth-no-squares parity argument; classical parallels O'Meara 63:2/63:5/63:8/63:9).
     Fallback single-clause leaf ONLY on a second explicit user approval.
7. Assemble → `hduality` → feed `card_deepPart_sq_of_duality` (f6) → `lemma_6_17_dim`
   closes at f8 with the statement-move.

### §8 status update (2026-07-07, session 3): the K-level pairing is LANDED

`GQ2/DeepDualityK.lean` (NEW, registered): `ker_isLocalDualizingGroup` (std-3) →
**`tateDualityK`** (first consumer of the base-generalized `tateDualityAt`);
`zmodMuDualEquiv`; **`pairingK`** = `inv_K ∘ cup11(evaluation) ∘ H1congr` on
`H¹(ker ρ, 𝔽₂)`; **(H2) `pairingK_nondeg`** (`#print axioms` = std-3 + `tateDualityAt`
exactly); **(H1) `pairingK_conjAct` + `pairingK_conjModule`** (the literal `hBinv` shape) —
via `conjMap_mul_apply`/`conjMap_(inv_)conjMap`, `comp_conjMap_mem_B2(_iff)` (coboundary
transport), `conjAct_H1mk`, and `inv_H2mk_eq_of_comp_conjMap` (equation-hypothesis form —
NB the naive `F∘(c×c)`-pattern lemma hits a higher-order-unification `isDefEq` timeout at the
call site; the `hco : Fc.1 = fun p => F.1 (conjMap …)`-hypothesis form with
`(funext fun p => rfl)` at the call is the fix).  `GQ2/DeepDuality.lean` §H (U-side inputs):
`polarSelfDual`(+`_equivariant` from `hinv`), **`dualSelfDual`(+`_equivariant`) = `eU`/`heU`**,
**`exists_dualModule_smul_ne` = `ht₀U`**.  Item 1 (mirrors) was §G; items 2, 3 are now DONE;
item 6 executed (B6′).  **Remaining for f7**: (H4) sharp (approved counting route: perp-count
banked + `(U_e,U_{e+1})=1` Tier-5 descent extension + B13/(93)-at-`e` sizes), item 5 (the hmid
twist `conjAct_mid_sub_mem_deep` + `t₀`-lifts residue-trivial), the isotropy `k`-splice
(item: `cup_deepClasses`-compatibility of `pairingK` — needs `trivialCupPairing` vs
`cup11(evaluation)` coefficient-transport + the `k.fixingSubgroup = ker ρ` view plumbing),
and the final `card_equivHoms_deep_eq_quot` instantiation.

### §8 status update (2026-07-07, session 4): (H5) twist, (H3) splice, (H4) easy half LANDED

* **(H5)/hmid DONE, pure std-3** — `GQ2/DeepDuality.lean` §G′ (`MidTwist`):
  `IsResidueTrivial N g` (norm form: every `N`-fixed integral `x` moves `< 1`),
  `IsResidueTrivial.conj` (conj-stability via `norm_galois` + `conj_mem_ker`),
  **`conjAct_mid_sub_mem_deep`** (Lemma 6.10: `conjAct ρ g ξ − ξ` deep for `ξ` mid, `g`
  residue-trivial — 2-torsion + `kcf_mul_of_fixed` turn the difference into
  `[κ_{(g•β)β}]`, and the PRODUCT `(g•A)·A = 1 + 2(g•b + b + 2(g•b)b)` is a deep unit via
  the inertia estimate at `x := b`; `p = 2` turns the paper's division into a product — no
  root-factoring, no leaf), **`conjAct_surjInv_conj_mid_sub_mem_deep`** (the literal `hmid`
  at `conjModule`: ONE residue-trivial lift `g₀ : AbsGalQ2` of `t₀` covers all
  `d·t₀·d⁻¹`-conjugates via `conjAct_ker` + conj-stability).  Still hypothesis-side for f8:
  *tame-inertia lifts are residue-trivial* (`BoundaryMaps`/`hfac` unpacking).
* **(H3)/hiso DONE** — `GQ2/DeepDualityK.lean` §IsotropySplice: `kerToFixing`
  (+`_mul`, `continuous_`) under the POINTWISE `hker : x ∈ ker ρ ↔ x ∈ k.fixingSubgroup`
  (no subgroup-equality cast is ever formed); **`pairingK_deep_deep`** (destructure the deep tuples,
  re-form them over `k.fixingSubgroup`, apply Tier-5 `cup_deepClasses`, pull the `B²`-witness
  back along `kerToFixing` and through `muNTwoEquiv.symm` — the two cup cocycles are
  literally the same functions), wrapper **`deepClassesSubgroup_le_pairPerp_pairingK`** =
  `hiso`.  Ax: std-3 + B11a + tateDualityAt.
* **(H4) easy half DONE** — `(U_e, U_{e+1}) = 1` PROVED (no leaf):
  `GQ2/HilbertLedger.lean` `normForm_of_mid_aux`/`normForm_of_mid` (mid-base Brahmagupta
  descent: with `‖a−1‖ ≤ ‖2‖` the error contracts by the CURRENT depth `‖b−1‖/‖2‖` —
  self-referential budget `‖b−1‖·(‖b−1‖/‖2‖)^j < ‖4‖`, monotone along the iteration; FV
  Ch. VII §4 Ex. 4c at `(e, e+1)`) + `cup_mid_deep` (std-3 ∪ {B11a});
  `GQ2/DeepDualityK.lean` `norm_sub_one_le_of_isMidUnit`, `midClass_eq_kummerClassK`
  (`≤`-mirror of the deep bridge), `cup_midClasses_deepClasses`, **`pairingK_mid_deep`**
  (same splice as (H3)), wrapper **`midClassesSubgroup_le_pairPerp_pairingK`** =
  `E ≤ Deep^⊥`.
* **Remaining for f7**: the (H4) COUNTING half — `#Deep^⊥ ≤ #E`, whence `Deep^⊥ = E`
  (`AddSubgroup.eq_of_le_of_card_le` off the easy half) and `hsharp`.  Chain:
  `#Deep^⊥ = #((M⧸Deep)^∨) = #(M⧸Deep) = #M/#Deep` (Nat.card_congr `perpEquivDualQuot` +
  `card_addHom_zmod2` + Lagrange) vs `#E·#Deep ≥ #M` — the B12/B13 structural count
  (`kummerClassK_surjective` + `DyadicUnitFiltration.card_gr` + O'Meara 63:9-style
  square-depth bookkeeping).  Then the final `card_equivHoms_deep_eq_quot` instantiation
  (M := `H¹(ker ρ)` @ `conjModule`, U := `V^∨` @ `dualModule`, Deep/E :=
  deep/mid-`ClassesSubgroup`, B := `pairingK`, all inputs now named).
* Lean lessons this session: (i) inline `by rw [...]`-proofs of an argument whose expected
  type still contains METAVARS can capture them (`rw [hgsq]` matched `?y^2` and assigned
  `?y := g•β`) — hoist to a standalone `have` with concrete type; (ii) `(n : Kummer.GaloisGroup ℚ_[2])`
  ASCRIPTION on `n : ↥(ker-as-Subgroup-AbsGalQ2)` fails (coercion-insertion unifies at
  reducible) — use `n.1`/plain application (default-transparency defeq); (iii) lambdas
  inside a `+`-binop don't get the expected domain propagated — annotate binders; (iv) a
  goal produced by `rfl`-destructuring a definition carries the DEFINITION's instance-view —
  re-`show` it in your own view before `rw`-ing with your own lemmas.
