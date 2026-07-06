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

## 7. Session update — the §4 gate is RESOLVED; f6 bricks landed (branch `p15f6-conjact-deepclasses`)

This session **broke the §4 gate** and landed the remaining f6 bricks except the SES count.  All
new declarations are **`#print axioms` = std-3** (`GQ2.AdmissibleCount` builds green, sorry-free).
Work is on branch **`p15f6-conjact-deepclasses`** (not merged to master), commits `f1e35d3`,
`7d256e5`, `6206629`, `33ca7a1`.

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

### DEFERRED — step 3 (the `U_{e+1}` SES count) — the ONE remaining f6 blocker
`card_equivHoms_deepSES` (removed; full attempt in the git history of this branch, and its shape is
in the comment where it used to live) applies `card_equivHoms_of_exact` to
`0 → deepClassesSubgroup →ⱼ H¹(N) →π H¹(N)/deep → 0`.  **Everything is correct** —
`j = AddSubgroup.subtype` (`hjeq = fun c w => rfl`, `hjinj = Subtype.val_injective`),
`π = QuotientAddGroup.mk'` (`hπeq = fun c w => (conjActQuotHom_mk …).symm`,
`hπsurj = QuotientAddGroup.mk'_surjective`), `hexact` via `QuotientAddGroup.eq_zero_iff` +
`AddSubgroup.range_subtype`, `h2W = GQ2.h1_add_self`, package `(ι,r,hι,hr,hri)` + `Finite (H¹ N)`
as hypotheses.  **Blocker**: `(deepClassesSubgroup ρ.ker).Normal` and the quotient's `HAdd`
resolve at TOP level (`example … := inferInstance` compiles) but **FAIL in the nested position**
`card_equivHoms_of_exact` needs them (`instances`-transparency + the `ρ.ker` view clash).  `set Deep
:= …` + `haveI : Deep.Normal` did NOT fix it (a residual defeq mismatch surfaces at the engine call).
**Recommended fix = the standalone view-normalization brick from §4**: either (a) a transport lemma
exhibiting `deepClassesSubgroup ρ.ker` uniformly in ONE view, or (b) restate `deepClassesSubgroup`
(and `deepClasses`) directly over `Subgroup AbsGalQ2` so no coercion ever happens.  Once step 3
lands, step 5 is pure arithmetic:
`#H¹(ℚ₂,V) = #AdmissibleFam = #equivHoms(V^∨,H¹N) = #equivHoms(V^∨,deep)·#equivHoms(V^∨,quot)`
[SES], `#deepPart = #deepFam = #equivHoms(V^∨,deep)`, so `hduality : #equivHoms(V^∨,deep) =
#equivHoms(V^∨,quot)` ⟹ `#deepPart² = #H¹` (the f6 output; hand `hduality` to f7).
