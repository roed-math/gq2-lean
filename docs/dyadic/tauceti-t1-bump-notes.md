# T1 Mathlib-bump notes for the dyadic tree (ec410d23d → cfc55fc58, Lean v4.35.0)

Worker brief used during T1 of the dyadic Tau Ceti discharge (2026-10-17), kept as the catalogue of
breakage patterns met and their fixes, followed by the orchestrator's running notes (rule-1 exceptions,
transparency-option uses, pre-applied mechanical renames). Session-scratchpad paths in the text refer to
tooling that is not part of the repository.

## Hard rules

1. **Every declaration statement stays byte-identical.** Do not change the text of any
   `theorem`/`lemma` statement (everything before its top-level `:=`), any `def`/`abbrev`/
   `structure`/`class`/`instance`/`inductive` signature or body text, any `variable`, `open`,
   `namespace`, `universe`, or `notation` line. Change only:
   - proofs (the part after `:=` of a theorem/lemma, including `by` blocks, `termination_by`,
     `decreasing_by`);
   - `import` lines (add missing imports; replace a deprecated module import by its successor);
   - a `set_option … in` line placed directly before a declaration (see below).
   If a def body contains an embedded proof (e.g. a `fun … => by …` field proving a property,
   or a `⟨data, proof⟩` anonymous constructor) you may change the proof part only, leaving
   the data part byte-identical. If you believe a statement or data text *must* change (a
   Mathlib identifier used in it was removed outright, not merely deprecated), stop and report
   it instead of changing it.
2. Edit only the files assigned to you. Do not run `lake build`, `lake update`, `lake clean`,
   or anything that writes under `.lake/`; do not `git commit`, `git stash`, `git checkout` or
   `git reset`. The orchestrator builds and commits.
3. Do not add `sorry`, `axiom`, `admit`, or `native_decide`.
4. Do not touch the tmux session `fleet`, `~/.tauceti-fleet/`, `~/tauceti-fleet/`,
   `~/TauCetiWorker-v2/`, `~/TauCetiRoadmap/`.

## How to check a file

```
/tmp/claude-1006/-scratch-claudeM-gq2-tauceti/7313d86f-f71b-4b07-b403-b7c281f9491b/scratchpad/dyadic/tools.sh chk GQ2/Foo.lean
```

prints `OK GQ2/Foo.lean` or `FAIL` with the errors only (warnings suppressed). If it reports
`object file … .olean does not exist`, the orchestrator's build loop is rewriting oleans at that moment;
wait a minute and retry (never run `lake build` yourself). It runs `lake env lean`
with the lakefile's `leanOptions` passed as `-D` flags (`autoImplicit=false`, `relaxedAutoImplicit=false`:
plain `lake env lean` would NOT apply them and could pass a file that `lake build` rejects), so it uses the already-built `.olean`s of the file's imports, which are all up
to date. A file takes seconds to a few minutes. Iterate until `OK`. For exploration you can
write scratch `.lean` files under the scratchpad directory above and check them the same way
(`import Mathlib` works in a scratch file but is slow; prefer the file's own imports).

Mathlib source at the new revision: `/scratch/claudeM/gq2-dyadic/.lake/packages/mathlib/Mathlib/`
(grep it for renamed or moved declarations). The old revision is not checked out; to see the old
statement of a lemma, `git -C /scratch/claudeM/gq2-dyadic/.lake/packages/mathlib show ec410d23dfa4e7540d4663405b5e0dc71f3c3363:Mathlib/Path/To/File.lean`
works for a single known path, but `git log`/`git grep` over the old revision are very slow (>60 s);
avoid them.

## Known breakage patterns (all met during the ℚ₂ bump; report new ones)

Fixed ℚ₂ files are reference material: `git -C /scratch/claudeM/gq2-dyadic log --oneline tauceti -- GQ2/<File>.lean`
and `git show <hash>` show how each pattern was repaired (e.g. `GQ2/SectionSix.lean`, `GQ2/WordCoh2.lean`,
`GQ2/DevissageInduction.lean`, `GQ2/AdmissibleCount.lean`).

- **Lost transitive imports.** Mathlib trimmed its import graph; notation or instances may vanish
  (e.g. `∑ᶠ` needs `Mathlib.Algebra.BigOperators.Finprod`; `T1Space` from
  `TotallyDisconnectedSpace` needs `Mathlib.Topology.Separation.Connected`; `IsTopologicalGroup αˣ`
  and other `Units` topology instances moved to `Mathlib.Topology.Algebra.Group.Units`; this one
  has already hit two files — symptom `failed to synthesize IsTopologicalGroup ℤ_[2]ˣ`). Symptom: `expected
  token`, `unknown identifier`, or `failed to synthesize` for something that obviously holds.
  Fix: add the import. In a `module` file write `public import Mathlib.X`; in a non-module file
  plain `import Mathlib.X`. Find the defining file by grepping Mathlib.
- **New definitional-transparency checking (Lean v4.35).** Symptoms: `rewrite failed … Note: The
  target expression is not type-correct under the implicit transparency level`, `(kernel)
  declaration has metavariables`, `(kernel) application type mismatch` after a `show`/`rw`, or a
  defeq that used to go through. Fix: put `set_option backward.isDefEq.respectTransparency false in`
  on the line directly before the declaration (after its docstring is fine too, but the usual form
  is before the docstring). Mathlib itself uses this 6,678 times at this revision. Prefer a genuine
  proof fix if it is a one-liner; otherwise use the option. Example of a one-liner: after
  `obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective y`, `rw [AddMonoidHom.mem_ker]` fails to
  match; `refine AddMonoidHom.mem_ker.mpr ?_` (i.e. `.mpr`/`.mp` instead of `rw` with an iff)
  works. Another: after a `show` that restates the goal through a quotient-presented group
  (`DRFull`, `D0Full`, …), `rw [maxProPHomEquiv_symm_apply_maxProPMk]` fails; replace the `rw` +
  `exact h` by `exact (maxProPHomEquiv_symm_apply_maxProPMk _ _ _).trans h` (same shape is in
  `SectionThree.lean` `d0LiftHom_*` and `AnabelianBridge/Construction.lean` `deltaLift_*`/`d0Lift_*`).
  General rule: an iff/eq that `rw` can no longer find can usually be applied as a term
  (`.trans`, `.mpr`, `▸`) instead, or the `rw` of an `rfl`-lemma can simply be deleted when the
  following `exact` closes the goal by defeq (e.g. `mapCoeff1_H1mk` in `CupSymmetry`).
- **`ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one`** now needs
  `[ZeroDimensionalSpace G]`; it is found by instance once `Mathlib.Topology.Separation.Regular`
  and `Mathlib.Topology.Separation.Connected` are imported (compact + T2 + totally disconnected).
- **`IsSimpleGroup.eq_bot_or_eq_top_of_normal`** now takes normality as an instance argument
  (`∀ (H : Subgroup G) [H.Normal], …`); drop the explicit normality proof (symptom: `Function
  expected`).
- **`simp` made no progress** where `AddMonoidHom.mk'_apply`-style unfolding is now done by
  `ext`/`induction`: often the `simp only` line can simply be deleted.
- **`Equiv.setCongr h`** with `h : s = t` (sets) is now `Set.equivOfEq h`; `Equiv.setCongr` now
  means `(α ≃ β) → (Set α ≃ Set β)` (no deprecation alias, so the symptom is a type mismatch).
- **`simp only [… Foo.mk.injEq]` no longer splits** a structure equation whose fields have a
  `def`-synonym type (e.g. `CentExt c := L × ZMod 2` in `WordCoh2`), so a following
  `refine ⟨?_, ?_, ?_, ?_⟩` fails with `Constructor Eq.refl does not have explicit fields`. Use
  `congr 1` instead. On such synonym types `MonoidHom.coe_mk`/`OneHom.coe_mk` may not fire under
  simp; prove by definition (`rfl`, `zero_add _`). Fixed files are good references:
  `git -C /scratch/claudeM/gq2-dyadic log --oneline` and `git show <hash> -- <file>` show how
  earlier files were repaired (e.g. `GQ2/WordCoh2.lean` is the twin of `GQ2/Roe/DRWordCoh.lean`).
- **`Continuous.mul` / `.add` / … are now `@[to_fun]`**: `Continuous.mul` concludes
  `Continuous (f * g)`; for a goal `Continuous fun x => f x * g x` use `Continuous.fun_mul`
  (likewise `fun_add`, `fun_pow`, …). Symptom: a misleading `failed to synthesize ContinuousMul …`
  sometimes followed by `No goals to be solved`. Dot-notation chains too:
  `continuous_const.mul h` against a lambda goal → `continuous_const.fun_mul h`. Adding an import
  does not help.
- **A def passing a bare lambda where `N ≤ M.comap f` is expected** (`QuotientGroup.map`,
  `QuotientAddGroup.map`) now breaks `rw [map_mk]` downstream; fix with the transparency option
  on the def and `exact (QuotientAddGroup.map_mk N M f _ x).symm` (arguments explicit) instead of
  `rw` (see `GQ2/DevissageInduction.lean`, `stableQuotAction`). Same for `QuotientGroup.lift`
  with a bare lambda for `N ≤ φ.ker`: drop `rw [QuotientGroup.lift_mk]` and close by `rfl`
  (`GQ2/Block/Descent.lean`).
- **`PadicInt.ext` is now `@[ext]`**: a bare `ext` on a structure with a `ℤ_[p]` field goes on
  into `ℚ_[p]`; use `ext1` (symptom: a `ℚ_[2]` vs `ℤ_[2]` mismatch in a following
  `linear_combination`). If the structure also has a `ℤ_[p]ˣ` field, use
  `refine WordLift.ext ?_ (Units.ext ?_)` (or the analogous `Foo.ext`).
- **`def` synonyms of products** (`SemiProd C V := V × C`, `CentExt`): a bare pair `(a, b)` no
  longer unifies with the synonym in `simp`/`rw` with the synonym's `mul_def`/`inv_def`. Keep
  elements as variables while rewriting and `subst` concrete pairs only afterwards; prove group
  axioms coordinatewise with `Prod.ext (show … by …) (…)` (see `GQ2/SectionSix.lean`). For a
  nested product `s * x * s⁻¹` use `rw [SemiProd.mul_def, SemiProd.mul_def, SemiProd.inv_def]`
  (outermost first) rather than `simp only`, and split `simp only [h, mul_def]` into two passes
  (see `GQ2/RepIndependence.lean`).
- **`rw [show (⟨x, _⟩ : S) = Additive.toMul (c.1 γ) from Subtype.ext (by group)]; rfl`** (the
  `MLifts`/`ContSurj` subtype-synonym counting proofs) no longer matches; use
  `exact congrArg Additive.ofMul (show … from Subtype.ext (by group))` (see `GQ2/MStageCount.lean`)
  or `apply Additive.toMul.injective; apply Subtype.ext; show …; group` (`GQ2/Half139Local.lean`).
- **`rw [ElemDual.smul_apply]`** (and `rw [AddMonoidHom.mem_ker]` etc.) fails when the functional
  is a raw `A →+ ZMod 2` (e.g. a submodule element's `.1`) rather than `ElemDual A`; apply as a term
  with the type ascribed: `refine (GQ2.FoxH.ElemDual.smul_apply _ (chi.1 : GQ2.FoxH.ElemDual _) a).trans ?_`
  (see `GQ2/RStage/Local.lean`).
- **`rw [foo_apply]` on a target containing a `rfl : D.M = RF.MB` argument** (an equation holding
  only by unfolding) fails; build `have h1 := (foo_apply …).trans …` and close with
  `(congrArg … h1).trans …` (see `GQ2/Phase140/Assembly.lean`).
- **`Subgroup AbsGalQ2` vs `Subgroup (Kummer.GaloisGroup ℚ_[2])`** (same type up to unfolding):
  `rw` can't find visible patterns, `calc` fails with `Trans Eq Eq`, and `.Normal` instances are
  missed. Apply lemmas as terms with `.trans`, replace `calc` by `.trans` chains, and close
  definitional computation lemmas by `rfl` (see `GQ2/AdmissibleCount.lean`). Also
  `failed to synthesize TopologicalSpace ↥U₀` in `continuous_subtype_val.comp continuous_subtype_val`
  feeding a `Kummer.GaloisGroup` lemma: ascribe
  `(continuous_subtype_val : Continuous (Subtype.val : ↥U₀ → AbsGalQ2))` (`GQ2/InvolutionSplice.lean`).
- **Unfolding a `MonoidHom.codRestrict` def in `simp`** leaves `(f.codRestrict S h) x` stuck;
  keep the def folded and use its `rfl` coercion lemma (see `GQ2/AffineTLift.lean`).
- **`simp only` leaves a goal whose two sides print identically**: add `rfl` after it.
- **`rw [MonoidHom.coe_comp]`** on a composite whose middle types agree only up to a synonym:
  drop the `rw`, give the continuity/term as `(term :)` so the defeq runs at default transparency.
- **Renamed induction cases**: `FreeGroup.induction_on`'s case `C1` is now `one`. Generally,
  `Invalid alternative name X: Expected Y` → rename the alternative.
- **`IsCompact.elim_finite_subfamily_closed`** now takes/returns `Disjoint s (⋂ i, t i)` instead
  of `s ∩ ⋂ i, t i = ∅`; convert with `Set.disjoint_iff_inter_eq_empty` / `Set.disjoint_left`.
- **`pow_left_injective`, `pow_left_inj`, `zpow_left_injective` now need `[HasUniqueRoots M]`** (a new
  class; `IsMulTorsionFree` no longer provides it, and there is deliberately no reverse instance even
  for commutative monoids). Symptom: `failed to synthesize HasUniqueRoots …`. Fix on a commutative
  type: `intro a b hab; exact (Commute.all a b).eq_of_pow_eq_pow hn hab`
  (`Commute.eq_of_pow_eq_pow`, `Mathlib/Algebra/Group/Torsion.lean`); or
  `eq_of_pow_eq_pow_of_commute`.
- **`Sylow`'s second field is now `maximal_isPGroup : Maximal (IsPGroup p ·) toSubgroup`**, so
  `P.2` / `P.prop` no longer have type `IsPGroup p ↥P`: use `P.isPGroup` (`Sylow.isPGroup' → Sylow.isPGroup`,
  `Sylow.is_maximal' → Sylow.maximal_isPGroup` are deprecated aliases).
- **`decide` fails with `failed to synthesize Decidable …`** on an equation in `ZMod (2 ^ d.r)`
  whose instance would need unfolding a non-reducible def (`ZMod.decidableEq` no longer matches at
  implicit transparency): try `rfl`, or `show _ = ((… : ℕ) : ZMod (2 ^ d.r))` before `decide`.
- **`Group.FG` / `Subgroup.FG` / `Monoid.FG` are now abbrevs of one class `IsMulFG`**:
  `Group.fg_iff_subgroup_fg` is `rfl` (so its `.mpr ⟨s, _⟩` wants `s : Finset ↥D`), and `hfg.1`/`hfg.out`
  gives a `Subsemigroup.closure` fact. Build with `Subgroup.isMulFG_iff.mpr ⟨s, h⟩` (`s : Finset G`) and
  destructure with `Group.isMulFG_iff.mp hfg : ∃ S : Finset G, Subgroup.closure ↑S = ⊤`
  (`Mathlib/GroupTheory/Finiteness.lean`).
- **`IsMulTorsionFree`'s field is now `eq_of_pow_eq_pow_of_commute ⦃n⦄ (hn : n ≠ 0) ⦃a b⦄ (hab : Commute a b) (h : a ^ n = b ^ n) : a = b`**;
  an instance built by `constructor; intro n hn x y h` now needs the extra `Commute` binder, and
  `IsMulTorsionFree.pow_left_injective` is a deprecated alias with a changed signature (symptom: a
  misleading `failed to synthesize IsMulTorsionFree …`).
- **A def synonym blocks instance search on a quotient by an `OpenNormalSubgroup`** (e.g.
  `Group (proPCompletion p A ⧸ ↑V)` not found): restate the fact at the right type with an ascribed
  `have hP : IsProP p (proPCompletion p A) := …` first, then apply it.
- **`simp only [def, foo_val]` where `foo_val` is an `rfl` lemma rewriting inside an `if` condition**
  leaves the `Decidable` instance on the old expression, so a later `rw [if_neg …]` finds no `ite`:
  keep `have hj := foo_val j` as a hypothesis for `omega` instead of rewriting with it.
- **`padicValNat.pow` lost its `a ≠ 0` hypothesis** (now `padicValNat.pow (a n : ℕ)`); passing the old
  argument gives `Application type mismatch … expected ℕ`: drop it.
- **`omit [inst] in` before a declaration that still references `inst`** is now an error
  (`cannot omit referenced section variable`): remove that variable from the `omit` list. The
  elaborated statement is unchanged (the old Lean kept the binder anyway); say so in the report,
  since the statement checker will flag the edited `omit` line.
- **Pair literals against a `def` synonym of a product** (`PinV := ZMod 2 × ZMod 2`, `SemiProd`): `rw`
  with lemmas stated on the synonym fails on every occurrence; feed them as terms
  (`(lemma _ _).trans ?_`, `congrArg₂ (· + ·) …`) or `show` the unfolded form.
- **Tau Ceti environment leak (fixed at the root on 2026-10-17; know the symptom).** Files that
  reach `GQ2.Foundations.TauCetiInstance` (every user of a legacy input name such as
  `localReciprocity`, `tateDualityAt`, `markedRecipAt`, and all their non-`module` importers) load the
  Tau Ceti library and its Mathlib closure, which adds instances (`Pi.instCharP`,
  `TauCeti.IsTopologicalAddGroup.nonarchimedeanAddGroup_of_compactSpace`) and changes `simp` and
  instance paths: `CharTwo.sub_eq_add` rewrites function-level `-` before `Pi.sub_apply`, an `omit
  [Finite _]` becomes "cannot omit referenced section variable" because the instance path now
  uses it. For a dyadic-only file, fix locally (`Pi.add_apply` in the simp set; drop the variable
  from `omit` and SAY SO). For a ℚ₂ file that is byte-identical to `tauceti`'s (check with
  `git diff tauceti -- FILE`), do NOT edit it: report "leak-induced" and stop; the orchestrator
  decides. `Interfaces.lean` no longer re-exports `Axioms.lean`, so a file that lost a legacy
  name (`unknown identifier localReciprocity` etc.) needs `import GQ2.Foundations.TauCetiInstance`
  (the nine ℚ₂ names) or `import GQ2.Foundations.Axioms` (the K names, re-exports the former).
- **`IntermediateField.finrank_eq_fixingSubgroup_index` now takes the ambient field explicitly**
  (`finrank_eq_fixingSubgroup_index E' L`): a call `(… L).symm` fails with `Function.symm`; write
  `(IntermediateField.finrank_eq_fixingSubgroup_index _ L)`.
- **Approved rule-1 exception: ℚ₂-model pins.** `example : @foo_K_q2 = @GQ2.<Model>.foo := rfl`
  fails with `Type mismatch` because the ℚ₂ model's theorem gained a `[LiteratureInputs]` binder in
  the merged refactor. Rewrite the pin as `example [LiteratureInputs] : @foo_K_q2 C _ … = @GQ2.<Model>.foo
  C _ … _ := rfl` with the explicit arguments matching the section variables in scope (the
  orchestrator approved this shape on 2026-10-17 for LocalGauss/{Unramified,Ramified,Main}); list
  each such pin in your report under "rule-1 exceptions".
- **`failed to synthesize T2Space (Multiplicative (A × B × C × D × …))` (4+ factors)** exceeds the
  default `synthInstance.maxSize 128`; `set_option synthInstance.maxSize 256 in` before the
  declaration fixes it (MarkedCore/MFrameExists; NFrameExists-style frame models are candidates).
  Heartbeats and transparency options do not help.
- **`IsQuotientMap.of_surjective_continuous` moved to the `Topology` namespace** (no root alias):
  qualify it as `Topology.IsQuotientMap.of_surjective_continuous` (or `open Topology in`).
- **A `@[simp]` lemma stops firing through `simp` but closes the goal as a term** (EvenModelH2:
  `by simp` → `nLiftHom_gen _ _ _ _ _ _`): try the lemma as an explicit term before digging.
- **A local `let` bundled hom built from a `{ toFun := … }` literal** no longer reduces under `simp [myLet]`;
  pass `have h : ∀ c, myLet c = … := fun _ => rfl` to `simp` instead (HTwoFoxCounterexample).
- **Mixed instances on a `ProfiniteGrp` carrier vs its abbrev** (`↑(ProfiniteGrp.of ZmodThree)` vs
  `ZmodThree`): `group`/`rw [one_pow, map_one]` get stuck and `show` does not help; elaborate the
  equation separately at the synonym type (`have h : (1 : ZmodThree)⁻¹ * … = 1 := by simp; exact h`)
  or apply the lemma as a term (`exact map_one f`) (Count/Routine).
- **`failed to synthesize IsDedekindFiniteMonoid Gal(…)` from a full-simp-set `simpa`/`simp`**: a new
  Mathlib class whose instance search times out on Galois groups; replace the `simp` by the direct
  term/`exact` (or `simp only` with the needed lemmas) (HigherHilbert90).
- **`failed to compile definition, consider marking it as 'noncomputable'` on a `Set`-valued def.**
  `Set` is now a structure in Mathlib, so `Set`-valued bodies are compiled; a body mentioning a
  noncomputable constant needs the `noncomputable` modifier. Approved rule-1 exception: add
  `noncomputable` to that def only (nothing else on the line), and list it under "rule-1 exceptions".
- **`simp [myHomDef]` on a top-level def that is a `{ toFun := … }` structure literal** leaves
  `{ toFun := f, … } c` unreduced (H3FiniteBarFoxAssembly, TameShadowHessianRamified): do not unfold it
  with `simp`; use `change`/`show` to the definitional form or close with `exact`.
- **`rw [myDef]` exposing an abbrev-like synonym** (`Ztwo` = `maxProPQuotient 2 ℤ̂`) breaks the next `rw`:
  keep the def folded and `exact (lemma …).trans …` (Instances/Cores).
- **`LinearMap.map_sub f a b` elaborates with an unresolved map** → use the generic `map_sub f a b`
  (H3CompatibleFoxInjectivity).
- **Approved rule-1 exception: `MonoidAlgebra` is now a structure** (`structure MonoidAlgebra R M where
  ofCoeff :: coeff : M →₀ R`, no `CoeFun`): applying a group-algebra element to a point, `x q`, fails
  with `Function expected`. Write `x.coeff q` — in statements too when the statement applies the
  element; quote every changed statement old → new under "rule-1 exceptions". Do NOT add a local
  `CoeFun` instance. (Count/CompletedRankOneFox, 2026-10-17.)
- **`MonoidAlgebra.induction_on` cases renamed** `hM`/`hadd`/`hsmul` → `of`/`add`/`smul` (same
  arguments; `AddMonoidAlgebra.induction_on` likewise) (FiniteTwoGroupAugmentationNilpotence).
- **`MonoidHom.restrict f S` (restrict to a subgroup of the domain) is now `f.domRestrict S`**; the old
  name now takes a `Set.MapsTo` proof (symptom: `expected Set.MapsTo …`, `failed to synthesize SetLike`).
  `restrict_apply`/`restrictHom`/… → `domRestrict_*` (deprecated aliases exist) (GammaLSylowPreimageInflationKernel).
- **`simpa … using x.2` where `x.2 : ↑x ∈ S` now simplifies the hypothesis to `True`** (`SetLike.coe_mem`):
  restate it, `have hx : <unfolded membership> := x.2`, then `simpa … using hx` (ResidueLocalFieldBridge).
- **Leak symptom: `IsLocalRing ↥v.integer` instance search times out** through
  `TauCeti.IsAdicComplete.henselianLocalRing` (misleading `failed to synthesize LinearOrder (Submodule …)`):
  `set_option synthInstance.maxHeartbeats 40000 in` before the declaration, or
  `attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing in` (ResidueLocalFieldBridge).
- **`f.toZModLinearMap n` with `f` on a Pi/def-synonym domain fails with an application type mismatch**
  (unifier cannot match the `AddZero` instances while `M` is unassigned): give `(M := …) (M₁ := …)`
  explicitly (H3UniversalRelationLift).
- **`chk` caps output at 80 lines**: a file with many errors shows only the first few; run
  `CHK_LINES=2000 tools.sh chk FILE` to see all of them before declaring the file fixed.
- **`MonoidAlgebra`-as-structure, proof side**: `Finsupp.smul_single_one`/`Finsupp.induction`/
  `Finsupp.single` on group-algebra elements no longer apply; use `MonoidAlgebra.smul_single'` + `mul_one`,
  `MonoidAlgebra.induction` (same `zero`/`single_add` cases), `MonoidAlgebra.single` (H3SqQuadraticDiamond).
- **Subtype words over a plain `def` (`QuadraticNormalWord x s`)**: `w.1`, `⟨l, tail hw⟩` are not
  type-correct at implicit transparency, so `rw` over them fails; apply the equation lemma as a term
  (`(foo.eq_2 …).trans (dif_pos rfl)`) or, as a last resort, the transparency `set_option` (files built
  on `H3SqQuadraticPBW`).
- **`simpa using congrArg f …` no longer applies `map_zero`** to a cohomology class map: `.trans (map_zero _)`
  (GammaLSylowPreimageKernelFiniteLevel).
- **`MonoidAlgebra`-as-structure, def bodies**: a `Finsupp.lsum`/`Finsupp.*` linear map used as a map
  out of `MonoidAlgebra R M` needs `∘ₗ (MonoidAlgebra.coeffLinearEquiv R).toLinearMap`; this is a
  data-body edit — allowed under the approved MonoidAlgebra category when the signature and the computed
  function are unchanged; quote old → new under "rule-1 exceptions" (H3CompletedMagnusGradedBridge).
- **Mathlib swapped the ramification/inertia names (no meaning-preserving alias)**: old
  `Ideal.ramificationIdx p P` (Dedekind `sSup` index) is now `Ideal.ramificationIdx' p P`; old
  `q.ramificationIdx' R` (localized-length index) is now `q.ramificationIdx R`; old `q.inertiaDeg' R` is
  now `q.inertiaDeg R`. Rename in statements too (a renamed identifier is allowed by rule 1; list them);
  `Ideal.inertiaDeg_eq_inertiaDeg'` → `Ideal.inertiaDeg_eq_of_isMaximal` (RamificationInertiaBridge).
- **Leak timeouts on valuation integer rings** also hit `Module.Flat`, `Finite (p.primesOver S)`,
  `IsScalarTower BaseInteger (ExtensionInteger K) K` (supply with `haveI :=
  Valuation.HasExtension.instIsScalarTowerInteger`), `Fintype.ofFinite` (use `Fintype.ofSubsingleton default`).
- **`Finsupp.mapDomain_apply` (injective form) is now `Finsupp.mapDomain_apply_of_injective`**; the old
  name means a different lemma (symptom: application type mismatch) (H3CompletedMagnusKernelIdentity).
- **Generic `map_sub` on a `LinearMap` out of a `Submodule.toAddSubgroup` carrier times out** in
  instance search; use `LinearMap.map_sub` there (the opposite of the H3CompatibleFoxInjectivity item —
  try the other spelling).
- **Proof argument elaborated before its `let`-bound map is known** (`(LinearMap.ker d).liftQ T hker`
  fails against `ker ?f`): write `(by exact hker)` to delay it; name the target type of
  `LinearMap.exists_extend (V' := …)` when it can no longer be inferred (H3FiniteUniversalDegreeThreeComparison).
- **`⟨d c, ⟨c, rfl⟩⟩ : LinearMap.range d` now elaborates the membership as a bare `∃`** and the
  `quotKerEquivRange` simp lemmas stop firing: use `LinearMap.mem_range_self d c`.
- **Instance search on `Unitization (ZMod 2) (sqCubicStrictEnd h)` / `SqCubicOperatorAlgebra h`
  (`Semigroup`, `AddHomClass`) times out** (walks the normed-field paths first): `set_option
  synthInstance.maxHeartbeats 100000 in` before the declaration; a `noncomm_ring` "simp lemmas don't
  apply" failure there has the same cause (H3CompletedCubicFiniteOperator).
- **`simpa [f] using h` fails with `failed to synthesize Decidable (0 = 0)`** when beta-reducing exposes
  an `if i = 0 then … else …` over a def-synonym index type (`Fin (coreRank 0)`): restate `h` in its
  reduced form by defeq first (`have h2 : <reduced> := h`), then `simpa [f] using h2` (EvenStratumShift).
- **`refine IsOpen.inter ?_ ?_` against `IsOpen {x | A x ∧ B x}` gets stuck** (`TopologicalSpace ?m`):
  `Set` is a structure, so `a ∈ ?s` no longer unifies with `A a`; give both sides as terms,
  `exact hA.inter hB` (MpcNormValues).
- **A large reflective `by decide` (generated `Deriv.check` chains) times out at 200000 heartbeats**:
  use `decide +kernel` (kernel checks `of_decide_eq_true rfl`; no new axioms, already used in 7 dyadic
  files) rather than a heartbeat bump (MpcC6WeightedTracePrefix).
- **`rw [powOmega2_map f]` fails when the `powOmega2` argument is typed at a synonym** (`DD.C0` vs
  `Y ⧸ Blk.K`): `refine (congrArg (· • v) (powOmega2_map f _)).trans ?_` then continue the rewrites
  (MpcHandleBoundary, GammaLDeterminantRamifiedData, GammaLSourceArfGeneral); the simplest form is to
  give the point explicitly inside the `rw`: `rw [hstep, powOmega2_map f (rho0 DD rhoM (gammaGen … .tau)), …]`
  (WordPhaseCompactNData).
- **Stale-`Decidable` variant inside `refine ⟨fun i => if (i : ℕ) = 0 then … else …, ?_⟩; · intro i;
  simp only [sqHandleIdxU_val]; rw [if_neg (by omega)]`**: `have hv := sqHandleIdxU_val i` then
  `dsimp only` (beta-reduce only), then the unchanged `rw` (GradedExtraction, GradedUniformTower).
- **A singleton set literal `{a}` whose element spans lines no longer parses** (`unexpected token '}';
  expected '|'`): parenthesise the element, `{(f a … ⏎ * g b)}` (syntax-only def-body edit; list it)
  (GradedLatticeWide).
- **A `change`/`show` restating a goal at the unfolded type of a def synonym (`PinC`, `PinV`) loses the
  synonym's `Decidable` instance**: drop it and `decide` at the synonym type; a witness via
  `refine ⟨(lit : Syn), ?_⟩` has the same problem — `decide` the whole `∃` over the `Fintype` synonym
  (RamifiedCertificateResidueInertia).
- **Matrices over `AddMonoid.End V` holding a bare `L : V →+ V`**: after unfolding, `simp` leaves
  `(L * 0 + 1) x = x`-style goals stuck (`L` has type `V →+ V`, expected `AddMonoid.End V`). Prove the
  identity for a variable `M : AddMonoid.End V` (`simp [Matrix.mul_apply, Fin.sum_univ_two]` closes it)
  and `exact key L` (WordPhaseWallHandlePolarInverse).
- **`failed to synthesize DiscreteTopology (Kummer.GaloisGroup ℚ_[2])` (typeclass timeout) from a
  full-simp-set `simp`/`simpa` on an `IsClosed` goal**: use `simp only` with the needed lemmas
  (`Set.iInter_true`, `Set.iInter_false`, `isClosed_univ`) (RamifiedCertificateOddRootFrobeniusCompactness).
- **After `map_pow`/`map_mul` push a character inside a product, `@[simp] dmCoordinateCharacter_gen`
  stops firing on `χ U`**: for a single application `exact congrArg toAdd (dmCoordinateCharacter_gen …)`;
  for a whole `fin_cases` sweep the transparency option is the practical fix (MpcCupAdaptedSeed).
- **`simp` lemmas stated at a def-synonym type (`ElemDual (ElemDual A)`) do not fire on a lambda/value
  whose inferred type is the unfolded form** (`ElemDual A →+ ZMod 2`): generalize the term to a variable
  ascribed at the synonym type (`obtain ⟨f, hf⟩ : ∃ f : … → Syn, f = … := ⟨_, rfl⟩; rw [← hf]`), simp
  with it opaque, then `subst` and finish (EvenMHeadHandleHyperbolicRawStokes).
- **`minpoly.isIntegrallyClosed_dvd` now needs `[IsTorsionFree R S]`** and the search for
  `Module.IsTorsionFree ↥BaseInteger ℚ̄₂` times out: `haveI : Module.IsTorsionFree BaseInteger ℚ̄₂ :=
  Module.IsTorsionFree.trans_faithfulSMul BaseInteger ℚ_[2] ℚ̄₂` (RamifiedCertificateOddRootLocalConjugacy).
- **`[N.Normal]` not found when the ambient group is a plain `def` synonym** of the subgroup's own
  ambient type (`QuotientGroup.quotientMulEquivOfEq h` in a def body): the only proof-level fix edits
  the def body (`@… (inst) h`), so the transparency `set_option` on that def is the accepted fix
  (MpcOneHandleClassSevenNeutralCoordinateBound).
- **Deprecations are warnings, not errors.** Leave deprecated names alone unless they now fail.
  `Mathlib.Topology.Separation.Profinite` and `Mathlib.Topology.Separation.Lemmas` are deprecated
  modules; you may replace such deprecated `import` lines with the successor the warning names.
- Linter warnings (`haveI`/`letI` style, "consider adding `module`", unused variables) are not
  errors; ignore them.

## Report (your final message)

For each assigned file: `OK` or `FAIL`, a one-line summary of what you changed, and
- every Mathlib rename or removal you met: `old name → new name` (or `removed; replaced by …`);
- every lost import you added;
- every declaration where you used `set_option backward.isDefEq.respectTransparency false in`;
- any place where rule 1 could not be kept, with the exact reason.
Keep the report under 40 lines.

## Orchestrator notes

- SIGNATURE: pow_left_injective/pow_left_inj/zpow_left_injective need HasUniqueRoots (new class); use Commute.eq_of_pow_eq_pow (Dyadic/PrincipalUnitTorsion)
- transparency option on def padicOmega2 (Dyadic/Word/Syntax)
- SIGNATURE: Sylow second field now maximal_isPGroup; P.2 -> P.isPGroup (Dyadic/Count/H2SylowPreimageDevissage)
- decide fails (Decidable on ZMod (2^d.r) through non-reducible def) -> rfl (Dyadic/Branches)
- CLASS: Group.FG/Subgroup.FG -> IsMulFG abbrevs; use Subgroup.isMulFG_iff / Group.isMulFG_iff (Dyadic/FinitelyGeneratedK)
- Sylow P.2 -> P.isPGroup (Count/H2MaxProTwoTransport)
- CLASS: IsMulTorsionFree field now eq_of_pow_eq_pow_of_commute (Commute binder) (Dyadic/PrincipalUnitCompletion)
- def synonym blocks instance search on quotient by OpenNormalSubgroup -> ascribed have (Dyadic/PrincipalUnitCompletion)
- simp only [def, foo_val] leaves stale Decidable in ite -> keep _val as hypothesis (MarkedCore/Cores)
- rfl-lemma rw deleted (QuotientGroup.map_mk) (ZhatTorsion); SemiProd synonym show (Word/Hessian, LocalGauss/Q0); PadicInt ext1 + maxProPHomEquiv term (MarkedCore/Cores)
- SIGNATURE: padicValNat.pow no longer takes a ≠ 0 (LocalGauss/EulerShapiro); refactor: dyadic consumers of legacy nine names reach them via Interfaces -> Axioms -> TauCetiInstance re-export (03866bac)
- NEW CHECK: `omit [inst] in` with inst referenced is an error (Shapiro/Read)
- PinV pair synonym -> terms (NpcJet/Handles); rfl : D.M = RF.MB pattern (Recursion/Phase140Assembly)
- LEAK (2026-10-17): Interfaces -> Axioms -> TauCetiInstance -> (public) TauCeti.Instance put Tau Ceti + its Mathlib closure into every GQ2 file. Non-module importers (1379/1596 files) load private imports too, so hiding is only partial. Fixes applied: TauCetiInstance imports GQ2.TauCeti.Instance privately, `public section` (no @[expose]), instance built field-by-field from the legacy names; Interfaces no longer imports Axioms; 25 seed files (direct users of legacy names) import TauCetiInstance/Axioms directly. Residual leak set ~1000 files (transitive importers of the seeds). Reverted leak-induced edits in Shapiro/Read.lean (omit) and WordCoh2R.lean (Pi.add_apply); if they fail again in build 107+ they are in the residual set -> re-apply.
- TODO after build green: for every T1-committed file, test whether the merge-base version builds in the new environment; revert those that do (leak-induced edits).
- Tauceti follow-up for David: the same private-import restructuring of TauCetiInstance.lean applies to `tauceti` (there the file is a leaf imported by 4 files, so no leak today).
- RULE-1 EXCEPTION (approved by orchestrator 2026-10-17, to list on the board for David): ℚ₂-model pins `example : @foo_K_q2 = @Model.foo := rfl` in LocalGauss/Unramified.lean:1101, Ramified.lean:1687, Main.lean:580,585 get a `[LiteratureInputs]` binder (the ℚ₂ theorems gained it in the LiteratureInputs refactor). Cause: refactor, not Mathlib.
- SIGNATURE: IntermediateField.finrank_eq_fixingSubgroup_index now takes the ambient field explicitly (LiftingDualityG); blockFrameImpl vs SectionNine.blockFrame instance mismatch (ThmFourTwoN, same as tauceti 84e08795)
- PATTERN: synthInstance.maxSize for T2Space of Multiplicative 5-factor product (MFrameExists)
- LEAK-INDUCED ELABORATED-STATEMENT CHANGE (for the board): LocalGauss/ReadPerOrbitK.lean — 9 theorems gain `[Finite (RegRep N)]` (omit lists trimmed); only caller VanishCloseK has the instance.
- REFACTOR CONSEQUENCE: ℚ₂ declarations with a `[LiteratureInputs]` binder (chiD0G, markedPro2_R, …) used from dyadic files need the instance -> `import GQ2.Foundations.TauCetiInstance` (SqCore/Rank3). Docstrings of Rank3 (lines 69-114, 283-295) still claim B3c/B8 axioms and census 11 -> C2' docs sweep.
- RULE-1 EXCEPTION (approved): `noncomputable` added to Set-valued defs whose bodies mention noncomputable constants (Set is now a structure): Count/Wild.lean wildLetters. Pre-applied FreeGroup.induction_on C1->one in 6 more files; finrank_eq_fixingSubgroup_index `_ K` in 5 more files; IsQuotientMap qualified in RamifiedCertificateTameInertiaExact.
- RULE-1 EXCEPTION (approved): MonoidAlgebra is a structure; x q -> x.coeff q incl. statements (CompletedRankOneFox lines 88, 221).
- RULE-1 EXCEPTION (MonoidAlgebra): H3SqRowInitialForms sqFreeMagnusLinearInitial_coefficient line 269 -> .coeff
- TRANSPARENCY OPTION USED: H3SqQuadraticDiamond (sqNormalLeftLetter_single_tail, sqQuadraticNormalEval_leftXWord)
- RULE-1 EXCEPTION (MonoidAlgebra, def BODY): H3CompletedMagnusGradedBridge modTwoGroupAlgebraLinearMoment composes Finsupp.lsum with (MonoidAlgebra.coeffLinearEquiv (ZMod 2)).toLinearMap (signature and computed function unchanged). Users: H3CompletedAugmentationGenerators, LowerTwoCentralJenningsDegreeOneReverse.
- RULE-1 EXCEPTION (renamed Mathlib identifiers, allowed): RamificationInertiaBridge l.337/349/390/437: Ideal.ramificationIdx<->ramificationIdx', inertiaDeg'->inertiaDeg (Mathlib swapped the names; meaning unchanged). Six maxHeartbeats 40000 set_options (leak).
- CHECKER FIX (2026-10-17): dstmtcheck/stmtcheck top_level_assign skipped nothing: a letI/haveI/let/have := inside a statement ended the extracted signature early, hiding later statement edits (found via RamificationInertiaBridge). Fixed; re-audit of all 87 non-exception dyadic T1 files: 0 statement diffs.
- DEF-BODY (toZModLinearMap named args, data unchanged): H3FiniteUniversalDegreeThreeComparison syzygyBoundary let T (M := …) (M₁ := …)
- DEF-BODY (syntax only): GradedLatticeWide selGaTwoIm singleton literal parenthesised
- TRANSPARENCY OPTION USED: LPhaseAdditiveNormal ramifiedActionH1Equiv_add (term fix hit whnf timeout)
- TRANSPARENCY OPTION USED: MpcCupAdaptedSeed (modTwoCoordinate_clearModTwoHandles, dmCoordinateCharacter_core_comp_forget)
- TRANSPARENCY OPTION USED: MpcOneHandleClassSevenNeutralCoordinateBound oneHandleC7StandardNeutralityCokernelEquivBalanced (Normal instance at a def-synonym ambient group)
