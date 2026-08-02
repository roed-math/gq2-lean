/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.AdmissibleR
import GQ2.Dyadic.TameQuotientK

/-!
# Maps out of `Γ_R`, and the pro-`p` kernel under isomorphism  (dyadic campaign, ticket AS4-b)

Three generic facts that AS4 (`GQ2/Dyadic/Instances/QTwo.lean`) named as owed by nobody and that
its `n = 1` inventory (module docstring, "⚠ What blocks the last two rows") could not cite.  All
three are about *maps*, none is about a particular word, and none needs the certificate layer —
so they live in one leaf just above `AdmissibleR.lean` rather than inside the files AS4 suggested
(`GQ2/MaxProP.lean` and `GQ2/Dyadic/AdmissibleR.lean`), both of which have other owners.

## What this file lands

* **§1 — the pro-`p` kernel is natural, and an isomorphism pulls it back exactly.**
  `proPKernel_le_comap` is the naturality square `K_p(A) ≤ f⁻¹ K_p(B)` for *any* continuous
  homomorphism, with no surjectivity and no profiniteness hypothesis; `comap_proPKernel` is AS4's
  requested equality `e⁻¹ K_p(B) = K_p(A)` for a `ContinuousMulEquiv`, obtained by running
  naturality along `e` and along `e.symm`.  `ker_comp_continuousMulEquiv` is the packaged shape
  the consumer wants: precomposing a maximal-pro-`p`-quotient map with an isomorphism again has
  kernel the pro-`p` kernel — i.e. `WordCertificate.ker_pro2` transports along `≃ₜ*`.

* **§2 — the uniqueness principle for `Γ_R`.**  `gammaR_hom_ext`: two continuous homomorphisms
  out of `Γ_R = GammaR n q R` that agree on the `n + 3` marked letters `gammaGen n q R` are
  equal.  This is the reusable one, and its *hypotheses* matter more than its proof: the target
  need only be a **Hausdorff topological group** — no compactness, no total disconnectedness, not
  even `IsTopologicalGroup` on the target.  See the design note below.

* **§3 — the scalar trio at `Γ_R`.**  `gammaRSMulZmod2` / `gammaRContSMulZmod2` /
  `gammaR_htriv`, stated at the verbatim types of `WordCertificate.smulZmod2` /
  `.contSMulZmod2` / `.htriv` (`GQ2/Dyadic/CertificateMain.lean`).

## ⚠ Finding: §3 was *not* unwritten

AS4's inventory row reads "`smulZmod2`, `contSMulZmod2`, `htriv` — ⚠ not built (routine;
unwritten for `GammaR`)", and `CertificateMain.lean`'s obligation table used to say "routine, but
nobody has written them for `GammaR`".  Both were stale: **CB-0 closed this row generically**, in
`GQ2/Dyadic/Count/Routine.lean` §4, over an arbitrary monoid, and instantiated it at the
compact-`N` pilot (`Count.pilot_smulZmod2` and siblings).  What was genuinely missing is only
the `(n, q, R)`-generic *naming* at `Γ_R`, §3 — three one-line definitions.  (CB-DD has since
corrected `CertificateMain.lean`'s row, and moved CB-0's generic trio into §3 below; the pilot
instantiations in `Count/Routine.lean` §5 are unchanged and now consume §3 directly.)

## This file is the canonical home for both shared pieces (ticket CB-DD)

AS4-b recorded two duplications and reserved the merge for a follow-on ticket; **CB-DD performed
it, and this file is the home.**  `Count/Scalar.lean`'s §1 docstring ruled that "the merge belongs
to whichever ticket first has both in scope", and this file is the first place that could be that
home: it sits directly above `AdmissibleR.lean`, so every duplicate site can import it, and none
of them is in its own import closure (verified with Lake, not argued).

* **The trivial `ZMod 2`-action** had five copies.  `scalarActionZmodTwo` /
  `_continuousSMul` / `_triv` (§3) are the survivors.  Deleted: `Count.trivialSMulZmodTwo` and its
  two siblings (`Count/Routine.lean` §4, statements verbatim identical), and `Count.scalarAction`
  / `.scalarAction_continuousSMul` (`Count/Scalar.lean` §1, the same action one typeclass
  narrower).  **Two copies are deliberately kept** — the inline `letI actZ : DistribMulAction …`
  blocks in `GQ2/HalfTorsorGammaA.lean` and `GQ2/HalfTorsorGammaR.lean` — for two reasons: they
  are anonymous structure instances inside proof bodies rather than declarations (there is nothing
  to re-point), and both files belong to the **frozen `ℚ₂` development** (plan A6).  Redirecting
  them is technically possible — a Lake probe confirms both compile with this file imported, so
  there is no cycle and no module-rule obstruction — but it would create the tree's only
  `ℚ₂ → Dyadic` import edge to save ten lines inside two `letI`s.  Not taken.

* **`topGen_gammaR`** had four copies; §2's is the survivor.  Deleted: `Count.topGen_gammaR`
  (`Count/Routine.lean` §3), `Count.CorePresentation.topGen_gammaR` (`Count/ProTwo.lean` §2), and
  `Count.gammaGen_topGen` (`Count/Presentation.lean`) — the fourth, which carried a *different
  name* for the identical statement and proof, which is why AS4-b's grep did not name it.

⚠ `GQ2.Roe.topGen_gammaR` (`GQ2/Roe/Main.lean`) is **not** a further copy and was not touched: it
is the `ℚ₂` statement about the four-element set `{gammaSigmaR, gammaTauR, gammaX0R, gammaX1R}`,
not about `Set.range (gammaGen n q R)`.  Same name, different theorem.

## Design note: why `T2Space` is the right hypothesis in §2

`Γ_R` is a *topological* quotient of a free profinite group, so the marked letters generate it
only **topologically** (`topGen_gammaR`).  The uniqueness principle is therefore a density
argument, and density arguments need exactly one thing of the target: that the equalizer
`{z | f z = g z}` be closed.  For continuous `f, g` that is `isClosed_eq`, i.e. `T2Space`.
`IsTopologicalGroup` is needed on the *source* (to know `Subgroup.topologicalClosure` is a
subgroup at all) and is free there, `Γ_R` being profinite.

This is strictly more general than the two ext principles the campaign already had, and the gap
is not cosmetic:

* `Count.CorePresentation.hom_ext` (`Count/ProTwo.lean` §1) asks the target to be profinite
  (`IsTopologicalGroup`, `CompactSpace`, `T2Space`, `TotallyDisconnectedSpace`);
* `QTwo.free_hom_ext` (`Instances/QTwo.lean` §2) asks it to be a `ProfiniteGrp` object, and is
  about the *free* group rather than about `Γ_R`.

The intended `n = 1` consumer is `WordCertificate.compat`, whose two sides are continuous maps
into `Ztwo = ℤ₂`; `ℤ₂` is profinite, so any of the three would do there.  But the general-`K`
consumers of a `ν`-compatibility or boundary-square identity land in `Tq q`, in `ℤ₂`, and in
subgroups of products of those — and the Hausdorff form applies to all of them without an
instance search, which is why the statement is fixed here at the weakest hypothesis that works.

## What this unlocks at `n = 1`, verified

AS4's blocked row is `WordCertificate.pro2` / `.ker_pro2` / `.hpro2` / `.compat` at
`(n, q, R) = (1, 2, L_sq)` (AS1's divergence 3).  With §1 and §2 **all four discharge**, and this
was checked end to end rather than argued: composing Roe's `pro2R GQ2.Roe.Labute.bLab` with AS4's
`gammaR_lSq_equiv_roe` gives `pro2`; `hpro2` is `pro2R_surjective ∘ e.surjective`; `ker_pro2` is
literally `ker_comp_continuousMulEquiv gammaR_lSq_equiv_roe _ (ker_pro2R _)`; and `compat` is
`gammaR_hom_ext` against `Ztwo` followed by the four letter values
`nuTq_tqSigma`/`nuTq_tqTau` on the left and `phiR_gammaSigma`/`…Tau`/`…X0`/`…X1` +
`nuT_tameSigma`/`nuT_tameTau` on the right — since `nuTq 2 = nuT` by `rfl`
(`TameQuotientK.lean`).  The check prints the frozen `ℚ₂` census
(`localReciprocity`, `dyadicOrientation`, `peripheralCyclotomicAction`, plus the standard three)
and **no `sorryAx`**, i.e. nothing beyond what `pro2R` already carries.

The discharge itself is *not* landed here: it belongs in AS4's file, which has another owner, and
it would cost this leaf an import of `GQ2.Roe.Main`.  Two frictions the transcriber should expect,
both spelling and neither mathematics: Roe's `pro2R`/`phiR` are stated at the raw quotient
`FreeProfiniteGroup (Fin 4) ⧸ NR` while `toRoe` lands at the bundled carrier `↑GQ2.GammaR` (so
they need retyping wrappers — the two are defeq, but not at `instances` transparency, which makes
`rw` fail with a confusing "not type-correct" note); and the `Fin` literals in a
`match x with | .wild ⟨0, _⟩` need a `show … (Generator.wild 0) …` to normalise.

⚠ This says nothing about `exactLifting`/`stokes`/`scalar`/`determinant` — AS1's divergence 4,
which needs a `SourceDataN` transport lemma (ticket CB-TRN) and is untouched by anything here.

## Axiom posture

Every declaration is `sorry`-free and introduces **no** axiom.  All fourteen declarations print
exactly the standard three `[propext, Classical.choice, Quot.sound]` — as they must: nothing in
this file touches the arithmetic layers, so neither the frozen `ℚ₂` literature census nor the
dyadic census axioms `B5-K`/`B10-K` can enter.

## Sources

Board `docs/dyadic/tickets.md` lane AS row AS4-b; AS4's inventory and its "⚠ What blocks the last
two rows" note (`GQ2/Dyadic/Instances/QTwo.lean`); AS1's `WordCertificate` field list and
divergence 3 (`GQ2/Dyadic/CertificateMain.lean`).
-/

namespace GQ2

/-! ## §1 The pro-`p` kernel is natural

`proPKernel p G` (`GQ2/MaxProP.lean`) is the intersection of the open normal subgroups with
`p`-group quotient.  That description is manifestly contravariant, and §1 says so.  Everything
here is stated for bare topological groups: no profiniteness, no compactness, no surjectivity.

⚠ **Home.**  These three belong in `GQ2/MaxProP.lean` (AS4's judgement, and the right one — they
mention nothing but `proPKernel`).  They are parked here because that file has another owner; the
move is textual, since `MaxProP.lean` already imports everything they use.  Keeping the `GQ2`
namespace means the move will not rename anything. -/

section ProPKernelNaturality

variable {p : ℕ} {A B : Type*} [Group A] [TopologicalSpace A] [Group B] [TopologicalSpace B]

/-- **Naturality of the pro-`p` kernel.**  For *any* continuous homomorphism `f : A → B`,
`K_p(A) ≤ f⁻¹ K_p(B)`; equivalently `f (K_p(A)) ≤ K_p(B)`.

The proof is the kernel half of `proPKernel_le_ker` with the profiniteness of the target dropped:
for an open normal `V ≤ B` with `p`-group quotient, the composite `φ = (B ↠ B ⧸ V) ∘ f` has open
kernel and `A ⧸ ker φ ≅ range φ ≤ B ⧸ V` is a `p`-group, so `ker φ` lies in the family defining
`K_p(A)`.  **No surjectivity and no compactness are used**, which is what makes this the right
primitive: both directions of `comap_proPKernel` are instances of it. -/
theorem proPKernel_le_comap (f : ContinuousMonoidHom A B) :
    proPKernel p A ≤ Subgroup.comap f.toMonoidHom (proPKernel p B) := by
  intro x hx
  rw [Subgroup.mem_comap, proPKernel, Subgroup.mem_iInf]
  rintro ⟨V, hV⟩
  show f.toMonoidHom x ∈ V.toSubgroup
  set φ : A →* B ⧸ V.toSubgroup := (QuotientGroup.mk' V.toSubgroup).comp f.toMonoidHom with hφ
  have hset : ((φ.ker : Subgroup A) : Set A) = f ⁻¹' (V.toSubgroup : Set B) := by
    ext y
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Iff.rfl
  have hopen : IsOpen ((φ.ker : Subgroup A) : Set A) := by
    rw [hset]
    exact V.toOpenSubgroup.isOpen.preimage f.continuous_toFun
  let U : OpenNormalSubgroup A := { toSubgroup := φ.ker, isOpen' := hopen }
  have hUpg : IsPGroup p (A ⧸ U.toSubgroup) :=
    (hV.to_subgroup φ.range).of_equiv (QuotientGroup.quotientKerEquivRange φ).symm
  have hmem : x ∈ φ.ker := proPKernel_le U hUpg hx
  rwa [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hmem

/-- **AS4's requested lemma.**  A continuous isomorphism pulls the pro-`p` kernel back *exactly*:
`e⁻¹ (K_p(B)) = K_p(A)` for `e : A ≃ₜ* B`.

`≥` is naturality along `e`; `≤` is naturality along `e.symm`, transported across
`e.symm (e x) = x`.  This is what upgrades `WordCertificate.ker_pro2` along an identification of
candidate groups — see `ker_comp_continuousMulEquiv`. -/
theorem comap_proPKernel (e : A ≃ₜ* B) :
    Subgroup.comap (e : ContinuousMonoidHom A B).toMonoidHom (proPKernel p B) = proPKernel p A := by
  refine le_antisymm (fun x hx => ?_) (proPKernel_le_comap (p := p) (e : ContinuousMonoidHom A B))
  have h := proPKernel_le_comap (p := p) (e.symm : ContinuousMonoidHom B A) hx
  rw [Subgroup.mem_comap] at h
  simpa using h

/-- The pushforward form of `comap_proPKernel`: an isomorphism carries the pro-`p` kernel onto the
pro-`p` kernel. -/
theorem map_proPKernel (e : A ≃ₜ* B) :
    Subgroup.map (e : ContinuousMonoidHom A B).toMonoidHom (proPKernel p A) = proPKernel p B := by
  rw [← comap_proPKernel (p := p) e, Subgroup.map_comap_eq_self_of_surjective]
  exact e.surjective

/-- **The consumer's shape.**  If `f : B → P` is *the* maximal pro-`p` quotient map of `B` — i.e.
`ker f = K_p(B)`, which is exactly `WordCertificate.ker_pro2` / `SourceDataN.ker_pro2` — then
`f ∘ e` is the maximal pro-`p` quotient map of `A`, for any continuous isomorphism `e : A ≃ₜ* B`.

Surjectivity transports for free (`e` is onto), so this single lemma is the whole of the
`ker_pro2` + `hpro2` pair under a change of candidate group. -/
theorem ker_comp_continuousMulEquiv {P : Type*} [Group P] [TopologicalSpace P]
    (e : A ≃ₜ* B) (f : ContinuousMonoidHom B P) (hf : f.toMonoidHom.ker = proPKernel p B) :
    (f.comp (e : ContinuousMonoidHom A B)).toMonoidHom.ker = proPKernel p A := by
  rw [show (f.comp (e : ContinuousMonoidHom A B)).toMonoidHom
      = f.toMonoidHom.comp (e : ContinuousMonoidHom A B).toMonoidHom from rfl,
    ← MonoidHom.comap_ker, hf, comap_proPKernel]

end ProPKernelNaturality

namespace Dyadic

/-! ## §2 Maps out of `Γ_R` are determined by the marked letters

The candidate group `Γ_R = F(σ, τ, x₀ … x_n) ⧸ N_R` (`GQ2/Dyadic/AdmissibleR.lean` §3) is a
*topological* quotient of the free profinite group, so `gammaGen n q R` generates it only
topologically.  §2 is the corresponding uniqueness principle, at the weakest target hypothesis
that supports the density argument. -/

section HomExt

variable {n q : ℕ} {R : PWord (Generator n)}

/-- **The marked letters topologically generate `Γ_R`** — `TopGen.map` along the quotient
surjection `F(σ, τ, x₀ … x_n) ↠ Γ_R`, applied to F3's `TopGen.freeProfiniteGroup`.

**The canonical copy** (ticket CB-DD).  Three downstream duplicates — `Count.topGen_gammaR`,
`Count.CorePresentation.topGen_gammaR` and `Count.gammaGen_topGen` — were deleted in favour of
this one, which is the only one upstream of `GQ2.Dyadic.CertificateMain`. -/
theorem topGen_gammaR (n q : ℕ) (R : PWord (Generator n)) :
    (Subgroup.closure (Set.range (gammaGen n q R))).topologicalClosure = ⊤ := by
  have h := TopGen.map (gammaMk n q R).toMonoidHom (gammaMk n q R).continuous_toFun
    (gammaMk_surjective n q R) (TopGen.freeProfiniteGroup (Generator n))
  rwa [← Set.range_comp] at h

/-- **The uniqueness principle, unbundled.**  Two continuous homomorphisms `Γ_R → Q` agreeing on
the `n + 3` marked letters agree everywhere.

The target hypothesis is the weakest one that works: `Q` a **Hausdorff topological group**.  No
compactness, no total disconnectedness, and not even `IsTopologicalGroup Q` — the equalizer is a
subgroup of the *source* and only has to be closed in it. -/
theorem gammaR_monoidHom_eq {Q : Type*} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {f g : ((GammaR n q R) : Type) →* Q} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x : Generator n, f (gammaGen n q R x) = g (gammaGen n q R x)) : ∀ z, f z = g z :=
  TopGen.monoidHom_eq hf hg (topGen_gammaR n q R) (by rintro _ ⟨x, rfl⟩; exact h x)

/-- **The uniqueness principle** (ticket AS4-b, piece 2).  Two *continuous homomorphisms* out of
the candidate group `Γ_R = GammaR n q R` that agree on the marked generators `gammaGen n q R`
are equal.

This is the "generated by the marked letters" principle for `Γ_R`, and the shape consumers want:
any identity between two continuous maps out of `Γ_R` — a `ν`-compatibility square, a boundary
square, a comparison of two lifts through `gammaLift` — reduces to `n + 3` letter computations.

The target class is deliberately as wide as the argument allows (`Group`, `TopologicalSpace`,
`T2Space`); in particular it covers `Ztwo`, `Tq q`, every `ProfiniteGrp` carrier, and every
subgroup of a product of those, with no instance search. -/
theorem gammaR_hom_ext {Q : Type*} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {f g : ContinuousMonoidHom ((GammaR n q R) : Type) Q}
    (h : ∀ x : Generator n, f (gammaGen n q R x) = g (gammaGen n q R x)) : f = g :=
  ContinuousMonoidHom.ext
    (gammaR_monoidHom_eq (f := f.toMonoidHom) (g := g.toMonoidHom)
      f.continuous_toFun g.continuous_toFun h)

/-- The `Marking`-flavoured restatement: two continuous homomorphisms out of `Γ_R` inducing the
same marking of the target are equal.  `gammaMarking n q R` is `Γ_R` marked by its own
generators (`AdmissibleR.lean` §3), so this is `gammaR_hom_ext` read through `Marking.map`. -/
theorem gammaR_hom_ext_marking {Q : Type*} [Group Q] [TopologicalSpace Q] [T2Space Q]
    {f g : ContinuousMonoidHom ((GammaR n q R) : Type) Q}
    (h : (gammaMarking n q R).map ⇑f = (gammaMarking n q R).map ⇑g) : f = g :=
  gammaR_hom_ext fun x => congrArg (fun t : Marking n Q => t x) h

end HomExt

/-! ## §3 The scalar trio at `Γ_R`

`Aut(𝔽₂) = 1`, so a group has exactly one action on `ZMod 2` and it is trivial.  The three
`WordCertificate` fields `smulZmod2` / `contSMulZmod2` / `htriv` are therefore data-plus-two-`rfl`s.
See the module docstring for the inventory row this closes and for the de-duplication note. -/

section Scalar

/-- The trivial `ZMod 2`-action of a monoid.  Deliberately a `def`, not an `instance`: the
certificate records carry the action as *data*, and a global instance on every monoid would shadow
the genuine `ZMod 2`-module structures the `(140)` layer builds.

**The canonical copy** (ticket CB-DD).  `Count.trivialSMulZmodTwo` and `Count.scalarAction` were
deleted in favour of this one; the two inline copies inside the frozen `ℚ₂` proofs
(`GQ2/HalfTorsorGammaA.lean`, `GQ2/HalfTorsorGammaR.lean`) are deliberately kept.  See the module
docstring. -/
@[reducible] def scalarActionZmodTwo (M : Type*) [Monoid M] : DistribMulAction M (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

theorem scalarActionZmodTwo_continuousSMul (M : Type*) [Monoid M] [TopologicalSpace M] :
    letI := scalarActionZmodTwo M; ContinuousSMul M (ZMod 2) :=
  letI := scalarActionZmodTwo M
  ⟨continuous_snd⟩

theorem scalarActionZmodTwo_triv (M : Type*) [Monoid M] :
    letI := scalarActionZmodTwo M; ∀ (γ : M) (m : ZMod 2), γ • m = m :=
  fun _ _ => rfl

variable (n q : ℕ) (R : PWord (Generator n))

/-- **`WordCertificate.smulZmod2` at `Γ_R`**, at the field's verbatim type. -/
@[reducible] noncomputable def gammaRSMulZmod2 :
    DistribMulAction ↥(GammaR n q R) (ZMod 2) :=
  scalarActionZmodTwo _

/-- **`WordCertificate.contSMulZmod2` at `Γ_R`**, at the field's verbatim type. -/
theorem gammaRContSMulZmod2 :
    letI := gammaRSMulZmod2 n q R; ContinuousSMul ↥(GammaR n q R) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **`WordCertificate.htriv` at `Γ_R`**, at the field's verbatim type. -/
theorem gammaR_htriv :
    letI := gammaRSMulZmod2 n q R; ∀ (γ : ↥(GammaR n q R)) (m : ZMod 2), γ • m = m :=
  scalarActionZmodTwo_triv _

end Scalar

end Dyadic

end GQ2
