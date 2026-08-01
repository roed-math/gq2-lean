/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Words.N0

/-!
# The generic candidate-side pro-`2` bridge  (dyadic campaign, ticket CB-P)

**`Γ_R(2) ≅ D_P`, once, over an abstract presented core** — the group-level statement that
`GQ2/Dyadic/CertificateMain.lean`'s `WordCertificate` needs and that AS1's *finding 3* recorded
as unbuilt.

## The gap this closes

All five branch lanes landed the **word-level** pro-2 specialization
(`Words/{N0, M0, Npc, Mpc, L}.lean`'s `eval_pro2_*`): the pro-2 specialization `pro2 R` of the
branch word evaluates, at every marking of every profinite group, to the standard core's relator.
AS1 observed — correctly — that this is a statement about *words*, whereas `SourceDataN` needs a
statement about *groups*: a map `pro2 : Γ_R → D_P` that **is** the maximal pro-2 quotient map.
This file is the passage between them.

## What is generalized, and what is deliberately not

The `ℚ₂` ancestor of the group-level statement is `GQ2.Roe.exists_pro2R`
(`GQ2/Roe/Main.lean:226`), and it consumes `BLabHypothesis`.  **It is the wrong thing to
generalize.**  `exists_pro2R` is the four-fold composite `eA ∘ e⁻¹ ∘ maxPro2Bridge ∘ maxProPMk`,
of which three legs are *arithmetic*: they exist only because `ℚ₂`'s pro-2 boundary object
`PiBd` is not a presented core, so the chain had to detour through `G_{ℚ₂}(2)` — which is where
Labute lives.  The one **candidate-side** leg is `maxPro2Bridge`
(`GQ2/Roe/MaxPro2Bridge.lean:426`), 504 lines with zero occurrences of `BLab`, and it is the only
leg the campaign's two-sided design needs, because in `SourceDataN` the pro-2 slot `P` *is* the
presented standard core `D_P` (MC2's `DM`/`DN`, SqCore's `DSq`).

So this file generalizes `maxPro2Bridge` and **not** `exists_pro2R`.  The Labute-type content
stays on the arithmetic side, where it already lives: `MarkedCoreCertificateM/N.abstractEquiv`
(`GQ2/Dyadic/MarkedCore/Certificate.lean:629,645`), consumed by ticket ASK.  Inheriting it here
would have pinned a rank-3, `q = 2` hypothesis (`BLabHypothesis` is literally
`demushkinRank 2 (DR) = 3 → demushkinQ (DR) = 2 → …`) onto a rank-`4 + 2h` candidate side, which
is both wrong and unusable.  **Every headline below prints the standard three axioms; no
declaration in this file mentions `BLabHypothesis`, `MLabHypothesis`, `NLabHypothesis`, or any
B-set axiom.**

## The architecture

The bridge is `maxPro2Bridge`'s architecture with the concrete `D_R` replaced by an abstract
`CorePresentation` (§1) — the core, *in alphabet coordinates*, together with its pro-2 universal
property.  Then:

* **forward** `PhiMax : Γ_R(2) → P` — F3's `prop_3_4_two` (`GQ2/Dyadic/TameBoundary.lean:640`)
  applied to the core's own marking, descended through the maximal pro-2 quotient
  (`proPKernel_le_ker`, since `P` is pro-2).  `prop_3_4_two` is exactly `maxPro2Bridge`'s
  "`R`-admissibility at every finite 2-group level" step, already done generically by F3 — which
  is why this file is a fraction of the ℚ₂ file's length;
* **backward** `PsiMax : P → Γ_R(2)` — the core's own universal property at the tautological
  marking of `Γ_R(2)`, whose two obligations are `τ`-death (`map_gammaGen_tau_eq_one_of_isProP`,
  F3's, generic: tame ⇒ odd order ⇒ trivial in a 2-group) and `maxMarking.eval (pro2 R) = 1`
  (F2's `Marking.eval_pro2` plus `gammaMarking_eval_R`);
* **mutual inverse** by `CorePresentation.hom_ext` one way and topological generation of `Γ_R(2)`
  the other (§2 — `topGen_gammaR` did not exist and is proved here, two lines from F3's
  `TopGen.map`).

Note the *keystone* of the ℚ₂ file, `wildValueR_eq_drWord_of_powOmega2_id` ("in a 2-group the wild
value of the marking **is** the core relator"), is exactly `WordCertificate.proTwoWord`, and it is
landed for all five branches.  Here it enters through `CoreReindex` (§6): it is `hword`.

## What it delivers

§5 supplies, at the abstract core, the four `WordCertificate` fields the bridge owes:

| field | here |
|---|---|
| `pro2 : ContinuousMonoidHom Γ_R P` | `coreHom` |
| `ker_pro2 : ker = proPKernel 2 Γ_R` | `ker_coreHom` |
| `hpro2 : Surjective` | `coreHom_surjective` |
| `compat : ν_{T_q} ∘ tame = ν_P ∘ pro2` | `nu_compat_coreHom` |

`compat` is the one that takes extra input, and only the unavoidable amount: the core's own
ν-normalization `ν_P(σ) = 1`, `ν_P(x_i) = 0` (§5).  Everything else is hypothesis-free given the
`CorePresentation`.

§6 builds a `CorePresentation` from the inputs the campaign already has — `WordCoh.PresentedBy`
for the core (`presentedBy_DM`/`_DN`, landed) plus a `CoreReindex`: the branch's dictionary
between alphabet letters and core generators, with its section.  §7 instantiates the whole stack
at the pilot branch, compact `N`, against `Words/N0.lean`'s landed `eval_pro2_nCompact`.

## Module style

`GQ2/Roe/MaxPro2Bridge.lean` is `module`-style.  **This file is plain**, and is forced to be: its
consumer `GQ2/Dyadic/CertificateMain.lean` and its input `GQ2/Dyadic/Words/N0.lean` are both
plain `import` files, and a module file cannot import a non-module one.

## Sources

Packet `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` Prop. 3.4(2); Roe note
Lemma 3.1 ⟦lem:pro2word⟧ (the `ℚ₂` instance); CB1's memo `docs/dyadic/cb-design.md` §4.
-/

namespace GQ2.Dyadic.Count

-- ORCHESTRATOR MERGE FIX 2026-08-01: branch predated AS1-b's deletion of AS1's §2b
-- top-level `TameSpecializes`/`tameOfSpec` in favour of F3b's `TameSpec` namespace;
-- `open TameSpec` re-resolves the bare identifiers (same adaptation as AS1-b and CB-0).
open GQ2 GQ2.Dyadic GQ2.Dyadic.TameSpec

/-! ## §1 The core, in alphabet coordinates

`WordCoh.PresentedBy` presents a group on *its own* generator index type `X`.  The bridge has to
compare it with `Γ_R`, whose generators are the alphabet `Generator n = {σ, τ, x₀, …, x_n}`.  The
record below is `PresentedBy` transported into alphabet coordinates, with `τ` sent to `1` — which
is the only shape in which the two universal properties are directly comparable, since F3's
`prop_3_4_two` is stated at `Marking n Q`.

§6 constructs this from a landed `PresentedBy` plus the branch's reindexing dictionary, so no
branch has to build it by hand. -/

/-- **The presented core, in alphabet coordinates.**

`P` is a pro-2 group carrying a marking `mark` of the alphabet with `τ ↦ 1`, at which the pro-2
specialization `pro2 R` of the branch word vanishes, and which presents `P` among pro-2 groups:
every relator-killing, `τ`-killing alphabet marking of a pro-2 group extends over `P`, uniquely.

This is `GQ2.Roe.DRPresentation`'s `(drS, drX, drY)` + `drLiftHom` + `dr_hom_ext` package, made
alphabet-indexed and rank-generic.  Note it does **not** mention `q`: the core knows nothing about
the tame modulus, which is precisely why the bridge below is uniform in `q`. -/
structure CorePresentation (n : ℕ) (R : PWord (Generator n)) (P : ProfiniteGrp.{0}) where
  /-- The core is pro-2. -/
  isProP : IsProP 2 (P : Type)
  /-- The core's marking of the alphabet `σ, τ, x₀, …, x_n`. -/
  mark : Marking n (P : Type)
  /-- `τ` is not a generator of the core. -/
  mark_tau : mark.τ = 1
  /-- The core relation: the pro-2 specialization of the branch word dies at `mark`. -/
  rel : mark.eval (pro2 R) = 1
  /-- **Universal property, existence.**  Any pro-2 marking killing `τ` and the relator extends. -/
  liftHom : ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
    [T2Space Q] [TotallyDisconnectedSpace Q], IsProP 2 Q → ∀ t : Marking n Q, t.τ = 1 →
    t.eval (pro2 R) = 1 → ContinuousMonoidHom (P : Type) Q
  /-- **Universal property, computation.** -/
  liftHom_mark : ∀ {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] (hQ : IsProP 2 Q)
    (t : Marking n Q) (hτ : t.τ = 1) (hrel : t.eval (pro2 R) = 1) (g : Generator n),
    liftHom hQ t hτ hrel (mark g) = t g
  /-- **Universal property, uniqueness.**  Continuous homs out of `P` are pinned on `mark`.

  Stated at *profinite* targets only — weaker than `WordCoh.PresentedBy.hom_ext`, which asks for
  merely-`T2` targets, and therefore easier to supply.  The bridge uses it once, at `A = P`. -/
  hom_ext : ∀ {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [CompactSpace A]
    [T2Space A] [TotallyDisconnectedSpace A]
    (φ ψ : ContinuousMonoidHom (P : Type) A), (∀ g, φ (mark g) = ψ (mark g)) → φ = ψ

namespace CorePresentation

variable {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp.{0}}

/-! ## §2 Topological generation of `Γ_R` and of `Γ_R(2)`

`GQ2/Roe/MaxPro2Bridge.lean:375`'s `topGen_maxR`, rank-generic.  Neither statement existed in the
dyadic tree: `TameBoundary.lean` has `topGen_tameGammaR` for the *tame* quotient `Γ_R/W_R` but not
for `Γ_R` itself, and `CertificateMain.lean:435` records the omission ("routine, but nobody has
written them for `GammaR`").  Both are pushforwards of F3's `TopGen.freeProfiniteGroup` along
quotient surjections. -/

/-- The image of the alphabet topologically generates `Γ_R` — `TopGen.map` along
`F(Generator n) ↠ Γ_R`. -/
theorem topGen_gammaR (n q : ℕ) (R : PWord (Generator n)) :
    (Subgroup.closure (Set.range (gammaGen n q R))).topologicalClosure = ⊤ := by
  have h := TopGen.map (gammaMk n q R).toMonoidHom (gammaMk n q R).continuous_toFun
    (gammaMk_surjective n q R)
    (TopGen.freeProfiniteGroup (Generator n))
  rwa [← Set.range_comp] at h

/-- The image of the alphabet topologically generates `Γ_R(2)` — one more `TopGen.map`, along
`Γ_R ↠ Γ_R(2)`. -/
theorem topGen_maxGammaR (n q : ℕ) (R : PWord (Generator n)) :
    (Subgroup.closure (Set.range fun g : Generator n =>
      maxProPMk 2 ((GammaR n q R) : Type) (gammaGen n q R g))).topologicalClosure = ⊤ := by
  have h := TopGen.map (maxProPMk 2 ((GammaR n q R) : Type)).toMonoidHom
    (maxProPMk 2 ((GammaR n q R) : Type)).continuous_toFun
    (quotientMk_surjective (proPKernel 2 ((GammaR n q R) : Type)))
    (topGen_gammaR n q R)
  rwa [← Set.range_comp] at h

/-! ## §3 The tautological marking of `Γ_R(2)`

The two obligations the backward map needs, both generic and both F3's or F2's. -/

/-- The tautological marking of `Γ_R(2)`: push the alphabet through `Γ_R ↠ Γ_R(2)`. -/
noncomputable def maxMarking (n q : ℕ) (R : PWord (Generator n)) :
    Marking n ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type) :=
  (gammaMarking n q R).map ⇑(maxProPMk 2 ((GammaR n q R) : Type))

@[simp] theorem maxMarking_apply (n q : ℕ) (R : PWord (Generator n)) (g : Generator n) :
    maxMarking n q R g = maxProPMk 2 ((GammaR n q R) : Type) (gammaGen n q R g) := rfl

/-- **`τ` dies in `Γ_R(2)`.**  `MaxPro2Bridge.lean:271`'s `maxProPMk_gammaTauR`, rank-generic —
and here it is not re-proved at all: F3's `map_gammaGen_tau_eq_one_of_isProP` is already the
statement for *every* pro-2 target, and `Γ_R(2)` is pro-2. -/
theorem maxMarking_tau (hq0 : q ≠ 0) (hqe : Even q) : (maxMarking n q R).τ = 1 :=
  map_gammaGen_tau_eq_one_of_isProP hq0 hqe isProP_maxProPQuotient
    (maxProPMk 2 ((GammaR n q R) : Type))

/-- **The relator dies in `Γ_R(2)`.**  `MaxPro2Bridge.lean:303`'s `drWord_maxR_eq_one`,
rank-generic: `pro2 R` and `R` have the same value at any marking that kills `τ` and is
`ω₂`-trivial (F2's `Marking.eval_pro2`), and `R` dies in `Γ_R` by construction. -/
theorem maxMarking_eval (hq0 : q ≠ 0) (hqe : Even q) :
    (maxMarking n q R).eval (pro2 R) = 1 := by
  have hω : ∀ x : ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type), x ^ᶻ omega2 = x :=
    zpowHat_omega2_eq_self_of_isProP isProP_maxProPQuotient
  rw [Marking.eval_pro2 _ (maxMarking_tau hq0 hqe) hω R, maxMarking,
    ← Marking.map_eval (maxProPMk 2 ((GammaR n q R) : Type)) (gammaMarking n q R) R,
    gammaMarking_eval_R, map_one]

/-! ## §4 The bridge `Γ_R(2) ≅ D_P`

`GQ2/Roe/MaxPro2Bridge.lean`'s `PhiMaxR` / `PsiMaxR` / `maxPro2Bridge`, over an abstract
`CorePresentation`. -/

section Bridge

variable (CP : CorePresentation n R P) (hq0 : q ≠ 0) (hqe : Even q)

/-- **The classifier `Γ_R → P`** (`MaxPro2Bridge.lean:205`'s `phiDR`): F3's `prop_3_4_two`, whose
two hypotheses are exactly the `CorePresentation`'s `mark_tau` and `rel`.  This is where the ℚ₂
file's whole "`R`-admissible at every finite 2-group level of `D_R`" argument sits, already done
generically. -/
noncomputable def coreHom : ContinuousMonoidHom ((GammaR n q R) : Type) (P : Type) :=
  ((prop_3_4_two (R := R) hq0 hqe P CP.isProP CP.mark).mpr ⟨CP.mark_tau, CP.rel⟩).choose

@[simp] theorem coreHom_gammaGen (g : Generator n) :
    coreHom CP hq0 hqe (gammaGen n q R g) = CP.mark g :=
  ((prop_3_4_two (R := R) hq0 hqe P CP.isProP CP.mark).mpr ⟨CP.mark_tau, CP.rel⟩).choose_spec g

/-- **The forward map `Φ : Γ_R(2) → P`** (`MaxPro2Bridge.lean:232`'s `PhiMaxR`): the descent of
the classifier, which kills the pro-2 kernel because `P` is pro-2. -/
noncomputable def PhiMax :
    ContinuousMonoidHom ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type) (P : Type) :=
  quotientLift (proPKernel 2 ((GammaR n q R) : Type)) (coreHom CP hq0 hqe)
    (proPKernel_le_ker CP.isProP _)

@[simp] theorem PhiMax_maxMarking (g : Generator n) :
    PhiMax CP hq0 hqe (maxMarking n q R g) = CP.mark g :=
  (quotientLift_quotientMk _ _ _ _).trans (coreHom_gammaGen CP hq0 hqe g)

/-- `Φ ∘ (Γ_R ↠ Γ_R(2)) = ` the classifier, on the nose. -/
theorem PhiMax_maxProPMk (g : ((GammaR n q R) : Type)) :
    PhiMax CP hq0 hqe (maxProPMk 2 ((GammaR n q R) : Type) g) = coreHom CP hq0 hqe g := rfl

/-- **The backward map `Ψ : P → Γ_R(2)`** (`MaxPro2Bridge.lean:352`'s `PsiMaxR`): the core's own
universal property at the tautological marking of `Γ_R(2)`, whose two obligations are §3. -/
noncomputable def PsiMax :
    ContinuousMonoidHom (P : Type) ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type) :=
  CP.liftHom isProP_maxProPQuotient (maxMarking n q R) (maxMarking_tau hq0 hqe)
    (maxMarking_eval hq0 hqe)

@[simp] theorem PsiMax_mark (g : Generator n) :
    PsiMax CP hq0 hqe (CP.mark g) = maxMarking n q R g :=
  CP.liftHom_mark _ _ _ _ g

/-- `Φ ∘ Ψ = id` on the core — both fix `mark`, and `hom_ext` pins them. -/
theorem PhiMax_PsiMax (x : (P : Type)) : PhiMax CP hq0 hqe (PsiMax CP hq0 hqe x) = x := by
  have h : (PhiMax CP hq0 hqe).comp (PsiMax CP hq0 hqe) = ContinuousMonoidHom.id (P : Type) :=
    CP.hom_ext _ _ fun g => by
      show PhiMax CP hq0 hqe (PsiMax CP hq0 hqe (CP.mark g)) = CP.mark g
      rw [PsiMax_mark, PhiMax_maxMarking]
  exact DFunLike.congr_fun h x

/-- `Ψ ∘ Φ = id` on `Γ_R(2)` — checked on the alphabet images, which topologically generate (§2). -/
theorem PsiMax_PhiMax (x : ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type)) :
    PsiMax CP hq0 hqe (PhiMax CP hq0 hqe x) = x := by
  refine SectionThree.monoidHom_eq_of_topGen
    (f := (PsiMax CP hq0 hqe).toMonoidHom.comp (PhiMax CP hq0 hqe).toMonoidHom)
    (g := MonoidHom.id _)
    (by rw [MonoidHom.coe_comp]
        exact (PsiMax CP hq0 hqe).continuous_toFun.comp (PhiMax CP hq0 hqe).continuous_toFun)
    continuous_id (topGen_maxGammaR n q R) ?_ x
  rintro z ⟨g, rfl⟩
  show PsiMax CP hq0 hqe (PhiMax CP hq0 hqe (maxMarking n q R g)) = maxMarking n q R g
  rw [PhiMax_maxMarking, PsiMax_mark]

/-- **The maximal pro-2 quotient of the candidate group is the presented core**: a continuous
isomorphism `Γ_R(2) ≅ D_P` matching the marked generators.

This is the rank-generic, Labute-free generalization of `GQ2.maxPro2Bridge`
(`GQ2/Roe/MaxPro2Bridge.lean:426`), which is the `ℚ₂` instance at `n = 1`, `q = 2`, `P = D_R`. -/
noncomputable def maxProTwoBridge :
    ContinuousMulEquiv ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type) (P : Type) where
  toFun := PhiMax CP hq0 hqe
  invFun := PsiMax CP hq0 hqe
  left_inv := PsiMax_PhiMax CP hq0 hqe
  right_inv := PhiMax_PsiMax CP hq0 hqe
  map_mul' := map_mul (PhiMax CP hq0 hqe)
  continuous_toFun := (PhiMax CP hq0 hqe).continuous_toFun
  continuous_invFun := (PsiMax CP hq0 hqe).continuous_toFun

@[simp] theorem maxProTwoBridge_apply (x : ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type)) :
    maxProTwoBridge CP hq0 hqe x = PhiMax CP hq0 hqe x := rfl

/-- The bridge in existence shape, with its marked generator images — the interface a
`WordCertificate` producer consumes. -/
theorem maxProTwoBridge_spec (CP : CorePresentation n R P) (hq0 : q ≠ 0) (hqe : Even q) :
    ∃ e : ContinuousMulEquiv ((maxProPQuotient 2 ((GammaR n q R) : Type)) : Type) (P : Type),
      ∀ g : Generator n, e (maxMarking n q R g) = CP.mark g :=
  ⟨maxProTwoBridge CP hq0 hqe, fun g => PhiMax_maxMarking CP hq0 hqe g⟩

/-! ## §5 The four `WordCertificate` pro-2 fields

`GQ2/Dyadic/CertificateMain.lean:465-473` asks for `pro2`, `ker_pro2`, `hpro2` and `compat`.
`coreHom` is the first; the other three follow from the bridge.  The `ℚ₂` analogue of the bundle
is `GQ2.Roe.exists_pro2R` (`GQ2/Roe/Main.lean:226`) — **which takes `hBLab` and this does not**. -/

/-- **`ker_pro2`.**  `coreHom` *is* the maximal pro-2 quotient map: `P` is pro-2 so the pro-2
kernel dies (`proPKernel_le_ker`), and nothing more does, because the induced map on `Γ_R(2)` is
the bridge, an isomorphism. -/
theorem ker_coreHom :
    (coreHom CP hq0 hqe).toMonoidHom.ker = proPKernel 2 ((GammaR n q R) : Type) := by
  refine le_antisymm (fun g hg => ?_) (proPKernel_le_ker CP.isProP _)
  have hg' : coreHom CP hq0 hqe g = 1 := MonoidHom.mem_ker.mp hg
  refine (quotientMk_eq_one_iff (proPKernel 2 ((GammaR n q R) : Type))).mp ?_
  have h := PsiMax_PhiMax CP hq0 hqe (maxProPMk 2 ((GammaR n q R) : Type) g)
  rw [PhiMax_maxProPMk, hg', map_one] at h
  exact h.symm

/-- **`hpro2`.**  Surjective: the bridge is bijective and `Γ_R ↠ Γ_R(2)` is onto. -/
theorem coreHom_surjective : Function.Surjective (coreHom CP hq0 hqe) := fun y => by
  obtain ⟨g, hg⟩ :=
    quotientMk_surjective (proPKernel 2 ((GammaR n q R) : Type)) (PsiMax CP hq0 hqe y)
  refine ⟨g, ?_⟩
  rw [← PhiMax_maxProPMk CP hq0 hqe g,
    show maxProPMk 2 ((GammaR n q R) : Type) g = PsiMax CP hq0 hqe y from hg, PhiMax_PsiMax]

/-- `τ` dies under `pro2`, the marked shape `exists_pro2R`'s last conjunct records. -/
@[simp] theorem coreHom_tau : coreHom CP hq0 hqe (gammaGen n q R .tau) = 1 :=
  (coreHom_gammaGen CP hq0 hqe .tau).trans CP.mark_tau

/-- **`compat`.**  ν-compatibility of the tame and pro-2 legs, checked on the alphabet (§2's
`topGen_gammaR`) against the core's own ν-normalization.  The two hypotheses are exactly F3's
`prop_3_4_three` on the core side: `ν_P(σ) = 1`, `ν_P(x_i) = 0`. -/
theorem nu_compat_coreHom (hspec : TameSpecializes n q R)
    (nuP : ContinuousMonoidHom (P : Type) Ztwo)
    (hnuSigma : nuP (CP.mark .sigma) = ztwoOne)
    (hnuWild : ∀ i : Fin (n + 1), nuP (CP.mark (.wild i)) = 1) (g : ((GammaR n q R) : Type)) :
    nuTq q (tameOfSpec n q R hspec g) = nuP (coreHom CP hq0 hqe g) := by
  refine SectionThree.monoidHom_eq_of_topGen
    (f := (nuTq q).toMonoidHom.comp (tameOfSpec n q R hspec).toMonoidHom)
    (g := nuP.toMonoidHom.comp (coreHom CP hq0 hqe).toMonoidHom)
    (by rw [MonoidHom.coe_comp]
        exact (nuTq q).continuous_toFun.comp (tameOfSpec n q R hspec).continuous_toFun)
    (by rw [MonoidHom.coe_comp]
        exact nuP.continuous_toFun.comp (coreHom CP hq0 hqe).continuous_toFun)
    (topGen_gammaR n q R) ?_ g
  rintro z ⟨x, rfl⟩
  show nuTq q (tameOfSpec n q R hspec (gammaGen n q R x))
    = nuP (coreHom CP hq0 hqe (gammaGen n q R x))
  rw [tameOfSpec_gammaGen, coreHom_gammaGen]
  cases x with
  | sigma => rw [show tameMarking n q Generator.sigma = tqSigma q from rfl, nuTq_tqSigma]
             exact hnuSigma.symm
  | tau => rw [show tameMarking n q Generator.tau = tqTau q from rfl, nuTq_tqTau,
             show CP.mark Generator.tau = 1 from CP.mark_tau, map_one]
  | wild i => rw [show tameMarking n q (Generator.wild i) = 1 from rfl, map_one,
                (hnuWild i)]

/-- **The pro-2 bundle**, in the existence shape of `GQ2.Roe.exists_pro2R`
(`GQ2/Roe/Main.lean:226`) — *without* its `BLabHypothesis` binder, and at any rank.

Read against the ℚ₂ statement: `exists_pro2R (hBLab : BLabHypothesis) : ∃ pro2R, … ` lands in
`PiBd`, the pro-2 boundary object of the one-sided record, and so had to route through
`G_{ℚ₂}(2)`; here the target is the presented core itself, which is what the two-sided
`SourceDataN` slot asks for, and the arithmetic legs — with the Labute content — are gone. -/
theorem exists_proTwo (CP : CorePresentation n R P) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes n q R) (nuP : ContinuousMonoidHom (P : Type) Ztwo)
    (hnuSigma : nuP (CP.mark .sigma) = ztwoOne)
    (hnuWild : ∀ i : Fin (n + 1), nuP (CP.mark (.wild i)) = 1) :
    ∃ pro2G : ContinuousMonoidHom ((GammaR n q R) : Type) (P : Type),
      Function.Surjective pro2G ∧
      pro2G.toMonoidHom.ker = proPKernel 2 ((GammaR n q R) : Type) ∧
      (∀ g, nuTq q (tameOfSpec n q R hspec g) = nuP (pro2G g)) ∧
      pro2G (gammaGen n q R .tau) = 1 :=
  ⟨coreHom CP hq0 hqe, coreHom_surjective CP hq0 hqe, ker_coreHom CP hq0 hqe,
    nu_compat_coreHom CP hq0 hqe hspec nuP hnuSigma hnuWild, coreHom_tau CP hq0 hqe⟩

end Bridge

end CorePresentation

/-! ## §6 Building a `CorePresentation` from the campaign's landed inputs

CB1's memo lists what the generic bridge needs and what already exists:

| input | status |
|---|---|
| word-level `t.eval (pro2 R) = coreRel G t` | landed, all five (`eval_pro2_*`) |
| `PresentedBy` for the core `D_P` | landed (`presentedBy_DM`/`_DN`, `MarkedCore/Certificate.lean:278,285`) |
| the core relation `W.ev μ = 1` | landed (`dm_relation`/`dn_relation`/`dsq_relation`) |
| `R`-admissibility at finite 2-group levels | **not needed** — F3's `prop_3_4_two` already did it generically |
| `τ` dies pro-2 | **not needed** — F3's `map_gammaGen_tau_eq_one_of_isProP` |

The one thing not on that list, and the only per-branch work left, is the **dictionary** between
the alphabet `{σ, τ, x₀, …, x_n}` and the core's index type `X = Fin (4 + 2h)` (or
`Fin (3 + 2h)`).  It is genuinely branch data: N0 and L read core generators straight off letters,
while M0/Npc/Mpc read *twisted* combinations (`(x₀)⁻¹ σ^{-m}`, `σ^{η̂}`, `x₁ σ^{2^r}`, …).  A
`CoreReindex` is that dictionary together with its inverse — which exists for all five, since each
branch's twist is a triangular change of generators.

Note the memo's estimate of "`~80–150` lines per branch" is exactly the cost of a `CoreReindex`. -/

/-- **The alphabet ↔ core-index dictionary.**  `mk` reads a core marking off an alphabet marking
(this is the map appearing on the right of every branch's `eval_pro2_*`), `un` reads an alphabet
marking off a core marking, sending `τ ↦ 1`; the two are mutually inverse on `τ`-trivial markings
and natural in continuous homomorphisms.

For the untwisted branches `toCore t = t ∘ ι` for a letter table `ι : X → Generator n`, and
`ofCore` is its inverse table with `τ ↦ 1`; the twisted branches use genuine words in the letters,
which is why both are stated over profinite `G` (`Npc`'s dictionary uses a `Ẑ`-power `σ^{η̂}`). -/
structure CoreReindex (n : ℕ) (X : Type) where
  /-- Alphabet marking ↦ core marking. -/
  toCore : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G], Marking n G → (X → G)
  /-- Core marking ↦ alphabet marking, with `τ ↦ 1`. -/
  ofCore : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G], (X → G) → Marking n G
  /-- `ofCore` never uses `τ`. -/
  ofCore_tau : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (m : X → G), (ofCore m).τ = 1
  /-- Round trip on core markings. -/
  toCore_ofCore : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (m : X → G),
    toCore (ofCore m) = m
  /-- Round trip on `τ`-trivial alphabet markings. -/
  ofCore_toCore : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (t : Marking n G),
    t.τ = 1 → ofCore (toCore t) = t
  /-- `toCore` is natural. -/
  toCore_nat : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (f : ContinuousMonoidHom G H) (t : Marking n G) (k : X), f (toCore t k) = toCore (t.map ⇑f) k
  /-- `ofCore` is natural. -/
  ofCore_nat : ∀ {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (f : ContinuousMonoidHom G H) (m : X → G) (g : Generator n),
    f (ofCore m g) = ofCore (fun k => f (m k)) g

namespace CorePresentation

variable {n : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp.{0}}

/-- **The constructor.**  A landed `WordCoh.PresentedBy` for the core, its relation, a
`CoreReindex`, and the branch's landed word-level pro-2 specialization assemble into the
alphabet-coordinate presentation the bridge consumes.

`hword` is `WordCertificate.proTwoWord` with `coreRel G t` unfolded to `W.ev (rx.toCore t)` — the
five `Words/*.lean` files prove exactly this shape.  Nothing here is Labute-shaped: the only
core-side inputs are a presentation and a relation. -/
noncomputable def ofPresentedBy {X : Type} {W : WordCoh.NatWord X} {μ : X → (P : Type)}
    (hP : IsProP 2 (P : Type)) (pres : WordCoh.PresentedBy (P : Type) W μ) (hrel : W.ev μ = 1)
    (rx : CoreReindex n X)
    (hword : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
      [T2Space G] [TotallyDisconnectedSpace G] (t : Marking n G),
      t.eval (pro2 R) = W.ev (rx.toCore t)) :
    CorePresentation n R P where
  isProP := hP
  mark := rx.ofCore μ
  mark_tau := rx.ofCore_tau μ
  rel := by rw [hword, rx.toCore_ofCore]; exact hrel
  liftHom := fun hQ t _ hrelt => pres.liftHom hQ (rx.toCore t) (by rw [← hword]; exact hrelt)
  liftHom_mark := fun hQ t hτ hrelt g => by
    rw [rx.ofCore_nat]
    have hpt : (fun k => pres.liftHom hQ (rx.toCore t) (by rw [← hword]; exact hrelt) (μ k))
        = rx.toCore t := funext fun k => pres.liftHom_mark hQ (rx.toCore t) _ k
    rw [hpt, rx.ofCore_toCore t hτ]
  hom_ext := fun φ ψ h => pres.hom_ext φ ψ fun k => by
    have hmap : (rx.ofCore μ).map ⇑φ = (rx.ofCore μ).map ⇑ψ := Marking.ext fun g => h g
    calc φ (μ k) = φ (rx.toCore (rx.ofCore μ) k) := by rw [rx.toCore_ofCore]
      _ = rx.toCore ((rx.ofCore μ).map ⇑φ) k := rx.toCore_nat φ _ k
      _ = rx.toCore ((rx.ofCore μ).map ⇑ψ) k := by rw [hmap]
      _ = ψ (rx.toCore (rx.ofCore μ) k) := (rx.toCore_nat ψ _ k).symm
      _ = ψ (μ k) := by rw [rx.toCore_ofCore]

end CorePresentation

/-! ## §7 The pilot: compact `N` at rank `4 + 2h`

AS2's branch.  Everything below is the per-branch cost of the bridge, and it is exactly one
`CoreReindex` plus one restatement of a landed theorem.

The dictionary: the compact-`N` core `D_N` has rank `coreRank h = 4 + 2h` with letters
`(x₀, x₁, σ, x₂)` at indices `0, 1, 2, 3` (note `σ` sits at **index 2**, not 0) and the handle pair
`(u_j, v_j)` at `4 + 2j, 5 + 2j`; the alphabet at `n = 2 + 2h` is `(σ, τ, x₀, …, x_{2+2h})` with the
handle letters at `x_{3+2j}, x_{4+2j}`.  So the table is "delete `τ`, and move `σ` into slot 2",
i.e. wild letter `x_j` sits at core index `j` for `j ≤ 1` and at `j + 1` for `j ≥ 2`. -/

namespace PilotN

open GQ2.Dyadic.Words GQ2.Dyadic.MarkedCore

/-- Core generator index ↦ alphabet letter: `0 ↦ x₀`, `1 ↦ x₁`, `2 ↦ σ`, `3 ↦ x₂`,
`4 + 2j ↦ x_{3+2j}`, `5 + 2j ↦ x_{4+2j}`. -/
def nIdx (h : ℕ) (i : Fin (coreRank h)) : Generator (2 + 2 * h) :=
  if (i : ℕ) = 2 then .sigma
  else .wild ⟨if (i : ℕ) ≤ 1 then (i : ℕ) else (i : ℕ) - 1, by
    have := i.isLt; simp only [coreRank] at this; split <;> omega⟩

/-- Wild-letter index ↦ core generator index (the inverse table off `σ`). -/
def nWildIdx (h : ℕ) (j : Fin (2 + 2 * h + 1)) : Fin (coreRank h) :=
  ⟨if (j : ℕ) ≤ 1 then (j : ℕ) else (j : ℕ) + 1, by
    have := j.isLt; simp only [coreRank]; split <;> omega⟩

/-- The core index carrying `σ`. -/
def nSigmaIdx (h : ℕ) : Fin (coreRank h) := ⟨2, by simp only [coreRank]; omega⟩

@[simp] theorem nIdx_nSigmaIdx (h : ℕ) : nIdx h (nSigmaIdx h) = .sigma := rfl

@[simp] theorem nIdx_nWildIdx (h : ℕ) (j : Fin (2 + 2 * h + 1)) :
    nIdx h (nWildIdx h j) = .wild j := by
  have hj := j.isLt
  simp only [nIdx, nWildIdx]
  rw [if_neg (by split <;> omega)]
  congr 1
  exact Fin.ext (by simp only; split_ifs <;> omega)

/-- **The compact-`N` dictionary.** -/
noncomputable def nReindex (h : ℕ) : CoreReindex (2 + 2 * h) (Fin (coreRank h)) where
  toCore := fun t i => t (nIdx h i)
  ofCore := fun m => Marking.ofLetters (m (nSigmaIdx h)) 1 (fun j => m (nWildIdx h j))
  ofCore_tau := fun _ => rfl
  toCore_ofCore := fun m => by
    funext i
    have hi := i.isLt
    simp only [coreRank] at hi
    by_cases h2 : (i : ℕ) = 2
    · have : nIdx h i = .sigma := by simp only [nIdx, if_pos h2]
      rw [this]
      exact congrArg m (Fin.ext (by simp only [nSigmaIdx]; omega))
    · have hne : nIdx h i
          = .wild ⟨if (i : ℕ) ≤ 1 then (i : ℕ) else (i : ℕ) - 1, by split <;> omega⟩ := by
        simp only [nIdx, if_neg h2]
      rw [hne]
      exact congrArg m (Fin.ext (by simp only [nWildIdx]; split_ifs <;> omega))
  ofCore_toCore := fun t ht => by
    ext g
    cases g with
    | sigma => rfl
    | tau => exact ht.symm
    | wild j => exact congrArg t (nIdx_nWildIdx h j)
  toCore_nat := fun _ _ _ => rfl
  ofCore_nat := fun f m g => by cases g with
    | sigma => rfl
    | tau => exact map_one f
    | wild _ => rfl

/-- Off the `σ` slot, `nIdx` is a wild letter — in the form that identifies the letter *without*
rewriting under the `Fin.mk` proof term (which is motive-unsound: the inner `if` occurs in both
the value and its bound proof). -/
theorem nIdx_eq_wild (h : ℕ) (i : Fin (coreRank h)) (h2 : (i : ℕ) ≠ 2)
    (j : Fin (2 + 2 * h + 1)) (hj : (j : ℕ) = if (i : ℕ) ≤ 1 then (i : ℕ) else (i : ℕ) - 1) :
    nIdx h i = .wild j := by
  simp only [nIdx, if_neg h2]
  exact congrArg Generator.wild (Fin.ext hj.symm)

@[simp] theorem nIdx_zero (h : ℕ) : nIdx h 0 = coreLetter h 0 :=
  nIdx_eq_wild h 0 (by rw [coreVal_zero]; omega) _ (by rw [coreVal_zero]; rfl)

@[simp] theorem nIdx_one (h : ℕ) : nIdx h 1 = coreLetter h 1 :=
  nIdx_eq_wild h 1 (by rw [coreVal_one]; omega) _ (by rw [coreVal_one]; rfl)

@[simp] theorem nIdx_two (h : ℕ) : nIdx h 2 = .sigma := by
  simp only [nIdx, coreVal_two, if_pos]

@[simp] theorem nIdx_three (h : ℕ) : nIdx h 3 = coreLetter h 2 :=
  nIdx_eq_wild h 3 (by rw [coreVal_three]; omega) _ (by rw [coreVal_three]; rfl)

@[simp] theorem nIdx_handleIdxU (h : ℕ) (j : Fin h) :
    nIdx h (handleIdxU j) = handleU j :=
  nIdx_eq_wild h (handleIdxU j) (by rw [handleIdxU_val]; omega) _ (by
    show 3 + 2 * (j : ℕ) = _
    rw [handleIdxU_val, if_neg (by omega)]
    omega)

@[simp] theorem nIdx_handleIdxV (h : ℕ) (j : Fin h) :
    nIdx h (handleIdxV j) = handleV j :=
  nIdx_eq_wild h (handleIdxV j) (by rw [handleIdxV_val]; omega) _ (by
    show 4 + 2 * (j : ℕ) = _
    rw [handleIdxV_val, if_neg (by omega)]
    omega)

/-- **The landed word-level input, in the shape the bridge consumes.**  This is
`GQ2.Dyadic.Words.eval_pro2_nCompact` (`GQ2/Dyadic/Words/N0.lean:378`) read through the
dictionary: the RHS `nWord α (t x₀) (t x₁) t.σ (t x₂) * handleWord …` **is** `nRelWord α` at the
reindexed marking, at every handle count `h` — not only at `h = 0`, where `Words/N0.lean` states
its `_eq_nRelWord` corollary. -/
theorem eval_pro2_nCompact_reindex (α h : ℕ) {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (t : Marking (2 + 2 * h) G) :
    t.eval (pro2 (nCompactW α h)) = (nNatWord α h).ev ((nReindex h).toCore t) := by
  rw [eval_pro2_nCompact α h t]
  show _ = nRelWord α (fun i => t (nIdx h i))
  simp only [nRelWord, nIdx_zero, nIdx_one, nIdx_two, nIdx_three, nIdx_handleIdxU,
    nIdx_handleIdxV, Marking.apply_sigma]

/-- **The pilot core presentation**: `D_N` at rank `4 + 2h`, in alphabet coordinates.

Inputs, all landed: `isProP_DN`, `presentedBy_DN` (`MarkedCore/Certificate.lean:285`),
`dn_relation`, and WN0's `eval_pro2_nCompact`.  **No `NLabHypothesis`** — note in particular that
`presentedBy_DN` and `dn_relation` are used, not `markedRelator_DN`, so not even the `1 ≤ α`
side condition is inherited. -/
noncomputable def nCorePresentation (α h : ℕ) :
    CorePresentation (2 + 2 * h) (nCompactW α h) (DN α h) :=
  CorePresentation.ofPresentedBy (isProP_DN α h) (presentedBy_DN α h) (dn_relation α h)
    (nReindex h) (fun t => eval_pro2_nCompact_reindex α h t)

@[simp] theorem nCorePresentation_mark_sigma (α h : ℕ) :
    (nCorePresentation α h).mark .sigma = dnSigma α h :=
  congrArg (dnGen α h) (Fin.ext (by rw [coreVal_two]; rfl))

@[simp] theorem nCorePresentation_mark_wild (α h : ℕ) (j : Fin (2 + 2 * h + 1)) :
    (nCorePresentation α h).mark (.wild j) = dnGen α h (nWildIdx h j) := rfl

/-- **The pilot bridge**: the maximal pro-2 quotient of the compact-`N` candidate group is the
presented core `D_N`, at every handle count.  The `ℚ₂` shadow of this statement is
`GQ2.maxPro2Bridge`; that one is `n = 1`, `q = 2`, rank 3, and this one is rank `4 + 2h`. -/
noncomputable def nMaxProTwoBridge (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMulEquiv
      ((maxProPQuotient 2 ((GammaR (2 + 2 * h) q (nCompactW α h)) : Type)) : Type)
      ((DN α h) : Type) :=
  CorePresentation.maxProTwoBridge (nCorePresentation α h) hq0 hqe

/-- **The pilot's four `WordCertificate` pro-2 fields.**  Compare `GQ2.Roe.exists_pro2R`: same
shape, no `BLabHypothesis`, and at rank `4 + 2h` rather than 3. -/
theorem n_exists_proTwo (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes (2 + 2 * h) q (nCompactW α h))
    (nuP : ContinuousMonoidHom ((DN α h) : Type) Ztwo)
    (hnuSigma : nuP (dnSigma α h) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 + 2 * h + 1), nuP (dnGen α h (nWildIdx h j)) = 1) :
    ∃ pro2G : ContinuousMonoidHom (((GammaR (2 + 2 * h) q (nCompactW α h))) : Type)
        ((DN α h) : Type),
      Function.Surjective pro2G ∧
      pro2G.toMonoidHom.ker = proPKernel 2 ((GammaR (2 + 2 * h) q (nCompactW α h)) : Type) ∧
      (∀ g, nuTq q (tameOfSpec (2 + 2 * h) q (nCompactW α h) hspec g) = nuP (pro2G g)) ∧
      pro2G (gammaGen (2 + 2 * h) q (nCompactW α h) .tau) = 1 :=
  CorePresentation.exists_proTwo (nCorePresentation α h) hq0 hqe hspec nuP
    (by rw [nCorePresentation_mark_sigma]; exact hnuSigma)
    (fun j => by rw [nCorePresentation_mark_wild]; exact hnuWild j)

/-! ### Stress checks (plan rule 9) -/

/-- **Stress test.**  The bridge's word-level input really is the landed `eval_pro2_nCompact`:
the two sides of the dictionary agree on the nose at every `h`. -/
example (α h : ℕ) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (t : Marking (2 + 2 * h) G) :
    nRelWord α ((nReindex h).toCore t)
      = nWord α (t (coreLetter h 0)) (t (coreLetter h 1)) t.σ (t (coreLetter h 2)) *
        handleWord (fun j => t (handleU j)) (fun j => t (handleV j)) :=
  (eval_pro2_nCompact_reindex α h t).symm.trans (eval_pro2_nCompact α h t)

/-- **Stress test (`h = 0`).**  At no handles the pilot core is `D_N` at rank 4 and the dictionary
reproduces `Words/N0.lean`'s own `coreMark` normalization (`eval_pro2_nCompact_eq_nRelWord`). -/
example (α : ℕ) {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] (t : Marking 2 G) :
    nRelWord α ((nReindex 0).toCore t)
      = nRelWord (h := 0) α (coreMark (t.x 0) (t.x 1) t.σ (t.x 2)) :=
  (eval_pro2_nCompact_reindex α 0 t).symm.trans (eval_pro2_nCompact_eq_nRelWord α t)

/-- **Stress test (`τ` death).**  The pilot bridge carries the class of `τ` to `1 ∈ D_N`. -/
example (α h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    nMaxProTwoBridge α h q hq0 hqe
        (CorePresentation.maxMarking (2 + 2 * h) q (nCompactW α h) .tau) = 1 :=
  (CorePresentation.PhiMax_maxMarking (nCorePresentation α h) hq0 hqe .tau).trans
    (nCorePresentation α h).mark_tau

end PilotN


/-! ### The field-fit check

`WordCertificate` (`GQ2/Dyadic/CertificateMain.lean:450`) takes `P : ProfiniteGrp.{0}`, and its
four pro-2 fields have exactly the types below.  This `example` is the proof that §5's outputs
plug into those slots verbatim — it is the ticket's acceptance test, and it is deliberately
stated at the *abstract* `CorePresentation`, so it certifies the fit for all five branches at
once, not just the pilot. -/
noncomputable example {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp.{0}}
    (CP : CorePresentation n R P) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes n q R) (nuP : ContinuousMonoidHom (P : Type) Ztwo)
    (h1 : nuP (CP.mark .sigma) = ztwoOne) (h2 : ∀ i, nuP (CP.mark (.wild i)) = 1) :
    -- `WordCertificate.pro2`
    (ContinuousMonoidHom ((GammaR n q R) : Type) P)
    -- `WordCertificate.ker_pro2`
    × PLift ((CorePresentation.coreHom CP hq0 hqe).toMonoidHom.ker
        = proPKernel 2 ((GammaR n q R) : Type))
    -- `WordCertificate.hpro2`
    × PLift (Function.Surjective (CorePresentation.coreHom CP hq0 hqe))
    -- `WordCertificate.compat`
    × PLift (∀ g : ((GammaR n q R) : Type),
        nuTq q (tameOfSpec n q R hspec g) = nuP (CorePresentation.coreHom CP hq0 hqe g)) :=
  ⟨CorePresentation.coreHom CP hq0 hqe,
   ⟨CorePresentation.ker_coreHom CP hq0 hqe⟩,
   ⟨CorePresentation.coreHom_surjective CP hq0 hqe⟩,
   ⟨CorePresentation.nu_compat_coreHom CP hq0 hqe hspec nuP h1 h2⟩⟩

end GQ2.Dyadic.Count
