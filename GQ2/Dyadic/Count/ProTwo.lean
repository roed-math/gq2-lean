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

open GQ2 GQ2.Dyadic

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
  /-- **Universal property, uniqueness.**  Continuous homs out of `P` are pinned on `mark`. -/
  hom_ext : ∀ {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
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
    (quotientMk_surjective (relatorSubgroup (gammaRelators n q R)))
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

end Bridge

end CorePresentation

end GQ2.Dyadic.Count
