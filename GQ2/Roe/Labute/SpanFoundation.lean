/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.Levelwise

/-!
# Span-theorem foundation: shift words, grading, descent infra, the free pro-2 group
(GL-campaign ticket GL0)

Text-moved out of `StageLemma.lean` (2026-07-26, statements byte-identical) so that the
GL-campaign files (`GQ2/Roe/Labute/GradedLie/`) can sit **below** `StageLemma.lean` in the
import graph: `StageLemma` imports `GradedLie.SpanAssembly`, which needs the definitions
here.  Design record: `docs/orchestration/span-gradedlie-plan.md`.

Contents (in original `StageLemma.lean` order):
* the shift word shapes `dbarWordR0` / `dbarWordR2` and their smoke lemmas;
* the λ-grading lemma (`GRAD`) section;
* the descent infrastructure (`lambdaImage_induction` and friends);
* the free pro-2 group `freeProTwo`, its marked generators, universal property and
  topological generation (`freeTopGenFinset` made public in the move — the GL fills
  need the `hfg`-hypothesis shape);
* NEW (GL0): the span-target subgroups `SpanTargetR0/R2` — the verbatim right-hand
  sides of the frozen `span_free_r0/r2` statements, kept as plain defs so the
  StageLemma fills are definitional.
-/

namespace GQ2.Roe.Labute

/-! ## The shift word shapes -/

/-- The **`r₀`-side defect-shift word** `d̄(w) = w₁²·[w₁,a]·[w₂,y]·[w₃,s]` at the triple
`(a, s, y)` (spike §2.2; repo `commP`).  A word shape in any group; its homomorphism
property on `Z`-layer classes is part of the L4a calculus, not of the definition. -/
def dbarWordR0 {G : Type*} [Group G] (a s y : G) (w : Fin 3 → G) : G :=
  w 0 ^ 2 * commP (w 0) a * commP (w 1) y * commP (w 2) s

/-- The **`r₂`-side defect-shift word** `d̄(u,v,w) = w²·[w,y]·[u,x]·[v,s]` at the triple
`(s, x, y)` (spike §2.2 — note the r₂-tails/cross-terms pair `(u,x), (v,s)`, *not* the
draft's `(x, y)` pairing). -/
def dbarWordR2 {G : Type*} [Group G] (s x y : G) (w : Fin 3 → G) : G :=
  w 2 ^ 2 * commP (w 2) y * commP (w 0) x * commP (w 1) s

/-- Naturality of the `r₀`-shift word (smoke). -/
theorem map_dbarWordR0 {F G H : Type*} [Group G] [Group H] [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (a s y : G) (w : Fin 3 → G) :
    φ (dbarWordR0 a s y w) = dbarWordR0 (φ a) (φ s) (φ y) (fun i => φ (w i)) := by
  simp only [dbarWordR0, commP, map_mul, map_inv, map_pow]

/-- Naturality of the `r₂`-shift word (smoke). -/
theorem map_dbarWordR2 {F G H : Type*} [Group G] [Group H] [FunLike F G H]
    [MonoidHomClass F G H] (φ : F) (s x y : G) (w : Fin 3 → G) :
    φ (dbarWordR2 s x y w) = dbarWordR2 (φ s) (φ x) (φ y) (fun i => φ (w i)) := by
  simp only [dbarWordR2, commP, map_mul, map_inv, map_pow]

/-- Abelian collapse (smoke): only the square survives — the cross terms are honest
commutators. -/
theorem dbarWordR0_comm {G : Type*} [CommGroup G] (a s y : G) (w : Fin 3 → G) :
    dbarWordR0 a s y w = w 0 ^ 2 := by
  rw [dbarWordR0, commP_eq_one, commP_eq_one, commP_eq_one, mul_one, mul_one, mul_one]

/-- Trivial modification, trivial shift (smoke). -/
theorem dbarWordR0_one {G : Type*} [Group G] (a s y : G) :
    dbarWordR0 a s y (fun _ => 1) = 1 := by
  simp [dbarWordR0, commP]

/-- Trivial modification, trivial shift, `r₂` side (smoke). -/
theorem dbarWordR2_one {G : Type*} [Group G] (s x y : G) :
    dbarWordR2 s x y (fun _ => 1) = 1 := by
  simp [dbarWordR2, commP]

/-! ### The λ-grading lemma (L4b fill helper; Hall–Witt calculus)

`⁅λₐ, λᵦ⁆ ≤ λ_{a+b}` — the graded-bracket bound underlying every depth estimate of the
span reduction (spike §2.5(a)'s identity list).  Proved by induction on `b` via the three
subgroups lemma (transported from mathlib's `⊥`-form through the quotient by `λ_{a+b}`)
and the closed-subgroup trick for the topological closure step. -/

section Grading

variable {G : Type*} [Group G]

open scoped commutatorElement in
/-- The three subgroups lemma, `≤ N`-form: transport of
`Subgroup.commutator_commutator_eq_bot_of_rotate` through `G ⧸ N`. -/
theorem commutator_commutator_le_of_rotate {A B C N : Subgroup G} [N.Normal]
    (h1 : ⁅⁅B, C⁆, A⁆ ≤ N) (h2 : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  have key : ∀ X Y Z : Subgroup G, ⁅⁅X, Y⁆, Z⁆ ≤ N ↔
      ⁅⁅X.map (QuotientGroup.mk' N), Y.map (QuotientGroup.mk' N)⁆,
        Z.map (QuotientGroup.mk' N)⁆ = ⊥ := by
    intro X Y Z
    rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff,
      QuotientGroup.ker_mk']
  rw [key] at h1 h2 ⊢
  exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2

variable (G) [TopologicalSpace G] [IsTopologicalGroup G]

open scoped commutatorElement in
/-- One-step bound, subgroup form: `⁅λₐ, ⊤⁆ ≤ λ_{a+1}`. -/
theorem commutator_twoCentralSeries_top_le (a : ℕ) :
    ⁅twoCentralSeries G a, (⊤ : Subgroup G)⁆ ≤ twoCentralSeries G (a + 1) := by
  rw [Subgroup.commutator_le]
  intro v hv g _
  exact commutator_mem_twoCentralSeries_succ G hv g

open scoped commutatorElement in
/-- **The λ-grading lemma** (`GRAD`): `⁅λₐ, λᵦ⁆ ≤ λ_{a+b}`. -/
theorem commutator_twoCentralSeries_le :
    ∀ (b a : ℕ), ⁅twoCentralSeries G a, twoCentralSeries G b⁆ ≤ twoCentralSeries G (a + b)
  | 0, a => by
    simpa using (commutator_twoCentralSeries_top_le G a).trans
      (twoCentralSeries_antitone G (Nat.le_succ a))
  | 1, a => by simpa using commutator_twoCentralSeries_top_le G a
  | (b + 2), a => by
    -- Notation: `N = λ_{a+b+2}` is the target, `H = λ_{b+1}` the penultimate layer.
    set N := twoCentralSeries G (a + (b + 2)) with hN
    set H := twoCentralSeries G (b + 1) with hH
    haveI hNn : N.Normal := twoCentralSeries_normal G _
    rw [Subgroup.commutator_le]
    intro v hv h hh
    -- The membership set of `v`-brackets is a closed subgroup; unfold `λ_{b+2}` into it.
    set S : Subgroup G :=
      { carrier := {g | ⁅v, g⁆ ∈ N}
        one_mem' := by simp
        mul_mem' := by
          intro g₁ g₂ hg₁ hg₂
          show ⁅v, g₁ * g₂⁆ ∈ N
          have hexp : ⁅v, g₁ * g₂⁆ = ⁅v, g₁⁆ * (g₁ * ⁅v, g₂⁆ * g₁⁻¹) := by group
          rw [hexp]
          exact N.mul_mem hg₁ (Subgroup.Normal.conj_mem hNn _ hg₂ g₁)
        inv_mem' := by
          intro g hg
          show ⁅v, g⁻¹⁆ ∈ N
          have hexp : ⁅v, g⁻¹⁆ = g⁻¹ * ⁅v, g⁆⁻¹ * g := by group
          rw [hexp]
          exact Subgroup.Normal.conj_mem' hNn _ (N.inv_mem hg) g } with hS
    have hSclosed : IsClosed (S : Set G) := by
      have : (S : Set G) = (fun g => ⁅v, g⁆) ⁻¹' (N : Set G) := rfl
      rw [this]
      refine (isClosed_twoCentralSeries G _).preimage ?_
      simp only [commutatorElement_def]
      fun_prop
    -- Atom cases over `λ_{b+1}`.
    have hsq : ∀ u ∈ H, u ^ 2 ∈ S := by
      intro u hu
      have hvu : ⁅v, u⁆ ∈ twoCentralSeries G (a + (b + 1)) :=
        commutator_twoCentralSeries_le (b + 1) a (Subgroup.commutator_mem_commutator hv hu)
      have hexp : ⁅v, u ^ 2⁆ = ⁅v, u⁆ ^ 2 * ⁅⁅v, u⁆⁻¹, u⁆ := by
        simp [commutatorElement_def, pow_two, mul_assoc]
      have h1 : ⁅v, u⁆ ^ 2 ∈ N := by
        have := sq_mem_twoCentralSeries_succ G hvu
        rwa [show a + (b + 1) + 1 = a + (b + 2) from rfl] at this
      have h2 : ⁅⁅v, u⁆⁻¹, u⁆ ∈ N := by
        have := commutator_mem_twoCentralSeries_succ G
          ((twoCentralSeries G (a + (b + 1))).inv_mem hvu) u
        rwa [show a + (b + 1) + 1 = a + (b + 2) from rfl] at this
      show ⁅v, u ^ 2⁆ ∈ N
      rw [hexp]
      exact N.mul_mem h1 h2
    have hbr : ∀ u ∈ H, ∀ g : G, ⁅u, g⁆ ∈ S := by
      intro u hu g
      have hrot : ⁅⁅H, (⊤ : Subgroup G)⁆, twoCentralSeries G a⁆ ≤ N := by
        refine commutator_commutator_le_of_rotate ?_ ?_
        · -- `⁅⁅⊤, λₐ⁆, λ_{b+1}⁆ ≤ N` via the induction hypothesis at `(a+1, b+1)`.
          refine (Subgroup.commutator_mono
            ((Subgroup.commutator_comm _ _).le.trans
              (commutator_twoCentralSeries_top_le G a)) le_rfl).trans ?_
          have := commutator_twoCentralSeries_le (b + 1) (a + 1)
          rwa [show a + 1 + (b + 1) = a + (b + 2) from by omega] at this
        · -- `⁅⁅λₐ, λ_{b+1}⁆, ⊤⁆ ≤ N` via the induction hypothesis at `(a, b+1)` + one step.
          refine (Subgroup.commutator_mono
            (commutator_twoCentralSeries_le (b + 1) a) le_rfl).trans ?_
          exact (commutator_twoCentralSeries_top_le G _)
      show ⁅v, ⁅u, g⁆⁆ ∈ N
      refine hrot ?_
      have hw : ⁅u, g⁆ ∈ ⁅H, (⊤ : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator hu (Subgroup.mem_top g)
      have hflip : ⁅v, ⁅u, g⁆⁆ = ⁅⁅u, g⁆, v⁆⁻¹ := by group
      rw [hflip]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hw hv)
    -- Assemble: `S` contains the generating join and is closed, hence contains `λ_{b+2}`.
    have hle : twoCentralSeries G (b + 2) ≤ S := by
      rw [twoCentralSeries_succ G (Nat.le_add_left 1 b), twoCentralSucc]
      refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hSclosed
      · rw [Subgroup.closure_le]
        rintro _ ⟨u, hu, rfl⟩
        exact hsq u hu
      · rw [Subgroup.commutator_le]
        intro u hu g _
        exact hbr u hu g
    exact hle hh

open scoped commutatorElement in
/-- Element form of the grading lemma. -/
theorem commutator_mem_twoCentralSeries_add {a b : ℕ} {v h : G}
    (hv : v ∈ twoCentralSeries G a) (hh : h ∈ twoCentralSeries G b) :
    ⁅v, h⁆ ∈ twoCentralSeries G (a + b) :=
  commutator_twoCentralSeries_le G b a (Subgroup.commutator_mem_commutator hv hh)

end Grading

/-! ### Descent infrastructure (L4b fill helpers; not part of the frozen interface)

For a topologically f.g. pro-2 `G` the level quotients are finite *discrete* groups, the
λ-series of `Qₘ` is the image of the λ-series of `G` (`map_twoCentralSeries_eq` along
`levelMk`), and in particular `λₘ(Qₘ) = ⊥`.  These are the transport facts through which
the free span statement descends to the towers. -/

section DescentInfra

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The level quotients of a topologically f.g. pro-2 group are discrete (`λₘ` is open). -/
theorem discreteTopology_levelQuot
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) : DiscreteTopology (levelQuot G m) := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro q
  obtain ⟨g, rfl⟩ := levelMk_surjective G m q
  have hset : (QuotientGroup.mk : G → levelQuot G m) ⁻¹' {levelMk G m g} =
      (fun x : G => x⁻¹ * g) ⁻¹' (twoCentralSeries G m : Set G) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    exact (QuotientGroup.eq (s := twoCentralSeries G m)).trans Iff.rfl
  have hopen : IsOpen ((QuotientGroup.mk : G → levelQuot G m) ⁻¹' {levelMk G m g}) := by
    rw [hset]
    exact (isOpen_twoCentralSeries G hfg hpro m).preimage (by fun_prop)
  exact ((QuotientGroup.isQuotientMap_mk (twoCentralSeries G m)).isOpen_preimage).mp hopen

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The canonical projection `levelMk` is continuous. -/
theorem continuous_levelMk (m : ℕ) : Continuous (levelMk G m) :=
  QuotientGroup.continuous_mk

/-- **λ-transport along `levelMk`**: the two-index image `λⱼλₘ/λₘ` *is* the `j`-th layer of
the λ-series of the level quotient `Qₘ` (verbal functoriality for the continuous epi
`levelMk`, using discreteness of the target). -/
theorem lambdaImage_eq_twoCentralSeries_levelQuot
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (j m : ℕ) :
    lambdaImage G j m = twoCentralSeries (levelQuot G m) j := by
  haveI := discreteTopology_levelQuot G hfg hpro m
  exact map_twoCentralSeries_eq (levelMk G m) (continuous_levelMk G m)
    (levelMk_surjective G m) j

/-- The λ-series of the level-`m` quotient vanishes at level `m`. -/
theorem twoCentralSeries_levelQuot_self
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) : twoCentralSeries (levelQuot G m) m = ⊥ := by
  rw [← lambdaImage_eq_twoCentralSeries_levelQuot G hfg hpro m m, lambdaImage,
    Subgroup.map_eq_bot_iff, levelMk, QuotientGroup.ker_mk']

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Mapping into a *discrete* group erases topological closures: the image of `cl K` is
the image of `K` (the preimage of the image subgroup is clopen). -/
theorem map_topologicalClosure_eq_of_discrete {H : Type*} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] (K : Subgroup G) (f : G →* H) (hf : Continuous f) :
    K.topologicalClosure.map f = K.map f := by
  refine le_antisymm ?_ (Subgroup.map_mono K.le_topologicalClosure)
  have hle : K.topologicalClosure ≤ Subgroup.comap f (K.map f) := by
    refine Subgroup.topologicalClosure_minimal K (Subgroup.le_comap_map f K) ?_
    exact (isClosed_discrete ((K.map f : Subgroup H) : Set H)).preimage hf
  exact (Subgroup.map_mono hle).trans (Subgroup.map_comap_le f (K.map f))

omit [T2Space G] [TotallyDisconnectedSpace G] in
open scoped commutatorElement in
/-- **Atomization of the layer images** (L4b workhorse): for topologically f.g. pro-2 `G`,
a property closed under the group operations that holds on the residues of squares `v²`
and brackets `⁅v, g⁆` (`v ∈ λⱼ`, `g ∈ G`) holds on all of `λ_{j+1}λₘ/λₘ ≤ Qₘ`.  This is
the mod-`λₘ` shadow of the verbal generation of `λ_{j+1}`, with the topological closure
erased by discreteness of the finite quotient. -/
theorem lambdaImage_induction [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {j m : ℕ} (hj : 1 ≤ j) {p : levelQuot G m → Prop}
    (hsq : ∀ v ∈ twoCentralSeries G j, p (levelMk G m (v ^ 2)))
    (hbr : ∀ v ∈ twoCentralSeries G j, ∀ g : G, p (levelMk G m ⁅v, g⁆))
    (hone : p 1) (hmul : ∀ x y, p x → p y → p (x * y)) (hinv : ∀ x, p x → p x⁻¹)
    {q : levelQuot G m} (hq : q ∈ lambdaImage G (j + 1) m) : p q := by
  haveI := discreteTopology_levelQuot G hfg hpro m
  have hsucc : twoCentralSeries G (j + 1) =
      (Subgroup.closure (((fun v : G => v ^ 2) '' (twoCentralSeries G j : Set G)) ∪
        {g | ∃ g₁ ∈ twoCentralSeries G j, ∃ g₂ ∈ (⊤ : Subgroup G), ⁅g₁, g₂⁆ = g})
      ).topologicalClosure := by
    rw [twoCentralSeries_succ G hj, twoCentralSucc, Subgroup.closure_union,
      ← Subgroup.commutator_def]
  rw [lambdaImage, hsucc,
    map_topologicalClosure_eq_of_discrete G _ _ (continuous_levelMk G m),
    MonoidHom.map_closure] at hq
  refine Subgroup.closure_induction ?_ hone (fun x y _ _ => hmul x y) (fun x _ => hinv x) hq
  rintro _ ⟨x, hx | hx, rfl⟩
  · obtain ⟨v, hv, rfl⟩ := hx
    exact hsq v hv
  · obtain ⟨v, hv, g, -, rfl⟩ := hx
    exact hbr v hv g

end DescentInfra

/-! ## The free pro-2 group on three generators -/

/-- The free pro-2 group `F₃` on three generators — the *only* group in which the span
theorem is proved (spike §2.3: "The Lean statement only ever needs the free version");
the towers receive it by descent. -/
noncomputable def freeProTwo : ProfiniteGrp :=
  maxProPQuotient 2 (FreeProfiniteGroup (Fin 3))

/-- The marked generators of `F₃`. -/
noncomputable def freeGen (i : Fin 3) : (freeProTwo : Type) :=
  maxProPMk 2 (FreeProfiniteGroup (Fin 3)) (FreeProfiniteGroup.of i)

section FreeLift

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `F₃`** (L4b helper): a bare triple in a pro-2 group `H`
classifies a continuous hom `F₃ → H` — `drLiftHom`/`d0LiftHom` without the relator step. -/
noncomputable def freeProTwoLift (hH : IsProP 2 H) (m : Fin 3 → H) :
    ContinuousMonoidHom (freeProTwo : Type) H :=
  (maxProPHomEquiv hH).symm
    ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom

@[simp] theorem freeProTwoLift_freeGen (hH : IsProP 2 H) (m : Fin 3 → H) (i : Fin 3) :
    freeProTwoLift hH m (freeGen i) = m i := by
  show ((maxProPHomEquiv hH).symm _)
    (maxProPMk 2 (FreeProfiniteGroup (Fin 3)) (FreeProfiniteGroup.of i)) = m i
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact FreeProfiniteGroup.homEquiv_symm_of _ _ _

end FreeLift

/-- **`F₃` is topologically generated by its marked generators** (density of the abstract
free group in its profinite completion — `ProfiniteGrp.ProfiniteCompletion.denseRange` — pushed through
the surjective pro-2 projection; the `AdmissibleLimit.lean` generation pattern). -/
theorem topGen_freeProTwo :
    (Subgroup.closure (Set.range freeGen)).topologicalClosure = ⊤ := by
  have hdense : DenseRange (⇑(maxProPMk 2 (FreeProfiniteGroup (Fin 3))) ∘
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3)))) :=
    DenseRange.comp (Function.Surjective.denseRange (quotientMk_surjective _))
      (ProfiniteGrp.ProfiniteCompletion.denseRange _)
      (maxProPMk 2 (FreeProfiniteGroup (Fin 3))).continuous_toFun
  -- every word-image lies in the subgroup generated by the marked generators
  have hmem : ∀ w : FreeGroup (Fin 3),
      maxProPMk 2 (FreeProfiniteGroup (Fin 3))
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3))) w)
        ∈ Subgroup.closure (Set.range freeGen) := by
    intro w
    induction w using FreeGroup.induction_on with
    | C1 =>
      show (1 : (freeProTwo : Type)) ∈ _
      exact one_mem _
    | of x => exact Subgroup.subset_closure ⟨x, rfl⟩
    | inv_of x hx =>
      show (maxProPMk 2 (FreeProfiniteGroup (Fin 3))
        (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3)))
          (FreeGroup.of x)))⁻¹ ∈ _
      exact Subgroup.inv_mem _ hx
    | mul x y hx hy =>
      show maxProPMk 2 (FreeProfiniteGroup (Fin 3))
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3))) x) *
        maxProPMk 2 (FreeProfiniteGroup (Fin 3))
          (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 3))) y) ∈ _
      exact Subgroup.mul_mem _ hx hy
  refine SetLike.ext' ?_
  rw [Subgroup.topologicalClosure_coe, Subgroup.coe_top]
  refine Dense.closure_eq (Dense.mono ?_ hdense)
  rintro _ ⟨w, rfl⟩
  exact hmem w

/-- `Finset` form of `topGen_freeProTwo` (the `hfg`-hypothesis shape of the tower API;
made public in the GL0 move — the GL fills need it for the instance pack). -/
theorem freeTopGenFinset :
    ∃ s : Finset (freeProTwo : Type),
      (Subgroup.closure (s : Set (freeProTwo : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{freeGen 0, freeGen 1, freeGen 2}, ?_⟩
  have h : (({freeGen 0, freeGen 1, freeGen 2} : Finset (freeProTwo : Type)) :
      Set (freeProTwo : Type)) = Set.range freeGen := by
    ext x
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, Set.mem_range]
    constructor
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
    · rintro ⟨i, rfl⟩
      fin_cases i <;> tauto
  rw [h]
  exact topGen_freeProTwo

/-! ## The span-target subgroups (GL0)

The verbatim right-hand sides of the frozen `span_free_r0/r2` statements, as plain
(`rfl`-transparent) defs: `span_free_r0` in `StageLemma.lean` is filled by
`span_free_r0_proof k hk : zLayer … k ≤ SpanTargetR0 k` definitionally.  Do NOT
restate or unfold-normalize these — the expressions must stay literally identical to
the frozen statement bodies. -/

/-- The `r₀` span target: d̄-image over `λ_{k-1}`-modifications at the marked generators,
together with the `(S, Y)`-tails (generators 1, 2). -/
noncomputable def SpanTargetR0 (k : ℕ) : Subgroup (levelQuot (freeProTwo : Type) (k + 1)) :=
  Subgroup.closure
    ((fun w : Fin 3 → levelQuot (freeProTwo : Type) (k + 1) =>
        dbarWordR0 (levelMk (freeProTwo : Type) (k + 1) (freeGen 0))
          (levelMk (freeProTwo : Type) (k + 1) (freeGen 1))
          (levelMk (freeProTwo : Type) (k + 1) (freeGen 2)) w) ''
      {w | ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (k - 1) (k + 1)} ∪
    {levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1),
      levelMk (freeProTwo : Type) (k + 1) (freeGen 2) ^ 2 ^ (k - 1)})

/-- The `r₂` span target: tails at the `(s, x)`-slots = generators 0, 1 (the
relator-adapted pair). -/
noncomputable def SpanTargetR2 (k : ℕ) : Subgroup (levelQuot (freeProTwo : Type) (k + 1)) :=
  Subgroup.closure
    ((fun w : Fin 3 → levelQuot (freeProTwo : Type) (k + 1) =>
        dbarWordR2 (levelMk (freeProTwo : Type) (k + 1) (freeGen 0))
          (levelMk (freeProTwo : Type) (k + 1) (freeGen 1))
          (levelMk (freeProTwo : Type) (k + 1) (freeGen 2)) w) ''
      {w | ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (k - 1) (k + 1)} ∪
    {levelMk (freeProTwo : Type) (k + 1) (freeGen 0) ^ 2 ^ (k - 1),
      levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1)})

end GQ2.Roe.Labute
