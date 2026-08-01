/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Compare
import GQ2.Dyadic.AdmissibleR

/-!
# `Γ_R` is an admissibly marked presentation (dyadic campaign, ticket CB-MP)

CB-1 proved the count lane's comparison isomorphism `z1Equiv` degree-generically over an abstract
carrier, against a hypothesis class `IsMarkedPresentation` whose clause (iii) reads *every*
relator-killing marking of a finite discrete group extends over `Γ`.  It left the instance for
`GammaR n q R` unbuilt.

**That instance does not exist, and cannot: the plain clause (iii) is false at `Γ_R`.**  GR1
redefined `GammaR` as the admissible limit `F ⧸ N_R`, the pro-`2` clause on the wild part being
part of the definition (`GQ2/Dyadic/AdmissibleR.lean` §3).  The plain clause is *equivalent* to
being the bare presentation `GammaBare`, and CB-W's `ℤ/3` markings (`Count/Wild.lean` §2–§4) kill
both relators while sending a wild letter to an element of order `3`; they extend over
`GammaBare` (`Count.testHom`) and provably not over `Γ_R` — §5 below re-derives the obstruction
self-containedly.

So this file builds the **restricted** instance, of `Count.IsAdmissibleMarkedPresentation`, whose
clause (iii) asks only for markings satisfying `Count.IsWildTwo` — the normal closure of the
images of the wild letters is a `2`-group.  That property is CB-1's with (iii) weakened, and
`Count.IsMarkedPresentation.toAdmissible` records that the plain class implies it.

## What this file lands

* **§1** `wildLetters n = {x₀, …, x_n} ⊆ Generator n`, the distinguished subset `J` that
  instantiates the restricted class, and its two image lemmas (one of which identifies
  `AdmissibleR.wildFree n` as its image upstairs).
* **§2** `freeToProf`, the canonical `FreeGroup X →* F(X)`, and `comp_freeToProf` — the *word*
  side of CB-1's seam: a continuous hom out of the free profinite group restricts along it to the
  `FreeGroup.lift` of its marking.
* **§3** `ResolvesGammaRelators`, the seam itself, as an explicitly named hypothesis: the
  word-lane family `w : κ → FreeGroup (Generator n)` and the profinite relator set
  `gammaRelators n q R` cut out the same closed normal subgroup of `F`.  `of_range_eq` is the
  sufficient condition a branch actually checks.  ⚠ This is **not** discharged here; see
  "The seam" below.
* **§4** the instance, `isAdmissibleMarkedPresentation_gammaR`, built on GR1's machine:
  `gammaLift` for the lift, with `hrel` from the seam and `hcore` from `IsWildTwo` transported
  through `Subgroup.map_normalClosure_le`.
* **§5** the discharge of `z1Equiv`'s new side condition `hwild2` at `Γ_R`:
  `isWildTwo_gammaGen_of_surjective`, from GR1's `isPGroup_two_wildNormalClosure`.  Surjectivity
  of `ρ` — already a hypothesis of `tcocycle_cardN`/`hZcardN` — is exactly what is needed.
* **§6** the sanity check that the restriction is **not vacuous**: `not_isWildTwo_zmodThree`, no
  marking into `ℤ/3` with a surviving wild letter is admissible.  CB-W's `testMarking n c d` is
  of that shape for the exponents `exists_test_exponents` produces, so the restricted clause
  excludes precisely the counterexamples, and nothing else.
* **§7** the discharges of `z1Equiv`'s other new side condition `hA₂` at the two recursion
  modules: `D.T` and `DD.Vmod` are `2`-torsion, from `RadicalCoverData.helem`.

## The seam (what §3 does *not* prove)

The word lane's relators live in `FreeGroup (Generator n)`; the presentation's live in
`FreeProfiniteGroup (Generator n)`.  The two are related by `freeToProf`, but the branch families
are `heisToFree`-**resolved**: profinite `ω₂`-exponents are replaced by an integer representative
`e` (`nCompactFam α h q e = ![heisToFree … (tameRelW …), heisToFree … (nCompactW α h)]`).  The
resolved word and `(freeMarking n).eval R` are therefore *different elements of `F`* in general —
`PWord.eval` evaluates `ω₂` intrinsically, and no integer represents it there.  They agree at any
particular target where the resolver is correct, which is what `Word/Eval.lean`'s `ResolvedAt` /
`eval_eq_evalZ` and `Word/Stokes.lean`'s `evalZ_eq_lift_heisToFree` express.

`ResolvesGammaRelators` is that agreement, promoted to a hypothesis at the level of closed normal
subgroups.  It is the honest form of the seam CB-1 flagged, and discharging it per branch is the
count lane's remaining word-side obligation — not something `Γ_R`'s universal property can
supply.

## Axiom posture

`sorry`-free, **no new axiom**; every headline `#print axioms` is the standard three.  The two
`decide`s in §6 are kernel `decide`s in the three-element group.
-/

namespace GQ2.Dyadic

namespace Count

open GQ2 GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction GQ2.SectionEight.AffineTLift
open GQ2.SectionEight.RadicalEdgeGammaA

/-! ## §1 The distinguished letters

`IsAdmissibleMarkedPresentation` is parametrized by a set `J ⊆ ι` of letters whose normal closure
the admissibility clause constrains.  For the campaign's alphabet that set is the wild block. -/

section WildLetters

variable {n : ℕ}

/-- The **wild letters** `{x₀, …, x_n}` of `Generator n`, as a subset — the value of the
`IsAdmissibleMarkedPresentation` parameter `J` for every branch of the campaign. -/
def wildLetters (n : ℕ) : Set (Generator n) := Set.range (Generator.wild (n := n))

theorem wild_mem_wildLetters (i : Fin (n + 1)) : Generator.wild i ∈ wildLetters n := ⟨i, rfl⟩

/-- The image of the wild block under any marking is the range of its wild values.  This is the
shape every `IsPGroup` statement about `J` is really about. -/
theorem image_wildLetters {G : Type*} (f : Generator n → G) :
    f '' wildLetters n = Set.range fun i : Fin (n + 1) => f (Generator.wild i) := by
  rw [wildLetters, ← Set.range_comp]
  rfl

/-- `AdmissibleR.wildFree n` — the wild letters upstairs in `F`, which is what
`IsAdmissibleU`'s pro-`2` clause is stated about — is the image of `wildLetters n` under the
tautological marking. -/
theorem image_wildLetters_of :
    (FreeProfiniteGroup.of (X := Generator n)) '' wildLetters n = wildFree n :=
  image_wildLetters _

end WildLetters

/-! ## §2 The free group inside the free profinite group

CB-1's seam has a trivial half and a hard half.  The trivial half is this: there *is* a canonical
`FreeGroup X →* F(X)`, and a continuous hom out of `F(X)` restricts along it to the `FreeGroup`
lift of its own marking.  (The hard half is §3.) -/

section FreeToProf

/-- The canonical map from the discrete free group into its profinite completion.  The repo has
been inlining this as a `set` (seven copies: `FinitelyGenerated.lean:69`, `Prop32.lean:70`,
`TameQuotientK.lean:303`, …); it is named once here because §3 quantifies over its values. -/
noncomputable def freeToProf (X : Type) : FreeGroup X →* ((FreeProfiniteGroup X) : Type) :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup X))).hom

@[simp] theorem freeToProf_of (X : Type) (x : X) :
    freeToProf X (FreeGroup.of x) = FreeProfiniteGroup.of x := rfl

/-- **Restriction along `freeToProf` is `FreeGroup.lift` of the marking.**  Both sides are
homomorphisms out of `FreeGroup X` agreeing on the letters. -/
theorem comp_freeToProf {X : Type} {Q : Type*} [Group Q]
    (φ : ((FreeProfiniteGroup X) : Type) →* Q) (v : FreeGroup X) :
    φ (freeToProf X v) = FreeGroup.lift (fun x => φ (FreeProfiniteGroup.of x)) v := by
  have h : φ.comp (freeToProf X) = FreeGroup.lift fun x => φ (FreeProfiniteGroup.of x) := by
    apply FreeGroup.ext_hom
    intro x
    rw [MonoidHom.comp_apply, FreeGroup.lift_apply_of]
    rfl
  exact congrArg (fun ψ : FreeGroup X →* Q => ψ v) h

end FreeToProf

/-! ## §3 The seam, named

The word lane hands the presentation a family `w : κ → FreeGroup (Generator n)`; `Γ_R` is
defined by a set `gammaRelators n q R ⊆ F`.  Everything below needs exactly two implications
between them, and both are stated as fields rather than proved, because the branch families are
`ω₂`-resolved and the two objects are genuinely different elements of `F` (module docstring). -/

section Resolves

variable {n q : ℕ} {R : PWord (Generator n)} {κ : Type*}

/-- **The word-lane family and the profinite relators cut out the same closed normal subgroup.**

`fam_mem` says the family dies wherever the relators do (this gives the `rel` clause of the
presentation); `rel_mem` says the relators die wherever the family does (this gives the `extend`
clause).  Together they are "same normal closure", split into the two usable halves. -/
structure ResolvesGammaRelators (n q : ℕ) (R : PWord (Generator n))
    (w : κ → FreeGroup (Generator n)) : Prop where
  /-- Each word-lane relator lies in the closed normal closure of the profinite relator set. -/
  fam_mem : ∀ k, freeToProf (Generator n) (w k) ∈ relatorSubgroup (gammaRelators n q R)
  /-- Each profinite relator lies in the closed normal closure of the word-lane family. -/
  rel_mem : ∀ r ∈ gammaRelators n q R, r ∈ (Subgroup.normalClosure
    (Set.range fun k => freeToProf (Generator n) (w k))).topologicalClosure

/-- **The sufficient condition a branch checks**: the family's profinite images are *exactly* the
two relators.  For a two-relator family `![w₀, w₁]` this is the pair of equations
`freeToProf w₀ = tameRelatorGen n q` and `freeToProf w₁ = (freeMarking n).eval R`. -/
theorem ResolvesGammaRelators.of_range_eq {w : κ → FreeGroup (Generator n)}
    (h : (Set.range fun k => freeToProf (Generator n) (w k)) = gammaRelators n q R) :
    ResolvesGammaRelators n q R w where
  fam_mem k :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (h ▸ Set.mem_range_self k))
  rel_mem _ hr :=
    Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (h ▸ hr))

/-- **The two-relator form**, which is the shape every frozen branch has: `Γ_R` has two relators,
so a `Fin 2`-indexed word-lane family resolves them as soon as its two profinite images are the
tame relator and `R`.  This also witnesses that `ResolvesGammaRelators` is *satisfiable* — take
any `R` whose `PWord` carries no genuine profinite exponent, so that `(freeMarking n).eval R` is
literally a `freeToProf` image. -/
theorem ResolvesGammaRelators.of_two {v : Fin 2 → FreeGroup (Generator n)}
    (h0 : freeToProf (Generator n) (v 0) = tameRelatorGen n q)
    (h1 : freeToProf (Generator n) (v 1) = (freeMarking n).eval R) :
    ResolvesGammaRelators n q R v :=
  ResolvesGammaRelators.of_range_eq <| by
    rw [TopGen.range_fin_two, h0, h1]
    rfl

end Resolves

/-! ## §4 The instance

The three clauses, on GR1's machine.  `gen_top` is `TopGen.map` applied to `gammaMk`; `rel` is
§2's restriction lemma plus `relatorSubgroup_le_NR`; `extend` is `gammaLift`, whose two arguments
are the seam (`hrel`) and the admissibility hypothesis of the restricted clause (`hcore`).

⚠ `hcore` is *why* the clause had to be restricted: it is `gammaLift`'s third argument, GR1 flags
it in the `AdmissibleR` interface note, and there is nothing in a bare relator-killing marking
that supplies it. -/

section Instance

variable {n q : ℕ} {R : PWord (Generator n)} {κ : Type*}

/-- The marked letters of `Γ_R` topologically generate it: the free profinite group is
topologically generated by its letters, and `gammaMk` is a continuous surjection. -/
theorem gammaGen_topGen (n q : ℕ) (R : PWord (Generator n)) :
    (Subgroup.closure (Set.range (gammaGen n q R))).topologicalClosure = ⊤ := by
  have h := TopGen.map (gammaMk n q R).toMonoidHom (gammaMk n q R).continuous_toFun
    (gammaMk_surjective n q R) (TopGen.freeProfiniteGroup (Generator n))
  rwa [← Set.range_comp] at h

/-- A word-lane relator dies in `Γ_R` as soon as it lies in the relator subgroup. -/
theorem lift_gammaGen_eq_one {v : FreeGroup (Generator n)}
    (hv : freeToProf (Generator n) v ∈ relatorSubgroup (gammaRelators n q R)) :
    FreeGroup.lift (gammaGen n q R) v = 1 := by
  have h : FreeGroup.lift (gammaGen n q R) v = gammaMk n q R (freeToProf (Generator n) v) :=
    (comp_freeToProf (gammaMk n q R).toMonoidHom v).symm
  rw [h]
  exact gammaMk_eq_one_iff.mpr (relatorSubgroup_le_NR hv)

/-- **`Γ_R` is an admissibly marked presentation.**

The restricted class, at the corrected `GammaR`: `Γ_R` is presented by its own generators modulo
any word-lane family that resolves the relator set, with the wild block as the distinguished
letters.  This is the instance CB-1's `z1Equiv` consumes.

⚠ The **plain** class `IsMarkedPresentation` is *not* available here, and the failure is not an
artefact of this proof: `Count.not_isWildTwo_zmodThree` (§6) exhibits, for every `n ≥ 1`, the
markings clause (iii) would have to extend and cannot. -/
theorem isAdmissibleMarkedPresentation_gammaR (n q : ℕ) (R : PWord (Generator n))
    {w : κ → FreeGroup (Generator n)} (hres : ResolvesGammaRelators n q R w) :
    IsAdmissibleMarkedPresentation ((GammaR n q R) : Type) (gammaGen n q R) w
      (wildLetters n) where
  gen_top := gammaGen_topGen n q R
  rel k := lift_gammaGen_eq_one (hres.fam_mem k)
  extend := by
    intro Q _ _ _ _ f hf hw2
    -- the classifying map of `f` out of the free profinite group, at the plain carrier instances
    -- (the type ascription is load-bearing, exactly as for `Count.testBaseHom`)
    let φ : ContinuousMonoidHom ((FreeProfiniteGroup (Generator n)) : Type) Q :=
      ((FreeProfiniteGroup.homEquiv (Generator n) (ProfiniteGrp.of Q)).symm f).hom
    have hφ_of : ∀ g : Generator n, φ.toMonoidHom (FreeProfiniteGroup.of g) = f g := fun g =>
      FreeProfiniteGroup.homEquiv_symm_of _ _ _
    have hφfun : (fun g => φ.toMonoidHom (FreeProfiniteGroup.of g)) = f := funext hφ_of
    -- the relators die: the family does, and the seam moves that to the relators
    have hfam : ∀ k, φ.toMonoidHom (freeToProf (Generator n) (w k)) = 1 := by
      intro k
      rw [comp_freeToProf φ.toMonoidHom (w k), hφfun]
      exact hf k
    have hker : (Subgroup.normalClosure
        (Set.range fun k => freeToProf (Generator n) (w k))).topologicalClosure
          ≤ φ.toMonoidHom.ker :=
      Subgroup.topologicalClosure_minimal _
        (Subgroup.normalClosure_le_normal (by
          rintro _ ⟨k, rfl⟩
          exact MonoidHom.mem_ker.mpr (hfam k)))
        (IsClosed.preimage φ.continuous_toFun isClosed_singleton)
    have hrel : ∀ r ∈ gammaRelators n q R, φ r = 1 := fun r hr =>
      MonoidHom.mem_ker.mp (hker (hres.rel_mem r hr))
    -- the wild-`2` clause of `gammaLift`, from the restricted clause's own hypothesis
    have himg : ⇑φ.toMonoidHom '' wildFree n = f '' wildLetters n := by
      rw [← image_wildLetters_of, ← Set.image_comp,
        show ⇑φ.toMonoidHom ∘ (FreeProfiniteGroup.of (X := Generator n)) = f from hφfun]
    have hw2' : IsPGroup 2 (Subgroup.normalClosure (f '' wildLetters n)) := hw2
    have hle : (Subgroup.normalClosure (wildFree n)).map φ.toMonoidHom
        ≤ Subgroup.normalClosure (f '' wildLetters n) :=
      (Subgroup.map_normalClosure_le _ _).trans (le_of_eq (congrArg Subgroup.normalClosure himg))
    have hcore : ∀ V : OpenNormalSubgroup Q, IsPGroup 2 ((Subgroup.normalClosure (wildFree n)).map
        ((QuotientGroup.mk' V.toSubgroup).comp φ.toMonoidHom)) := by
      intro V
      rw [← Subgroup.map_map]
      exact (hw2'.to_le hle).map _
    exact ⟨gammaLift n q R φ hrel hcore,
      fun g => (gammaLift_gammaMk n q R φ hrel hcore (FreeProfiniteGroup.of g)).trans (hφ_of g)⟩

end Instance

/-! ## §5 Discharging `z1Equiv`'s admissibility side condition

The restricted clause bites in exactly one place downstream — `Count.toZ1w_surjective`, which
needs `IsWildTwo J c` for the *lower* marking `c = ρ ∘ gen`.  At `Γ_R` that is a theorem, and it
is GR1's `isPGroup_two_wildNormalClosure` read at the open normal subgroup `ker ρ`.  The
surjectivity hypothesis is the one `tcocycle_cardN`/`hZcardN` already carry. -/

section Wild2

variable {n q : ℕ} {R : PWord (Generator n)} {Q : Type} [Group Q] [TopologicalSpace Q]
  [DiscreteTopology Q]

/-- **The pushed marking of `Γ_R` is admissible**, for every finite discrete quotient.  This is
the `hwild2` argument of `z1Equiv`, `tcocycle_cardN` and `hZcardN`. -/
theorem isWildTwo_gammaGen_of_surjective (rho : ContinuousMonoidHom ((GammaR n q R) : Type) Q)
    (hsurj : Function.Surjective rho) :
    IsWildTwo (wildLetters n) fun g => rho (gammaGen n q R g) := by
  -- `ker ρ`, as an open normal subgroup of `Γ_R`
  have hopen : IsOpen ((rho.toMonoidHom.ker : Subgroup _) : Set ((GammaR n q R) : Type)) :=
    (isOpen_discrete ({1} : Set Q)).preimage rho.continuous_toFun
  let W : OpenNormalSubgroup ((GammaR n q R) : Type) :=
    { toSubgroup := rho.toMonoidHom.ker, isOpen' := hopen }
  -- GR1's clause at `W`, moved from `normalClosure ∘ image` to `map`
  have hquot : IsPGroup 2 ((Subgroup.normalClosure
      (Set.range fun i : Fin (n + 1) => gammaGen n q R (.wild i))).map
        (QuotientGroup.mk' W.toSubgroup)) := by
    rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
    exact isPGroup_two_wildNormalClosure W
  -- transfer across `ker (mk' W) = W = ker ρ`
  have hmap : IsPGroup 2 ((Subgroup.normalClosure
      (Set.range fun i : Fin (n + 1) => gammaGen n q R (.wild i))).map rho.toMonoidHom) :=
    isPGroup_map_of_ker_le (QuotientGroup.mk' W.toSubgroup) rho.toMonoidHom
      (le_of_eq (QuotientGroup.ker_mk' _)) hquot
  have hset : (fun g => rho (gammaGen n q R g)) '' wildLetters n
      = ⇑rho.toMonoidHom '' (Set.range fun i : Fin (n + 1) => gammaGen n q R (.wild i)) := by
    rw [image_wildLetters, ← Set.range_comp]
    rfl
  show IsPGroup 2 (Subgroup.normalClosure ((fun g => rho (gammaGen n q R g)) '' wildLetters n))
  rw [hset, ← Subgroup.map_normalClosure _ _ hsurj]
  exact hmap

/-- The form `tcocycle_cardN` and `hZcardN` want, with the marking presented as `c` through
their own `hc` hypothesis. -/
theorem isWildTwo_of_gammaGen {c : Generator n → Q}
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) Q) (hsurj : Function.Surjective rho)
    (hc : ∀ g, rho (gammaGen n q R g) = c g) : IsWildTwo (wildLetters n) c := by
  rw [← funext hc]
  exact isWildTwo_gammaGen_of_surjective rho hsurj

end Wild2

/-! ## §6 The restriction is not vacuous

CB-W's counterexamples are markings into `ℤ/3` that kill both relators while leaving `x₀` or `x₁`
nontrivial (`Count.exists_test_exponents`).  Every such marking fails `IsWildTwo`, so the
restricted clause (iii) excludes exactly them — and the plain clause, which would have to extend
them over `Γ_R`, is refuted.

Stated for an arbitrary `ℤ/3`-marking rather than for `Count.testMarking` itself, so that the
statement is self-contained; `Count.testMarking n c d` at CB-W's exponents is an instance, its
`(.wild 0)` or `(.wild 1)` value being nontrivial by `exists_test_exponents`. -/

section NotVacuous

variable {n : ℕ}

/-- Cubing kills `ℤ/3` — kernel `decide` on a three-element group. -/
theorem pow_three_eq_one (y : ZmodThree) : y ^ 3 = 1 := by revert y; decide

/-- A `2`-group inside `ℤ/3` has no nontrivial element: `3 ∣ 2 ^ k` is false. -/
theorem not_isPGroup_two_of_mem_zmodThree {H : Subgroup ZmodThree} (hp : IsPGroup 2 H)
    {y : ZmodThree} (hy : y ∈ H) (hy1 : y ≠ 1) : False := by
  obtain ⟨k, hk⟩ := hp ⟨y, hy⟩
  have hk1 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf y = 3 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _
      (orderOf_dvd_of_pow_eq_one (pow_three_eq_one y)) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hy1
    · exact h
  have hdvd : (3 : ℕ) ∣ 2 ^ k := by
    have h := orderOf_dvd_of_pow_eq_one hk1
    rwa [hord] at h
  have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  omega

/-- **The exclusion is real.**  No marking of the alphabet into `ℤ/3` with a surviving wild letter
is admissible — so no such marking is required to extend over `Γ_R`, and CB-W's are all of this
shape.  Contrast `Count.testHom`, which extends them over `GammaBare`. -/
theorem not_isWildTwo_zmodThree (f : Generator n → ZmodThree) {i : Fin (n + 1)}
    (hne : f (Generator.wild i) ≠ 1) : ¬ IsWildTwo (wildLetters n) f := fun hw2 =>
  not_isPGroup_two_of_mem_zmodThree hw2
    (Subgroup.subset_normalClosure ⟨Generator.wild i, wild_mem_wildLetters i, rfl⟩) hne

end NotVacuous

/-! ## §7 The `2`-torsion side condition, at the recursion's two modules

`z1Equiv`'s other new hypothesis, `hA₂ : ∀ a : A, a + a = 0`, is the campaign's standing spelling
of "`A` is an `𝔽₂`-module" (`GQ2/LocalLiftingDuality.lean:222`).  Both modules the count lane
feeds it are `2`-torsion by construction, so a branch never has to think about it: `T ≤ M` and
`M` is elementary abelian (`RadicalCoverData.helem`), and `V = M/T` is a quotient of `M`. -/

section TwoTorsion

variable {Bg : Type} [Group Bg] [Finite Bg]

/-- `D.T` is `2`-torsion: it sits inside the elementary abelian layer `M`. -/
theorem radT_add_self (D : RadicalCoverData Bg) (a : Additive ↥D.T) : a + a = 0 :=
  Additive.toMul.injective (Subtype.ext (D.helem _ (D.hTM (Additive.toMul a).2)))

/-- `DD.Vmod = M/T` is `2`-torsion: it is a quotient of the elementary abelian `M`. -/
theorem vmod_add_self {D : RadicalCoverData Bg} (DD : DescData D) (v : DD.Vmod) : v + v = 0 := by
  obtain ⟨m, hm⟩ := DD.hdesc_surj (Multiplicative.ofAdd v)
  have hmm : m * m = (1 : ↥D.M) := Subtype.ext (D.helem _ m.2)
  have h : Multiplicative.ofAdd (v + v) = (1 : Multiplicative DD.Vmod) := by
    rw [ofAdd_add, ← hm, ← map_mul, hmm, map_one]
  exact Multiplicative.ofAdd.injective h

end TwoTorsion

/-! ## §8 The pilot composition, end to end

The point of the file, assembled: at the `√−2` pilot both `SourceDataN` field values hold **over
`Γ_R` itself**, with every hypothesis this file introduced discharged in place.  What a branch
still supplies is exactly what it supplied before the correction — `rho`/`theta` and their
compatibilities, surjectivity, the `StokesDuality` payload — plus the one genuinely new item, the
relator-resolution seam `hres`.

Read against `Count/Compare.lean` §8: the `hpres` argument is now `IsAdmissibleMarkedPresentation`
and comes from §4, `hA₂` from §7, `hwild2` from §5.  Nothing is left for CB-4 to invent. -/

section PilotComposition

open GQ2.Dyadic.Certificates

variable {q : ℕ} {R : PWord (Generator 2)}
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- **The `√−2` pilot's `tcocycle_card` field value, over `Γ_R`.**  CB-1's
`sqrtNegTwo_tcocycle_card` with the restricted presentation, the `2`-torsion of `T` and the
admissibility of the lower marking all supplied here. -/
theorem sqrtNegTwo_tcocycle_card_gammaR
    [TopologicalSpace (Additive ↥D.T)] [DiscreteTopology (Additive ↥D.T)]
    [DistribMulAction ((GammaR 2 q R) : Type) (Additive ↥D.T)]
    [ContinuousSMul ((GammaR 2 q R) : Type) (Additive ↥D.T)]
    [TopologicalSpace (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (Additive ↥D.T) (Bg ⧸ D.M))]
    {t : Marking 2 (Bg ⧸ D.M)}
    (rho : ContinuousMonoidHom ((GammaR 2 q R) : Type) (Bg ⧸ D.M))
    (hcomp : ∀ (γ : ((GammaR 2 q R) : Type)) (a : Additive ↥D.T), γ • a = rho γ • a)
    (hc : ∀ g, rho (gammaGen 2 q R g) = t g)
    (hres : ResolvesGammaRelators 2 q R (nCompactFam 2 0 2 3))
    (hsurj : Function.Surjective rho)
    (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) (Additive ↥D.T)) :
    Nat.card (TCocycle D rho)
      = (standardNumerics 2).tMult (Nat.card (Additive ↥D.T))
        * Nat.card (fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) :=
  sqrtNegTwo_tcocycle_card rho hcomp hc (isAdmissibleMarkedPresentation_gammaR 2 q R hres)
    (radT_add_self D) (isWildTwo_of_gammaGen rho hsurj hc) hsurj hd

/-- **The `√−2` pilot's `hZcard` field value, over `Γ_R`** — the `V`-side twin. -/
theorem sqrtNegTwo_hZcard_gammaR {DD : DescData D}
    {E : Type} [Group E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [DistribMulAction E DD.Vmod] [DistribMulAction ((GammaR 2 q R) : Type) DD.Vmod]
    [TopologicalSpace (WordLift DD.Vmod E)] [DiscreteTopology (WordLift DD.Vmod E)]
    {t : Marking 2 E} {rho : ContinuousMonoidHom ((GammaR 2 q R) : Type) (Bg ⧸ D.M)}
    (theta : ContinuousMonoidHom ((GammaR 2 q R) : Type) E)
    (hround : ∀ (γ : ((GammaR 2 q R) : Type)) (v : DD.Vmod), rho0 DD rho γ • v = theta γ • v)
    (hact : ∀ (γ : ((GammaR 2 q R) : Type)) (v : DD.Vmod), γ • v = theta γ • v)
    (hc : ∀ g, theta (gammaGen 2 q R g) = t g)
    (hres : ResolvesGammaRelators 2 q R (nCompactFam 2 0 2 3))
    (hsurj : Function.Surjective theta)
    (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) DD.Vmod)
    (hsimple : IsSimpleModTwo E DD.Vmod) (hnt : ∃ (g : E) (v : DD.Vmod), g • v ≠ v) :
    Nat.card (VCocycle DD rho)
      = Nat.card DD.Vmod * (standardNumerics 2).h1Mult (Nat.card DD.Vmod) :=
  sqrtNegTwo_hZcard theta hround hact hc (isAdmissibleMarkedPresentation_gammaR 2 q R hres)
    (vmod_add_self DD) (isWildTwo_of_gammaGen theta hsurj hc) hsurj hd hsimple hnt

end PilotComposition

end Count

end GQ2.Dyadic
