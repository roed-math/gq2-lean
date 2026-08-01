/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Count.WildDischarge
import GQ2.Roe.Main

/-!
# The `n = 1` wrapper: the L-word machinery recovers the `ℚ₂` theorem  (ticket AS4)

**Merge gate 8.**  The dyadic campaign's degree-`n` apparatus, instantiated at the smallest
degree of the frozen odd-degree branch word `L_sq` (`GQ2/Dyadic/Words/L.lean`, selection-freeze
row 1), reproduces the frozen `ℚ₂` theorem — and the frozen `ℚ₂` capstones still typecheck at
their own statements alongside it.

## What is proved

1. **§1–§2 the alphabet transport.**  `Generator 1 = {σ, τ, x₀, x₁}` is `Fin 4` in the order of
   `GQ2.univMarking`, and the induced maps `F(σ, τ, x₀, x₁) ⇄ F₄` are mutually inverse
   (`toQ2F`/`ofQ2F`).  There is no `FreeProfiniteGroup` functoriality in the repo, so both maps
   are classified by hand through `FreeProfiniteGroup.homEquiv`.
2. **§3 the two admissibility conditions are one condition** (`isAdmissibleU_iff_isAdmissibleUR`).
   GR1's `GQ2.Dyadic.IsAdmissibleU 1 2 (lSqW 0)` and Roe's `GQ2.IsAdmissibleUR` match clause for
   clause: generation is automatic on both sides (`GQ2.generates_univMarking_map`), the two
   relators transport (`toQ2F_tameRelatorGen`, `toQ2F_eval_lSqW`), and the `2`-core clauses
   transfer through AdmissibleR's kernel lemma `isPGroup_map_of_ker_le`.
3. **§4 the groups are the same group.**  `NR_eq_comap` (the two intersections correspond) and
   `gammaR_lSq_equiv_roe : ContinuousMulEquiv (GammaR 1 2 (lSqW 0)) GQ2.GammaR`, **marked**:
   `toRoe` sends the four dyadic letters to `gammaSigmaR`, `gammaTauR`, `gammaX0R`, `gammaX1R`.
4. **§5 the recovery theorem, twice.**  `candidateGroup_lSq_equiv_absGalQ2` and
   `candidateGroup_lSq_equiv_absGalQ2_via_sourcesN`, both
   `Nonempty (ContinuousMulEquiv (candidateGroup 1 2 (lSqW 0)) AbsGalQ2)` and both
   **unconditional** — no hypothesis binder, no instance binder, no `sorry`.  The first composes
   §4 with Roe's terminal `GQ2.main_presentation_literal_roe_unconditional` (whose
   `BLabHypothesis` the L-campaign discharged as `GQ2.Roe.Labute.bLab`).  The second composes §4
   with **SD3's own degree-`n` reconstruction corollary** at `n = 1`
   (`nonempty_continuousMulEquiv_of_sourcesN` on SD-R1's `sourceR_N`/`sourceF_N`), so the
   *dyadic* pipeline closes the loop and not merely the frozen `ℚ₂` one.  `q2_capstones_agree` is
   the merge-gate-8 regression: `Γ_A ≅ G_ℚ₂`, `Γ_R ≅ G_ℚ₂` and `Γ_{L_sq,1} ≅ G_ℚ₂` side by side.
5. **§6 AS1's `WordCertificate` fields, at `(n, q, R) = (1, 2, L_sq)`,** for the ones the landed
   stack proves — see the inventory below.

The only mathematics beyond bookkeeping is §3, and its one non-formal input is WL-a's
`eval_lSqW_zero`: the certificate's tree for `L_sq` at `n = 1` denotes `Marking.wildRelatorR`,
the word `GQ2.GammaR` is defined by.  Everything else is cited.

## Why the group-level identification had to be proved and not merely stated

`GQ2.Dyadic.GammaR n q R` (GR1, `GQ2/Dyadic/AdmissibleR.lean:230`) and `GQ2.GammaR`
(`GQ2/Roe/GammaR.lean:196`) are **two independent constructions**: both are admissible limits
`F ⧸ N_R`, but over different alphabets, with different `IsAdmissibleU` predicates (the dyadic
one drops the `Generates` clause and phrases the pro-`2` clause with `Subgroup.map`), and with
the wild relator given by two *different trees* — the certificate's `x₀^{-3}` with an `n`-ary
`Multiply` versus the `ℚ₂` ledger's `(x₀³)⁻¹` with left association.  Nothing was definitional.

## Inventory: AS1's `WordCertificate 1 2 (lSqW 0) P hP nuP SN`

| field | status here |
|---|---|
| `tameSpecialization` | **done** (`tameSpecializes_lSq`) |
| `coreRel`, `proTwoWord` | **done** (`coreRelLSq`, `proTwoWord_lSq` = WL-a's Gate-C headline) |
| `tfg` | **done, and generic in `n, q, R`** (`gammaR_tfg`) |
| `htame` | **done** (`htame_lSq`, F3b's `tameOfSpec_surjective`) |
| `hwild` | **done** (`hwild_lSq_one`, GR1's generic discharge) |
| `pro2`, `ker_pro2`, `hpro2`, `compat` | ⚠ **not built** — see below |
| `smulZmod2`, `contSMulZmod2`, `htriv` | ⚠ not built (routine; unwritten for `GammaR`) |
| `exactLifting`, `stokes`, `scalar`, `determinant` | ⚠ **not built; not citable** |

### ⚠ What blocks the last two rows, precisely

* **`pro2` and friends.**  AS1's divergence 3 is *not* closed at `n = 1` by this file, and the
  reason is a missing generic transport, not missing mathematics.  `GQ2.Roe.exists_pro2R`
  (`GQ2/Roe/Main.lean:226`) supplies a `pro2R : Γ_R → Π` with `ν`-compatibility, surjectivity
  and `ker = proPKernel 2 Γ_R`; composing with `toRoe` gives the map, and surjectivity is free.
  What is missing is `Subgroup.comap e (proPKernel p B) = proPKernel p A` for a
  `ContinuousMulEquiv e : A ≃ₜ* B` (needed for `ker_pro2`) and a "two continuous homs out of
  `GammaR n q R` agreeing on `gammaGen` are equal" ext lemma (needed to identify F3b's
  `tameOfSpec` with `phiR ∘ toRoe`, hence for `compat`).  Both are short, generic and belong in
  `GQ2/MaxProP.lean` and `GQ2/Dyadic/AdmissibleR.lean` respectively — **owed by:** nobody
  currently; they are the natural follow-on.
* **The four analytic clauses.**  These are AS1's divergence 4 and they are *not* AS4-shaped.
  `WordCertificate`'s `exactLifting`/`stokes`/`scalar`/`determinant` are stated at
  `Γ := GammaR n q R`, in the `K`-layer vocabulary (`LiftsOverK`, `BoundaryFrameK`,
  `GaussZResidueK`).  The `ℚ₂` proofs of the corresponding counts exist — SD-R1 already packaged
  them as `GQ2.Dyadic.sourceR_N` (`GQ2/Dyadic/SourceDataN.lean:421`), a full
  `SourceDataN 1 2 PiBd _ nuTwo (standardNumerics 1)` whose carrier is `GQ2.GammaR` — but every
  one of them is a statement *about that carrier*, quantified over `BoundaryLiftsK`,
  `RecursionFrame`, `TCocycle`, `VCocycle` and `GaussZResidueK` data all of which depend on `Γ`
  through its boundary map.  Moving them across `gammaR_lSq_equiv_roe` is a `SourceDataN`
  transport lemma, i.e. an equivalence of all of those dependent families — a ticket of its own,
  and one nobody owns.  **This file therefore does not construct a `WordCertificate`, and the
  recovery theorem deliberately does not go through `candidate_equiv_absoluteGalois`.**

  ⚠ The consequence is worth stating plainly for AS5 and the G3 sign-off: at `n = 1` the dyadic
  recursion *does* reach `Γ_R ≅ G_ℚ₂` without a `WordCertificate` — that is
  `candidateGroup_lSq_equiv_absGalQ2_via_sourcesN` — but it reaches it with the record's `Γ`
  spelled `GQ2.GammaR`, because `sourceR_N` is built from the frozen `ℚ₂` supply lemmas rather
  than from a word certificate.  §4 is exactly the bridge between the two spellings.  So what
  the missing `WordCertificate` costs at `n = 1` is *only* the record-level plumbing, not the
  theorem; at general `K` it costs the theorem, and that is divergence 4's real content.

## Axiom posture

`sorry`-free; **no new axiom, and no `decide` outside the two four-element alphabet tables**.
Every declaration prints the standard three or a strict subset, with exactly four exceptions —
the two recovery theorems, the `hBLab` twin of the first, and `q2_capstones_agree` — which print
**exactly** the axiom list of `GQ2.main_presentation_literal_roe_unconditional`, i.e. the frozen
`ℚ₂` literature census of `GQ2/Foundations/Axioms.lean`.  Nothing is added, and in particular the
dyadic census axioms `B5-K`/`B10-K` (`markedRecipAt`, `orientedTameQuotientAt`) are **not**
consumed anywhere in this file: the `n = 1` route never enters the `K`-layer.

## Sources

Board `docs/dyadic/tickets.md` lane AS row AS4 and the merge-gate-8 line; `docs/dyadic/plan.md`
§7; `docs/dyadic/wl-recon.md` §4.2 (which re-scoped this ticket, moved SQ5's word-theorem
restatement here, and correctly predicted that the target is the hypothesis-free
`main_presentation_literal_roe_unconditional`).
-/

namespace GQ2.Dyadic.QTwo

open GQ2 GQ2.Dyadic.Words.LSq CategoryTheory

/-! ## §1 The `n = 1` alphabet is the `ℚ₂` alphabet -/

/-- The `n = 1` letter `σ, τ, x₀, x₁` as the index `0, 1, 2, 3` of `GQ2.univMarking`. -/
def genToFin : Generator 1 → Fin 4
  | .sigma => 0
  | .tau => 1
  | .wild i => i.succ.succ

/-- The inverse table. -/
def finToGen : Fin 4 → Generator 1 := ![.sigma, .tau, .wild 0, .wild 1]

@[simp] theorem finToGen_genToFin (g : Generator 1) : finToGen (genToFin g) = g := by
  revert g; decide

@[simp] theorem genToFin_finToGen (i : Fin 4) : genToFin (finToGen i) = i := by
  revert i; decide

/-- The alphabet equivalence `{σ, τ, x₀, x₁} ≃ Fin 4`. -/
def alphEquiv : Generator 1 ≃ Fin 4 where
  toFun := genToFin
  invFun := finToGen
  left_inv := finToGen_genToFin
  right_inv := genToFin_finToGen

/-! ## §2 The free profinite groups agree -/

/-- Two continuous homs out of a free profinite group agreeing on the generators are equal. -/
theorem free_hom_ext {X : Type} {P : ProfiniteGrp} {f g : FreeProfiniteGroup X ⟶ P}
    (h : ∀ x, f (FreeProfiniteGroup.of x) = g (FreeProfiniteGroup.of x)) : f = g :=
  (FreeProfiniteGroup.homEquiv X P).injective <| funext fun x => by
    rw [FreeProfiniteGroup.homEquiv_apply, FreeProfiniteGroup.homEquiv_apply]; exact h x

/-- `F(σ, τ, x₀, x₁) ⟶ F₄`, letter by letter. -/
noncomputable def toQ2Free : FreeProfiniteGroup (Generator 1) ⟶ FreeProfiniteGroup (Fin 4) :=
  (FreeProfiniteGroup.homEquiv (Generator 1) (FreeProfiniteGroup (Fin 4))).symm
    fun g => FreeProfiniteGroup.of (genToFin g)

/-- `F₄ ⟶ F(σ, τ, x₀, x₁)`, letter by letter. -/
noncomputable def ofQ2Free : FreeProfiniteGroup (Fin 4) ⟶ FreeProfiniteGroup (Generator 1) :=
  (FreeProfiniteGroup.homEquiv (Fin 4) (FreeProfiniteGroup (Generator 1))).symm
    fun i => FreeProfiniteGroup.of (finToGen i)

@[simp] theorem toQ2Free_of (g : Generator 1) :
    toQ2Free (FreeProfiniteGroup.of g) = FreeProfiniteGroup.of (genToFin g) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem ofQ2Free_of (i : Fin 4) :
    ofQ2Free (FreeProfiniteGroup.of i) = FreeProfiniteGroup.of (finToGen i) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem ofQ2Free_comp_toQ2Free : toQ2Free ≫ ofQ2Free = 𝟙 _ :=
  free_hom_ext fun x => by simp

theorem toQ2Free_comp_ofQ2Free : ofQ2Free ≫ toQ2Free = 𝟙 _ :=
  free_hom_ext fun x => by simp

/-- The alphabet transport `F(σ, τ, x₀, x₁) → F₄`, as a continuous monoid hom. -/
noncomputable def toQ2F : ContinuousMonoidHom ((FreeProfiniteGroup (Generator 1)) : Type)
    ((FreeProfiniteGroup (Fin 4)) : Type) := toQ2Free.hom

/-- Its inverse. -/
noncomputable def ofQ2F : ContinuousMonoidHom ((FreeProfiniteGroup (Fin 4)) : Type)
    ((FreeProfiniteGroup (Generator 1)) : Type) := ofQ2Free.hom

@[simp] theorem toQ2F_of (g : Generator 1) :
    toQ2F (FreeProfiniteGroup.of g) = FreeProfiniteGroup.of (genToFin g) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem ofQ2F_of (i : Fin 4) :
    ofQ2F (FreeProfiniteGroup.of i) = FreeProfiniteGroup.of (finToGen i) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem coe_toQ2F_toMonoidHom : ⇑toQ2F.toMonoidHom = ⇑toQ2F := rfl

@[simp] theorem coe_ofQ2F_toMonoidHom : ⇑ofQ2F.toMonoidHom = ⇑ofQ2F := rfl

@[simp] theorem ofQ2F_toQ2F (w : ((FreeProfiniteGroup (Generator 1)) : Type)) :
    ofQ2F (toQ2F w) = w := by
  rw [show ofQ2F (toQ2F w) = (toQ2Free ≫ ofQ2Free) w from rfl, ofQ2Free_comp_toQ2Free,
    ProfiniteGrp.id_apply]

@[simp] theorem toQ2F_ofQ2F (w : ((FreeProfiniteGroup (Fin 4)) : Type)) :
    toQ2F (ofQ2F w) = w := by
  rw [show toQ2F (ofQ2F w) = (ofQ2Free ≫ toQ2Free) w from rfl, toQ2Free_comp_ofQ2Free,
    ProfiniteGrp.id_apply]

theorem toQ2F_surjective : Function.Surjective toQ2F := fun w => ⟨ofQ2F w, toQ2F_ofQ2F w⟩

theorem ofQ2F_surjective : Function.Surjective ofQ2F := fun w => ⟨toQ2F w, ofQ2F_toQ2F w⟩

theorem toQ2F_injective : Function.Injective toQ2F := fun a b h => by
  rw [← ofQ2F_toQ2F a, h, ofQ2F_toQ2F]

/-- **The universal marking, transported.**  The `n = 1` tautological marking of
`F(σ, τ, x₀, x₁)` pushed along the alphabet transport is `GQ2.univMarking` — read in the
`Marking 1` vocabulary through `Marking.ofQ2`. -/
theorem freeMarking_map_toQ2F :
    (freeMarking 1).map ⇑toQ2F = Marking.ofQ2 univMarking := by
  ext g
  match g with
  | .sigma => exact toQ2F_of _
  | .tau => exact toQ2F_of _
  | .wild ⟨0, _⟩ => exact toQ2F_of _
  | .wild ⟨1, _⟩ => exact toQ2F_of _
  | .wild ⟨k + 2, hk⟩ => exact absurd hk (by omega)

/-! ## §3 The two relators, and the two admissibility conditions -/

/-- The dyadic tame relator at `(n, q) = (1, 2)` transports to `GQ2.Marking.tameRelator`. -/
theorem toQ2F_tameRelatorGen : toQ2F (tameRelatorGen 1 2) = univMarking.tameRelator := by
  simp only [tameRelatorGen, _root_.GQ2.Marking.tameRelator, univMarking, conjP,
    map_mul, map_inv, map_pow, toQ2F_of, genToFin]

/-- **The frozen `L_sq` word at `n = 1` transports to Roe's wild relator `r_R`** — WL-a's
`eval_lSqW_zero`, moved upstairs into the free profinite group.  This is the identification the
whole file turns on. -/
theorem toQ2F_eval_lSqW :
    toQ2F ((freeMarking 1).eval (lSqW 0)) = univMarking.wildRelatorR := by
  rw [Marking.map_eval, freeMarking_map_toQ2F, eval_lSqW_zero]

/-- The wild letters `x₀, x₁` transport to the `ℚ₂` wild pair. -/
theorem image_wildFree_toQ2F :
    ⇑toQ2F.toMonoidHom '' wildFree 1 = {univMarking.x₀, univMarking.x₁} := by
  rw [image_wildFree]
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff, univMarking]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl (toQ2F_of _)
    · exact Or.inr (toQ2F_of _)
  · rintro (rfl | rfl)
    exacts [⟨0, toQ2F_of _⟩, ⟨1, toQ2F_of _⟩]

/-- **The `n = 1` admissibility criteria agree.**  An open normal `U ≤ F(σ, τ, x₀, x₁)` is
`L_sq`-admissible in the dyadic sense (`GQ2/Dyadic/AdmissibleR.lean`) exactly when the
corresponding `V ≤ F₄` is `R`-admissible in Roe's sense (`GQ2/Roe/GammaR.lean`).

All four clauses are *cited*, not reproved: `GQ2.generates_univMarking_map` for the generation
clause `IsAdmissibleU` drops, `GQ2.Marking.map_tameRelator_eq_one_iff` and
`GQ2.Marking.map_wildRelatorR_eq_one_iff` for the two relations, and AdmissibleR's own §0
kernel-transfer `isPGroup_map_of_ker_le` for the `2`-core clause. -/
theorem isAdmissibleU_iff_isAdmissibleUR
    (U : OpenNormalSubgroup ((FreeProfiniteGroup (Generator 1)) : Type))
    (V : OpenNormalSubgroup ((FreeProfiniteGroup (Fin 4)) : Type))
    (hUV : ∀ w, w ∈ U.toSubgroup ↔ toQ2F w ∈ V.toSubgroup) :
    IsAdmissibleU 1 2 (lSqW 0) U ↔ GQ2.IsAdmissibleUR V := by
  haveI : U.toSubgroup.Normal := U.isNormal'
  haveI : V.toSubgroup.Normal := V.isNormal'
  set qU := QuotientGroup.mk' U.toSubgroup with hqU
  set qV := QuotientGroup.mk' V.toSubgroup with hqV
  -- the composite `F(σ,τ,x₀,x₁) → F₄ → F₄ ⧸ V` has kernel exactly `U`
  have hker : (qV.comp toQ2F.toMonoidHom).ker = U.toSubgroup := by
    ext w
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, hqV, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact (hUV w).symm
  have hkerU : qU.ker = U.toSubgroup := QuotientGroup.ker_mk' _
  -- ### the `2`-core clause
  have hcore : IsPGroup 2 ((Subgroup.normalClosure (wildFree 1)).map qU)
      ↔ (univMarking.map qV).Pro2Core := by
    have hmid : (Subgroup.normalClosure (wildFree 1)).map (qV.comp toQ2F.toMonoidHom)
        = (Subgroup.normalClosure ({univMarking.x₀, univMarking.x₁} : Set _)).map qV := by
      rw [← Subgroup.map_map, Subgroup.map_normalClosure _ _ toQ2F_surjective,
        image_wildFree_toQ2F]
    have hR : (univMarking.map qV).Pro2Core ↔ IsPGroup 2
        ((Subgroup.normalClosure ({univMarking.x₀, univMarking.x₁} : Set _)).map qV) := by
      rw [_root_.GQ2.Marking.Pro2Core,
        Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), Set.image_pair]
      rfl
    rw [hR, ← hmid]
    exact ⟨fun h => isPGroup_map_of_ker_le qU _ (by rw [hkerU, hker]) h,
      fun h => isPGroup_map_of_ker_le _ qU (by rw [hkerU, hker]) h⟩
  -- ### the two relations
  have htame : tameRelatorGen 1 2 ∈ U.toSubgroup ↔ (univMarking.map qV).TameRel := by
    rw [hUV, toQ2F_tameRelatorGen, ← QuotientGroup.eq_one_iff]
    exact _root_.GQ2.Marking.map_tameRelator_eq_one_iff (quotientMk V.toSubgroup) univMarking
  have hwild : (freeMarking 1).eval (lSqW 0) ∈ U.toSubgroup ↔ (univMarking.map qV).WildRelR := by
    rw [hUV, toQ2F_eval_lSqW, ← QuotientGroup.eq_one_iff]
    exact _root_.GQ2.Marking.map_wildRelatorR_eq_one_iff (quotientMk V.toSubgroup) univMarking
  -- ### assembly
  rw [IsAdmissibleU, _root_.GQ2.IsAdmissibleUR, _root_.GQ2.Marking.AdmissibleR, gammaRelators]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  rw [htame, hwild, hcore]
  exact ⟨fun h => ⟨generates_univMarking_map V, h.1.1, h.1.2, h.2⟩,
    fun h => ⟨⟨h.2.1, h.2.2.1⟩, h.2.2.2⟩⟩

/-! ## §4 `N_R` at `n = 1` is Roe's `N_R`, and `Γ_R` at `n = 1` is Roe's `Γ_R` -/

/-- Pull an open normal subgroup of `F₄` back along the alphabet transport. -/
noncomputable def comapON (V : OpenNormalSubgroup ((FreeProfiniteGroup (Fin 4)) : Type)) :
    OpenNormalSubgroup ((FreeProfiniteGroup (Generator 1)) : Type) where
  toSubgroup := Subgroup.comap toQ2F.toMonoidHom V.toSubgroup
  isOpen' := V.toOpenSubgroup.isOpen.preimage toQ2F.continuous_toFun
  isNormal' := V.isNormal'.comap _

/-- …and push one forward, i.e. pull back along the inverse transport. -/
noncomputable def comapON' (U : OpenNormalSubgroup ((FreeProfiniteGroup (Generator 1)) : Type)) :
    OpenNormalSubgroup ((FreeProfiniteGroup (Fin 4)) : Type) where
  toSubgroup := Subgroup.comap ofQ2F.toMonoidHom U.toSubgroup
  isOpen' := U.toOpenSubgroup.isOpen.preimage ofQ2F.continuous_toFun
  isNormal' := U.isNormal'.comap _

/-- **`N_R` at `n = 1` is the pullback of Roe's `N_R`.**  Both are intersections over the
admissible family, and §3 matches the families letter for letter. -/
theorem NR_eq_comap : NR 1 2 (lSqW 0) = Subgroup.comap toQ2F.toMonoidHom GQ2.NR := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · rw [Subgroup.mem_comap, GQ2.NR, Subgroup.mem_iInf]
    rintro ⟨V, hV⟩
    exact NR_le_of_isAdmissibleU
      ((isAdmissibleU_iff_isAdmissibleUR (comapON V) V fun _ => Iff.rfl).mpr hV) hx
  · rw [Subgroup.mem_comap] at hx
    rw [NR, Subgroup.mem_iInf]
    rintro ⟨U, hU⟩
    have hV : GQ2.IsAdmissibleUR (comapON' U) :=
      (isAdmissibleU_iff_isAdmissibleUR U (comapON' U) fun w => by
        show _ ↔ ofQ2F.toMonoidHom (toQ2F w) ∈ U.toSubgroup
        simp).mp hU
    have h := (GQ2.isAdmissibleUR_iff_NR_le _).mp hV hx
    rw [show (comapON' U).toSubgroup = Subgroup.comap ofQ2F.toMonoidHom U.toSubgroup from rfl,
      Subgroup.mem_comap] at h
    simpa using h

/-- **The `n = 1` candidate group maps to Roe's `Γ_R`.** -/
noncomputable def toRoe :
    ContinuousMonoidHom ((GammaR 1 2 (lSqW 0)) : Type) ((GQ2.GammaR) : Type) :=
  quotientLift (NR 1 2 (lSqW 0)) ((quotientMk GQ2.NR).comp toQ2F) fun x hx => by
    rw [MonoidHom.mem_ker]
    show quotientMk GQ2.NR (toQ2F x) = 1
    rw [quotientMk_eq_one_iff]
    rw [NR_eq_comap, Subgroup.mem_comap] at hx
    exact hx

/-- …and back. -/
noncomputable def fromRoe :
    ContinuousMonoidHom ((GQ2.GammaR) : Type) ((GammaR 1 2 (lSqW 0)) : Type) :=
  quotientLift GQ2.NR ((quotientMk (NR 1 2 (lSqW 0))).comp ofQ2F) fun y hy => by
    rw [MonoidHom.mem_ker]
    show quotientMk (NR 1 2 (lSqW 0)) (ofQ2F y) = 1
    rw [quotientMk_eq_one_iff, NR_eq_comap, Subgroup.mem_comap]
    simpa using hy

@[simp] theorem toRoe_gammaMk (w : ((FreeProfiniteGroup (Generator 1)) : Type)) :
    toRoe (gammaMk 1 2 (lSqW 0) w) = quotientMk GQ2.NR (toQ2F w) := rfl

@[simp] theorem fromRoe_quotientMk (w : ((FreeProfiniteGroup (Fin 4)) : Type)) :
    fromRoe (quotientMk GQ2.NR w) = gammaMk 1 2 (lSqW 0) (ofQ2F w) := rfl

theorem fromRoe_toRoe (g : ((GammaR 1 2 (lSqW 0)) : Type)) : fromRoe (toRoe g) = g := by
  obtain ⟨w, rfl⟩ := gammaMk_surjective 1 2 (lSqW 0) g
  rw [toRoe_gammaMk, fromRoe_quotientMk, ofQ2F_toQ2F]

theorem toRoe_fromRoe (g : ((GQ2.GammaR) : Type)) : toRoe (fromRoe g) = g := by
  obtain ⟨w, rfl⟩ := quotientMk_surjective GQ2.NR g
  rw [fromRoe_quotientMk, toRoe_gammaMk, toQ2F_ofQ2F]

/-- **AS4's core identification: at `n = 1` the L-word candidate group *is* Roe's `Γ_R`.**

`candidateGroup 1 2 (L_sq) = ⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², R^{sq}_{L,1} = 1, ⟪x₀,x₁⟫ pro-2⟩_prof`
(F3's `GammaR` at `n = 1`, `q = q_{ℚ₂} = 2`, `R = lSqW 0`) is `GQ2.GammaR`, the note's
Definition 1.1 object, as topological groups.

Nothing here is a re-derivation: the whole content is §3's admissibility match, whose only
non-formal input is WL-a's `eval_lSqW_zero` (the frozen `L_sq` tree denotes
`Marking.wildRelatorR`). -/
noncomputable def gammaR_lSq_equiv_roe :
    ContinuousMulEquiv ((GammaR 1 2 (lSqW 0)) : Type) ((GQ2.GammaR) : Type) where
  toFun := toRoe
  invFun := fromRoe
  left_inv := fromRoe_toRoe
  right_inv := toRoe_fromRoe
  map_mul' := map_mul toRoe
  continuous_toFun := toRoe.continuous_toFun
  continuous_invFun := fromRoe.continuous_toFun

/-! ### The identification is *marked*

`toRoe` carries the four dyadic generator letters to Roe's four marked generators
(`GQ2/Roe/Tame.lean`), on the nose.  This is what downstream consumers (AS5, and any `n = 1`
regression against the frozen chain) need: the isomorphism is not merely abstract. -/

@[simp] theorem toRoe_gammaGen (g : Generator 1) :
    toRoe (gammaGen 1 2 (lSqW 0) g) = quotientMk GQ2.NR (FreeProfiniteGroup.of (genToFin g)) := by
  rw [gammaGen, toRoe_gammaMk, toQ2F_of]

@[simp] theorem toRoe_sigma : toRoe (gammaGen 1 2 (lSqW 0) .sigma) = gammaSigmaR := toRoe_gammaGen _

@[simp] theorem toRoe_tau : toRoe (gammaGen 1 2 (lSqW 0) .tau) = gammaTauR := toRoe_gammaGen _

@[simp] theorem toRoe_x0 : toRoe (gammaGen 1 2 (lSqW 0) (.wild 0)) = gammaX0R := toRoe_gammaGen _

@[simp] theorem toRoe_x1 : toRoe (gammaGen 1 2 (lSqW 0) (.wild 1)) = gammaX1R := toRoe_gammaGen _

/-! ## §5 The recovery theorem -/

/-- **AS4's headline — the L-word machinery at `n = 1` recovers the `ℚ₂` theorem.**

`candidateGroup 1 2 (L_sq)`, F3's admissible candidate group on the frozen odd-degree branch
word at its smallest degree, is the absolute Galois group of `ℚ₂`:

`⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², (x₀^σ)⁻¹(x₀⁻³τ)^{ω₂}x₁²[x₁, x₁^{σ₂}] = 1, ⟪x₀,x₁⟫ pro-2⟩_prof ≅ G_ℚ₂`.

**Unconditional**: no hypothesis binder, no `sorry`.  Two named inputs, both cited:
`gammaR_lSq_equiv_roe` (§4, this file's mathematics) and Roe's terminal
`GQ2.main_presentation_literal_roe_unconditional`, whose `BLabHypothesis` the L-campaign
discharged (`GQ2.Roe.Labute.bLab`). -/
theorem candidateGroup_lSq_equiv_absGalQ2 :
    Nonempty (ContinuousMulEquiv ((candidateGroup 1 2 (lSqW 0)) : Type) AbsGalQ2) :=
  ⟨gammaR_lSq_equiv_roe.trans GQ2.main_presentation_literal_roe_unconditional.some⟩

/-- The `hBLab`-parametrized form, kept because it is the statement the R-campaign gates audit
(`GQ2.main_presentation_literal_roe`); `candidateGroup_lSq_equiv_absGalQ2` is this at
`GQ2.Roe.Labute.bLab`. -/
theorem candidateGroup_lSq_equiv_absGalQ2_of_bLab (hBLab : GQ2.BLabHypothesis) :
    Nonempty (ContinuousMulEquiv ((candidateGroup 1 2 (lSqW 0)) : Type) AbsGalQ2) :=
  ⟨gammaR_lSq_equiv_roe.trans (GQ2.main_presentation_literal_roe hBLab).some⟩

/-! ### The same conclusion, through the *dyadic* recursion

The theorem above composes §4 with the frozen `ℚ₂` capstone.  The one below reaches the same
conclusion through SD3's degree-`n` reconstruction corollary
(`nonempty_continuousMulEquiv_of_sourcesN`, packet Thm 11.1 clause 3) applied to SD-R1's two
`n = 1` records — so the *dyadic* pipeline, not the `ℚ₂` one, closes the loop, and §4 is what
lets it land on the L-word candidate group rather than on `GQ2.GammaR`.

The `AbsGalQ2` topology instances are file-local, as in `GQ2/Roe/Main.lean` and
`GQ2/PresentationLiteral.lean`, so the statement carries no instance binders. -/

section DyadicRoute

noncomputable local instance absGalQ2_compactSpace_qtwo : CompactSpace AbsGalQ2 := by
  change CompactSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

noncomputable local instance absGalQ2_totallyDisconnectedSpace_qtwo :
    TotallyDisconnectedSpace AbsGalQ2 := by
  change TotallyDisconnectedSpace (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2])
  infer_instance

/-- **The recovery theorem through SD3.**  `candidateGroup 1 2 (L_sq) ≅ G_ℚ₂`, obtained from the
dyadic degree-`n` reconstruction corollary at `n = 1` rather than from the frozen `ℚ₂` capstone:
SD-R1's `sourceR_N` (carrier `GQ2.GammaR`) against `sourceF_N` (carrier `G_ℚ₂`), over the shared
slot `(1, 2, Π, ν₂, standardNumerics 1)`, then §4's identification.

Also **unconditional**: the `B-Lab` binder is `GQ2.Roe.Labute.bLab`, the `BoundaryMaps` witness
is `SectionThree.boundaryMapsWitness`, and the orientation clause is
`GQ2.tameUnitOrientation_witness`.  The four §10 instantiation-side conditions are the frozen
`ℚ₂` facts (`phiR_surjective`, `ker_phiR` + `isProP_wildCoreR`, and two `BoundaryMaps` fields). -/
theorem candidateGroup_lSq_equiv_absGalQ2_via_sourcesN :
    Nonempty (ContinuousMulEquiv ((candidateGroup 1 2 (lSqW 0)) : Type) AbsGalQ2) := by
  set SR := sourceR_N GQ2.Roe.Labute.bLab with hSR
  set SF := sourceF_N SectionThree.boundaryMapsWitness GQ2.localReciprocity
    GQ2.tameUnitOrientation_witness with hSF
  have htame₁ : Function.Surjective SR.tame := phiR_surjective
  have hwild₁ : IsProP 2 SR.tame.toMonoidHom.ker := by
    have h : IsProP 2 phiR.toMonoidHom.ker := by rw [ker_phiR]; exact isProP_wildCoreR
    exact h
  have htame₂ : Function.Surjective SF.tame :=
    SectionThree.boundaryMapsWitness.tameF_surjective
  have hwild₂ : IsProP 2 SF.tame.toMonoidHom.ker := SectionThree.boundaryMapsWitness.wild_isProP
  obtain ⟨e⟩ := nonempty_continuousMulEquiv_of_sourcesN SR SF two_ne_zero even_two
    SectionThree.nuTwo_surjective htame₁ hwild₁ htame₂ hwild₂
  exact ⟨gammaR_lSq_equiv_roe.trans e⟩

end DyadicRoute

/-- **Merge gate 8, regression half.**  The two frozen `ℚ₂` capstones still typecheck at their
own statements, side by side with the `n = 1` route: `Γ_A ≅ G_ℚ₂` (the paper's Theorem 1.2,
`GQ2.main_presentation_literal`), `Γ_R ≅ G_ℚ₂` (the note's ⟦thm:main⟧), and now
`Γ_{L_sq,1} ≅ G_ℚ₂`.  The three left-hand sides are *three different presentations*: `Γ_A` is
the collector-cored `Γ_A`, `Γ_R` the Roe candidate, and `Γ_{L_sq,1}` the R2-frozen square word
read through F3's degree-`n` machinery — and §4 identifies the last two. -/
theorem q2_capstones_agree :
    Nonempty (ContinuousMulEquiv (GammaA : Type) AbsGalQ2)
      ∧ Nonempty (ContinuousMulEquiv (GQ2.GammaR : Type) AbsGalQ2)
      ∧ Nonempty (ContinuousMulEquiv ((candidateGroup 1 2 (lSqW 0)) : Type) AbsGalQ2) :=
  ⟨GQ2.main_presentation_literal, GQ2.main_presentation_literal_roe_unconditional,
    candidateGroup_lSq_equiv_absGalQ2⟩

/-! ## §6 AS1's `WordCertificate` at `n = 1`: the fields that are discharged

The fields below are the ones the landed stack proves at `(n, q, R) = (1, 2, L_sq)`.  What is
*not* here is exactly AS1's divergences 3 and 4 — see the module docstring. -/

/-- **Field 1 (`tameSpecialization`).**  One line, WL-a's tame boundary value fed to F3b's
`tameSpecializes_of_tau_pow`. -/
theorem tameSpecializes_lSq : TameSpec.TameSpecializes 1 2 (lSqW 0) :=
  TameSpec.tameSpecializes_of_tau_pow two_ne_zero even_two (eval_killWildLetters_lSq 0 _)

/-- **Field 2 (`coreRel`).**  The pro-`2` core relator of the `n = 1` branch: SqCore's rank-3
square-commutator word at `h = 0`. -/
noncomputable def coreRelLSq (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking 1 G) : G :=
  SqCore.sqRelWord (sqIdxMark (h := 0) t)

/-- **Field 2 (`proTwoWord`).**  Verbatim WL-a's Gate-C headline at `h = 0`. -/
theorem proTwoWord_lSq (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking 1 G) :
    t.eval (pro2 (lSqW 0)) = coreRelLSq G t :=
  eval_pro2_lSqW_eq_sqRelWord 0 t

/-- **Field `tfg`.**  Generic in `n, q, R`, and not owed to any lane: `Γ_R` is a continuous
quotient of a free profinite group on a `Fintype` alphabet. -/
theorem gammaR_tfg (n q : ℕ) (R : PWord (Generator n)) :
    ∃ s : Finset ((GammaR n q R) : Type),
      (Subgroup.closure (s : Set ((GammaR n q R) : Type))).topologicalClosure = ⊤ :=
  IsTopologicallyFinGen.of_surjective (gammaMk n q R).toMonoidHom
    (gammaMk n q R).continuous_toFun (gammaMk_surjective n q R)
    isTopologicallyFinGen_freeProfiniteGroup

/-- **Field `htame`** (§10 instantiation-side condition 1) at `n = 1`. -/
theorem htame_lSq : Function.Surjective (TameSpec.tameOfSpec 1 2 (lSqW 0) tameSpecializes_lSq) :=
  TameSpec.tameOfSpec_surjective _

/-- **Field `hwild`** (§10 instantiation-side condition 2) at `n = 1` — GR1's discharge, which
is generic; `Count.hwild_lSq` is its `L_sq` row. -/
theorem hwild_lSq_one :
    IsProP 2 (TameSpec.tameOfSpec 1 2 (lSqW 0) tameSpecializes_lSq).toMonoidHom.ker :=
  Count.hwild_lSq (h := 0) (q := 2) tameSpecializes_lSq

end GQ2.Dyadic.QTwo
