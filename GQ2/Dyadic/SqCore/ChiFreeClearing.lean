/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.SqCore.EichlerReduction

/-!
# P2′ — the χ-free clearing stratum: what the pro-2 realization actually consumes

**Lane SQ, the P2 residue, corrected interface** (the route-adjudication finding).  The
downstream consumer of the `L_sq` marked-core certificate is
`MarkedCoreRealization (DSq h) (lNu h)` (`GQ2/Dyadic/LabuteInterface.lean`), whose two fields
mention only the equivalence and the full `ν`-matching; its four exported theorems
(`pro2`/`pro2_surjective`/`ker_pro2`/`nu_compat`) feed the `KExactSupplyRN` pro-2 block
(`GQ2/Dyadic/Instances/KAnalytic.lean`) and the L-row arithmetic input
(`GammaLCorrectedArithmeticInput`, `CertificateSupplyRN.ofL`) — and **no χ-clause survives**
anywhere on that path.  The certificate's χ-fields (`orientation`, `correction_chi`) are
consumed by nothing the campaign still needs from this lane; the K-facing bypass is
`GQ2/Dyadic/Instances/GammaLSylowPreimageRealizationBypass.lean`.

Three consequences, adjudicated:

1. **The handle rows must still be cleared.**  `nu_equiv` evaluated at a handle letter *is*
   the normalization `ν'(e(u_j)) = 0`, so the strong bypass ("never normalize handle rows")
   is unavailable; and the proven intra-handle transvections alone cannot do it — `τ`-moves
   act by `SL₂(ℤ₂)` on each handle plane, which preserves the ideal
   `(ν'(u_j), ν'(v_j)) ⊆ ℤ₂` and hence never reaches `(0,0)` from a unit row.
2. **The χ-preservation half of the stratum dissolves.**  Both walls of
   `HandleMixFixesCore.lean` and the ansatz-pinning of the weight-4 seed obstruction (HEAD
   36e75fb0's search report) live in the χ-clause:
   * wall 2 (no χ-trivial core letter, `sqCore_no_clearBlind_letter`) forced the pivot to the
     non-isotropic combination `w = σ·x₀^{−c}` (`⟨w̄,w̄⟩ = −2c ≠ 0`), the source of the
     quadratic term absent from every `M`/`N` case;
   * the seed's χ/ν fields pinned the machine-search ansatz to `v̄`-classes times
     derived-subgroup corrections, inside which the four-slot lift solves at class 3 and is
     obstructed at weight 4 (first-order effect span 146/175).
   Dropping χ widens the ansatz in two independent directions: the pivot may be the *letter*
   `σ` — whose `ν`-row is `1` **by the P3 selection** (`SqMarkedForwardSupply`), so the
   exponent parameter `c` dissolves from the interface — and the slot corrections may carry
   `x̄₀`/`x̄₁`-classes (invisible to every marking with the two pinned core rows), not only
   `v̄`-classes.  The §2 refutation of `HandleMixFixesCore.lean` does **not** apply here: its
   witness has `ν'(σ) = c₀ ≠ 1`, and its contradiction consumes the χ-clause essentially
   (`χ_sq(Ψ⁻¹u₀) = 1` comes from `correction_chi`).
3. **The CoV route is adjudicated against, χ-free or not.**  The naive-Labute refutation
   ("the pivot `b` has `χ = X⁻¹ ≠ 1`") is *moot* under the bypass — χ-triviality of the
   pivot was only ever a certificate-side constraint — but the basis-independent walls of
   `docs/dyadic/eichler-reduction-note.md` (every letter-degree even in every basis; syllable
   counts of the reduced core against HM2's exactly-2 requirement) block the
   `W·[y,z]·∏[u,v]`-shape in every basis, so the proven `M`/`N` Proposition cannot be
   transported by any change of variables.  What the CoV recommendation was reaching for is
   exactly the widened seed search that §4's `SqNuSeed` now poses.

## Contents

* **§1** `SqNuClearHypothesis` — the χ-free clearing target (a `def`, never an axiom), with
  the pricing adapters from the χ-preserving strata (`sqNuClearHypothesis_of_fixesCore`,
  `sqNuClearHypothesis_of_eichler`) and the `h = 0` theorem;
* **§2** `SqNuMoveAt` — the per-handle χ-free move at the σ-pivot; the parameter calculus
  (`zero`/`add`/unit slice) and the adapter from the χ-Eichler move;
* **§3** the clearing recipe: §4-of-`HandleMixFixesCore` τ-normalisation plus the moves,
  `sq_nu_clear_one_handle` → `sq_nu_clear_upto` → `sqNuClearHypothesis_of_moves`;
* **§4** `SqNuSeed` — the corrected residual obligation: `SqEichlerSeed` minus its four
  χ-fields, with the ν-fields' hypothesis widened by the two pinned core rows and `nu_rho`'s
  target the bare parameter `k` (σ-pivot; no `c`); `sqNuMoveAt_of_seed`, the forgetful map
  `SqNuSeed.ofEichlerSeed`, and the assemblies `sqNuClearHypothesis_of_seeds` /
  `sqNuClearHypothesis_of_unit_seeds`;
* **§5** stress pins, **§6** committed axiom prints.

## Axiom hygiene

Every declaration prints **std-3** (`propext`, `Classical.choice`, `Quot.sound`); no census
axiom is reachable (the file consumes only `EichlerReduction`'s scaffold, the τ-machinery of
`HandleMixFixesCore`, and the h-generic `ν_sq` layer).  Census unchanged at **11**.
-/

open Multiplicative

namespace GQ2

open Roe

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The χ-free clearing target

The exact statement the realization bypass consumes: a marking with the two P3-selected core
rows admits a correcting automorphism onto `ν_sq` — with **no** χ-clause on the correction,
and no pivot-exponent parameter. -/

section Target

/-- **The χ-free clearing hypothesis** (a `def`, never an axiom): every continuous marking of
`D_sq` carrying the two P3-selected core rows `ν'(σ) = 1`, `ν'(x₀) = 0` is corrected onto the
standard marking by *some* continuous automorphism.  This is `SqHandleMixFixesCore`'s outcome
with the χ-preservation clause deleted and the pivot-row hypothesis specialized to the exact
selected rows — precisely what `MarkedCoreRealization (DSq h) (lNu h)` consumes and nothing
more. -/
def SqNuClearHypothesis (h : ℕ) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type), ∀ x, nu' (Ψ x) = nuSq h x

/-- **Pricing**: the χ-preserving one-binder stratum implies the χ-free target, at every
exponent.  Nothing is lost by retargeting the lane here. -/
theorem sqNuClearHypothesis_of_fixesCore {h : ℕ} {c : ℤ_[2]}
    (H : SqHandleMixFixesCore h c) : SqNuClearHypothesis h := by
  intro nu' hsigma hx0
  obtain ⟨u, _, hu⟩ := sqMarkedMatching_of_fixesCore H nu' hsigma hx0
  exact ⟨u, hu⟩

/-- At `h = 0` the χ-free target is a theorem (no handle plane to clear). -/
theorem sqNuClearHypothesis_zero : SqNuClearHypothesis 0 :=
  sqNuClearHypothesis_of_fixesCore (sqHandleMixFixesCore_zero 0)

/-- Pricing from the χ-preserving Eichler family. -/
theorem sqNuClearHypothesis_of_eichler {h : ℕ} {c : ℤ_[2]} (hE : SqHandleEichler h c) :
    SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_fixesCore (sqHandleMixFixesCore_of_eichler hE)

end Target

/-! ## §2 The χ-free per-handle move, and the parameter calculus

The σ-pivot: at the selected rows `ν'(σ) = 1`, `ν'(x₀) = 0` the old pivot row is
`ν'(w) = ν'(σ) − c·ν'(x₀) = 1` for *every* exponent `c`, so the shift `k·ν'(w)` collapses to
the bare parameter `k` and the exponent leaves the interface. -/

section Moves

/-- **The χ-free clearing move at `(j, k)`**: for every marking with the two selected core
rows and vanishing `v_j`-row, a continuous automorphism shifting the `u_j`-row by exactly `k`,
fixing the two core rows and every other handle row.  No χ-clause, no pivot exponent. -/
def SqNuMoveAt (h : ℕ) (j : Fin h) (k : ℤ_[2]) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
    nu' (sqGen h (sqHandleIdxV j)) = 1 →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
          ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
          ∧ toAdd (nu' (Ψ (sqGen h (sqHandleIdxU j))))
              = toAdd (nu' (sqGen h (sqHandleIdxU j))) + k
          ∧ (∀ i : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV i)))
              = nu' (sqGen h (sqHandleIdxV i)))
          ∧ (∀ i : Fin h, i ≠ j → nu' (Ψ (sqGen h (sqHandleIdxU i)))
              = nu' (sqGen h (sqHandleIdxU i)))

/-- **The χ-Eichler move implies the χ-free move**, at every exponent: at the selected rows
the pivot row is `1`, so the parameters agree on the nose and the χ-clause is forgotten. -/
theorem sqNuMoveAt_of_eichlerMoveAt {h : ℕ} {c : ℤ_[2]} {j : Fin h} {k : ℤ_[2]}
    (H : SqEichlerMoveAt h c j k) : SqNuMoveAt h j k := by
  intro nu' hsigma hx0 hv
  obtain ⟨Ψ, _, hs, hx, hu, hV, hU⟩ := H nu' hv
  have hpiv : toAdd (nu' (sqMixPivotElem h c)) = 1 := by
    rw [toAdd_nu_sqMixPivotElem nu' c, hsigma, hx0, toAdd_ofAdd, toAdd_ofAdd, mul_zero,
      sub_zero]
  refine ⟨Ψ, hs, hx, ?_, hV, hU⟩
  rw [hu, hpiv, mul_one]

/-- At parameter `0` the identity is a χ-free move. -/
theorem sqNuMoveAt_zero (h : ℕ) (j : Fin h) : SqNuMoveAt h j 0 := by
  intro nu' _ _ _
  refine ⟨ContinuousMulEquiv.refl _, rfl, rfl, ?_, fun _ => rfl, fun _ _ => rfl⟩
  rw [add_zero]
  rfl

/-- **The composition law**: χ-free moves at the same handle add in the parameter.  Each move
preserves the two selected core rows and every `v`-row, so all three hypotheses transport. -/
theorem sqNuMoveAt_add {h : ℕ} {j : Fin h} {k₁ k₂ : ℤ_[2]}
    (H₁ : SqNuMoveAt h j k₁) (H₂ : SqNuMoveAt h j k₂) : SqNuMoveAt h j (k₁ + k₂) := by
  intro nu' hsigma hx0 hv
  obtain ⟨Ψ₁, hs₁, hx₁, hu₁, hV₁, hU₁⟩ := H₁ nu' hsigma hx0 hv
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₁) with hmudef
  have hmusigma : mu (dsqSigma h) = ofAdd (1 : ℤ_[2]) := by
    show nu' (Ψ₁ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
    rw [hs₁, hsigma]
  have hmux : mu (dsqX0 h) = ofAdd (0 : ℤ_[2]) := by
    show nu' (Ψ₁ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
    rw [hx₁, hx0]
  have hmuv : mu (sqGen h (sqHandleIdxV j)) = 1 := by
    show nu' (Ψ₁ (sqGen h (sqHandleIdxV j))) = 1
    rw [hV₁ j, hv]
  obtain ⟨Ψ₂, hs₂, hx₂, hu₂, hV₂, hU₂⟩ := H₂ mu hmusigma hmux hmuv
  refine ⟨Ψ₂.trans Ψ₁, ?_, ?_, ?_, ?_, ?_⟩
  · show mu (Ψ₂ (dsqSigma h)) = nu' (dsqSigma h)
    rw [hs₂]
    exact hs₁
  · show mu (Ψ₂ (dsqX0 h)) = nu' (dsqX0 h)
    rw [hx₂]
    exact hx₁
  · show toAdd (mu (Ψ₂ (sqGen h (sqHandleIdxU j))))
      = toAdd (nu' (sqGen h (sqHandleIdxU j))) + (k₁ + k₂)
    rw [hu₂,
      show toAdd (mu (sqGen h (sqHandleIdxU j)))
        = toAdd (nu' (Ψ₁ (sqGen h (sqHandleIdxU j)))) from rfl, hu₁]
    ring
  · intro i
    show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))
    rw [hV₂ i]
    exact hV₁ i
  · intro i hi
    show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
    rw [hU₂ i hi]
    exact hU₁ i hi

/-- **The parameter reduction**: χ-free moves on the unit slice generate every parameter. -/
theorem sqNuMoveAt_of_units {h : ℕ} {j : Fin h}
    (H : ∀ k : ℤ_[2], IsUnit k → SqNuMoveAt h j k) (k : ℤ_[2]) : SqNuMoveAt h j k := by
  by_cases hk : IsUnit k
  · exact H k hk
  · by_cases hk0 : k = 0
    · rw [hk0]
      exact sqNuMoveAt_zero h j
    · have hsum := sqNuMoveAt_add (H 1 isUnit_one)
        (H (k - 1) (isUnit_sub_one_of_not_isUnit hk))
      have hrw : 1 + (k - 1) = k := by ring
      rwa [hrw] at hsum

end Moves

/-! ## §3 The clearing recipe

τ-normalisation of one handle plane (`sq_normalize_handle`, χ-preserving and core-fixing, so
it transports every hypothesis) followed by one χ-free move; then the induction over
handles. -/

section Clearing

/-- **One handle, cleared χ-free**: normalise the plane with the τ-moves, then spend one
χ-free move at parameter `−ν'(u_j)`.  The two selected core rows survive and no other handle
is touched. -/
theorem sq_nu_clear_one_handle {h : ℕ} {j : Fin h} (hmv : ∀ k : ℤ_[2], SqNuMoveAt h j k)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
        ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
        ∧ nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1
        ∧ nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1
        ∧ (∀ i : Fin h, i ≠ j →
            nu' (Ψ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
            ∧ nu' (Ψ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))) := by
  obtain ⟨Ψ₁, hloc, hv₁⟩ := sq_normalize_handle h j nu'
  set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψ₁) with hmudef
  have hmusigma : mu (dsqSigma h) = ofAdd (1 : ℤ_[2]) := by
    show nu' (Ψ₁ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
    rw [hloc.2.1, hsigma]
  have hmux : mu (dsqX0 h) = ofAdd (0 : ℤ_[2]) := by
    show nu' (Ψ₁ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
    rw [hloc.2.2.1, hx0]
  obtain ⟨Ψ₂, hs₂, hx₂, hu₂, hV₂, hU₂⟩ :=
    hmv (-(toAdd (mu (sqGen h (sqHandleIdxU j))))) mu hmusigma hmux hv₁
  refine ⟨Ψ₂.trans Ψ₁, ?_, ?_, ?_, ?_, ?_⟩
  · show mu (Ψ₂ (dsqSigma h)) = nu' (dsqSigma h)
    rw [hs₂]
    show nu' (Ψ₁ (dsqSigma h)) = _
    rw [hloc.2.1]
  · show mu (Ψ₂ (dsqX0 h)) = nu' (dsqX0 h)
    rw [hx₂]
    show nu' (Ψ₁ (dsqX0 h)) = _
    rw [hloc.2.2.1]
  · show mu (Ψ₂ (sqGen h (sqHandleIdxU j))) = 1
    refine Multiplicative.toAdd.injective ?_
    rw [hu₂, toAdd_one]
    ring
  · show mu (Ψ₂ (sqGen h (sqHandleIdxV j))) = 1
    rw [hV₂ j]
    exact hv₁
  · intro i hi
    refine ⟨?_, ?_⟩
    · show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
      rw [hU₂ i hi]
      show nu' (Ψ₁ (sqGen h (sqHandleIdxU i))) = _
      rw [hloc.2.2.2.1 i hi]
    · show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))
      rw [hV₂ i]
      show nu' (Ψ₁ (sqGen h (sqHandleIdxV i))) = _
      rw [hloc.2.2.2.2 i hi]

/-- The χ-free clearing recipe, run over the handles of index `< n`. -/
theorem sq_nu_clear_upto {h : ℕ} (hmv : ∀ (j : Fin h) (k : ℤ_[2]), SqNuMoveAt h j k) :
    ∀ (n : ℕ) (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        nu' (Ψ (dsqSigma h)) = nu' (dsqSigma h)
          ∧ nu' (Ψ (dsqX0 h)) = nu' (dsqX0 h)
          ∧ (∀ i : Fin h, (i : ℕ) < n → nu' (Ψ (sqGen h (sqHandleIdxU i))) = 1
              ∧ nu' (Ψ (sqGen h (sqHandleIdxV i))) = 1)
          ∧ (∀ i : Fin h, n ≤ (i : ℕ) →
              nu' (Ψ (sqGen h (sqHandleIdxU i))) = nu' (sqGen h (sqHandleIdxU i))
              ∧ nu' (Ψ (sqGen h (sqHandleIdxV i))) = nu' (sqGen h (sqHandleIdxV i))) := by
  intro n
  induction n with
  | zero =>
    intro nu' _ _
    exact ⟨ContinuousMulEquiv.refl _, rfl, rfl, fun i hi => absurd hi (by omega),
      fun i _ => ⟨rfl, rfl⟩⟩
  | succ n ih =>
    intro nu' hsigma hx0
    obtain ⟨Ψ₁, hs₁, hx₁, hclr₁, hfix₁⟩ := ih nu' hsigma hx0
    by_cases hn : n < h
    · set j : Fin h := ⟨n, hn⟩ with hjdef
      set mu : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
        nu'.comp (autHom Ψ₁) with hmudef
      have hmusigma : mu (dsqSigma h) = ofAdd (1 : ℤ_[2]) := by
        show nu' (Ψ₁ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
        rw [hs₁, hsigma]
      have hmux : mu (dsqX0 h) = ofAdd (0 : ℤ_[2]) := by
        show nu' (Ψ₁ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
        rw [hx₁, hx0]
      obtain ⟨Ψ₂, hs₂, hx₂, hu₂, hv₂, hother₂⟩ :=
        sq_nu_clear_one_handle (hmv j) mu hmusigma hmux
      have hne : ∀ i : Fin h, (i : ℕ) ≠ n → i ≠ j := by
        intro i hi hc
        exact hi (by rw [hc, hjdef])
      refine ⟨Ψ₂.trans Ψ₁, ?_, ?_, ?_, ?_⟩
      · show mu (Ψ₂ (dsqSigma h)) = nu' (dsqSigma h)
        rw [hs₂]
        exact hs₁
      · show mu (Ψ₂ (dsqX0 h)) = nu' (dsqX0 h)
        rw [hx₂]
        exact hx₁
      · intro i hi
        by_cases hij : (i : ℕ) = n
        · have hieq : i = j := by
            rw [hjdef]
            exact Fin.ext hij
          subst hieq
          exact ⟨hu₂, hv₂⟩
        · obtain ⟨hUi, hVi⟩ := hother₂ i (hne i hij)
          refine ⟨?_, ?_⟩
          · show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = 1
            rw [hUi]
            exact (hclr₁ i (by omega)).1
          · show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = 1
            rw [hVi]
            exact (hclr₁ i (by omega)).2
      · intro i hi
        obtain ⟨hUi, hVi⟩ := hother₂ i (hne i (by omega))
        refine ⟨?_, ?_⟩
        · show mu (Ψ₂ (sqGen h (sqHandleIdxU i))) = _
          rw [hUi]
          exact (hfix₁ i (by omega)).1
        · show mu (Ψ₂ (sqGen h (sqHandleIdxV i))) = _
          rw [hVi]
          exact (hfix₁ i (by omega)).2
    · refine ⟨Ψ₁, hs₁, hx₁, fun i hi => hclr₁ i ?_, fun i hi => hfix₁ i (by omega)⟩
      have := i.isLt
      omega

/-- **The χ-free reduction**: the per-handle χ-free moves discharge the whole clearing
target.  Closes with the §2 recognition lemma of `SqCore/Certificate.lean`, whose `x₁`-row is
the forced row. -/
theorem sqNuClearHypothesis_of_moves {h : ℕ}
    (hmv : ∀ (j : Fin h) (k : ℤ_[2]), SqNuMoveAt h j k) : SqNuClearHypothesis h := by
  intro nu' hsigma hx0
  obtain ⟨Ψ, hs, hx, hclr, _⟩ := sq_nu_clear_upto hmv h nu' hsigma hx0
  refine ⟨Ψ, ?_⟩
  have hcore : ∀ x, (nu'.comp (autHom Ψ)) x = nuSq h x := by
    refine nu_eq_nuSq_of_core _ ?_ ?_ (fun j => (hclr j j.isLt).1) (fun j => (hclr j j.isLt).2)
    · show nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2])
      rw [hs, hsigma]
    · show nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2])
      rw [hx, hx0]
  exact fun x => hcore x

/-- The reduction from the unit slice alone. -/
theorem sqNuClearHypothesis_of_unit_moves {h : ℕ}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → SqNuMoveAt h j k) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_moves fun j k => sqNuMoveAt_of_units (H j) k

end Clearing

/-! ## §4 The corrected residual: the χ-free seed

`SqEichlerSeed` minus its four χ-fields, with the three ν-fields' hypothesis widened by the
two selected core rows and the `u_j`-shift targeted at the bare parameter (σ-pivot).  The
widening is the point: the correction words may now carry `σ̄`-, `x̄₀`- and `x̄₁`-classes —
`ν'(x₀) = 0` and the forced row `ν'(x₁) = 2ν'(x₀)` make `x̄₀`/`x̄₁`-classes invisible, and the
`u_j`-shift word may be built directly on the letter `σ` — so the search ansatz is strictly
wider than the `v̄`-classes-only ansatz in which the weight-4 obstruction was found. -/

section Seed

variable {h : ℕ}

/-- **The χ-free Eichler seed at `(h, j, k)`** — the corrected residual word-level input, as
data.  The four substitution slots and the four structural fields are exactly
`SqEichlerSeed`'s; the four χ-fields are deleted (the realization consumes no χ-clause), the
ν-fields' hypothesis is widened by the two selected core rows, and `nu_rho`'s target is the
bare parameter `k`. -/
structure SqNuSeed (h : ℕ) (j : Fin h) (k : ℤ_[2]) where
  /-- The σ-slot correction word. -/
  beta1 : (DSq h : Type)
  /-- The `x₀`-slot correction word. -/
  beta0 : (DSq h : Type)
  /-- The `x₁`-slot correction word. -/
  beta2 : (DSq h : Type)
  /-- The `u_j`-slot shift word (of class `k·σ̄` up to ν'-invisible classes). -/
  rho : (DSq h : Type)
  /-- The σ-slot word of the inverse substitution. -/
  beta1Inv : (DSq h : Type)
  /-- The `x₀`-slot word of the inverse substitution. -/
  beta0Inv : (DSq h : Type)
  /-- The `x₁`-slot word of the inverse substitution. -/
  beta2Inv : (DSq h : Type)
  /-- The `u_j`-slot word of the inverse substitution. -/
  rhoInv : (DSq h : Type)
  /-- The forward substitution kills the relator. -/
  rel_fwd : sqRelWord (sqEichlerSub h j beta1 beta0 beta2 rho) = 1
  /-- The backward substitution kills the relator. -/
  rel_bwd : sqRelWord (sqEichlerSub h j beta1Inv beta0Inv beta2Inv rhoInv) = 1
  /-- Forward after backward is the identity on generators. -/
  comp_fwd : ∀ i, sqLiftHom h (isProP_DSq h) (sqEichlerSub h j beta1 beta0 beta2 rho) rel_fwd
      (sqEichlerSub h j beta1Inv beta0Inv beta2Inv rhoInv i) = sqGen h i
  /-- Backward after forward is the identity on generators. -/
  comp_bwd : ∀ i, sqLiftHom h (isProP_DSq h)
      (sqEichlerSub h j beta1Inv beta0Inv beta2Inv rhoInv) rel_bwd
      (sqEichlerSub h j beta1 beta0 beta2 rho i) = sqGen h i
  /-- The σ-correction is invisible to every marking with the selected rows and vanishing
  `v_j`-row. -/
  nu_beta1 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' beta1 = 1
  /-- The `x₀`-correction is invisible to every such marking. -/
  nu_beta0 : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → nu' beta0 = 1
  /-- The `u_j`-shift has row exactly `k` against every such marking (the σ-pivot). -/
  nu_rho : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        nu' (sqGen h (sqHandleIdxV j)) = 1 → toAdd (nu' rho) = k

variable {j : Fin h} {k : ℤ_[2]}

/-- The forward substitution of a χ-free seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqNuSeed.hom (S : SqNuSeed h j k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqEichlerSub h j S.beta1 S.beta0 S.beta2 S.rho) S.rel_fwd

/-- The backward substitution of a χ-free seed, as a continuous endomorphism of `D_sq`. -/
noncomputable def SqNuSeed.homInv (S : SqNuSeed h j k) :
    ContinuousMonoidHom (DSq h : Type) (DSq h : Type) :=
  sqLiftHom h (isProP_DSq h) (sqEichlerSub h j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv)
    S.rel_bwd

@[simp] theorem SqNuSeed.hom_gen (S : SqNuSeed h j k) (i : Fin (sqRank h)) :
    S.hom (sqGen h i) = sqEichlerSub h j S.beta1 S.beta0 S.beta2 S.rho i :=
  sqLiftHom_gen _ _ _ _ _

@[simp] theorem SqNuSeed.homInv_gen (S : SqNuSeed h j k) (i : Fin (sqRank h)) :
    S.homInv (sqGen h i) = sqEichlerSub h j S.beta1Inv S.beta0Inv S.beta2Inv S.rhoInv i :=
  sqLiftHom_gen _ _ _ _ _

/-- **The χ-free seed's automorphism.** -/
noncomputable def SqNuSeed.equiv (S : SqNuSeed h j k) :
    ContinuousMulEquiv (DSq h : Type) (DSq h : Type) :=
  continuousMulEquivOfBijective S.hom (Function.bijective_iff_has_inverse.mpr
    ⟨S.homInv,
      dsq_leftInverse S.homInv S.hom fun i => by rw [S.hom_gen]; exact S.comp_bwd i,
      dsq_leftInverse S.hom S.homInv fun i => by rw [S.homInv_gen]; exact S.comp_fwd i⟩)

@[simp] theorem SqNuSeed.equiv_gen (S : SqNuSeed h j k) (i : Fin (sqRank h)) :
    S.equiv (sqGen h i) = sqEichlerSub h j S.beta1 S.beta0 S.beta2 S.rho i :=
  S.hom_gen i

/-- **Seed to move**: a χ-free seed at `(h, j, k)` realizes the χ-free `(j, k)`-move. -/
theorem sqNuMoveAt_of_seed (S : SqNuSeed h j k) : SqNuMoveAt h j k := by
  intro nu' hsigma hx0 hv
  refine ⟨S.equiv, ?_, ?_, ?_, ?_, ?_⟩
  · show nu' (S.equiv (sqGen h 0)) = nu' (dsqSigma h)
    rw [S.equiv_gen, sqEichlerSub_zero, map_mul, S.nu_beta1 nu' hsigma hx0 hv, mul_one]
  · show nu' (S.equiv (sqGen h 1)) = nu' (dsqX0 h)
    rw [S.equiv_gen, sqEichlerSub_one, map_mul, S.nu_beta0 nu' hsigma hx0 hv, mul_one]
  · rw [S.equiv_gen, sqEichlerSub_handleU_self, map_mul, toAdd_mul,
      S.nu_rho nu' hsigma hx0 hv]
    ring
  · intro i
    rw [S.equiv_gen, sqEichlerSub_handleV]
  · intro i hi
    rw [S.equiv_gen, sqEichlerSub_handleU_of_ne j S.beta1 S.beta0 S.beta2 S.rho hi]

/-- **The forgetful map**: a χ-preserving Eichler seed is a χ-free seed — the four χ-fields
are dropped, the ν-fields forget the two extra hypotheses, and the σ-pivot parameter is the
old one because the selected rows make the pivot row `1`. -/
noncomputable def SqNuSeed.ofEichlerSeed {c : ℤ_[2]} (S : SqEichlerSeed h c j k) :
    SqNuSeed h j k where
  beta1 := S.beta1
  beta0 := S.beta0
  beta2 := S.beta2
  rho := S.rho
  beta1Inv := S.beta1Inv
  beta0Inv := S.beta0Inv
  beta2Inv := S.beta2Inv
  rhoInv := S.rhoInv
  rel_fwd := S.rel_fwd
  rel_bwd := S.rel_bwd
  comp_fwd := S.comp_fwd
  comp_bwd := S.comp_bwd
  nu_beta1 := fun nu' _ _ hv => S.nu_beta1 nu' hv
  nu_beta0 := fun nu' _ _ hv => S.nu_beta0 nu' hv
  nu_rho := fun nu' hsigma hx0 hv => by
    have hpiv : toAdd (nu' (sqMixPivotElem h c)) = 1 := by
      rw [toAdd_nu_sqMixPivotElem nu' c, hsigma, hx0, toAdd_ofAdd, toAdd_ofAdd, mul_zero,
        sub_zero]
    rw [S.nu_rho nu' hv, hpiv, mul_one]

/-- **The assembly**: χ-free seeds at every parameter discharge the clearing target. -/
theorem sqNuClearHypothesis_of_seeds {h : ℕ}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), Nonempty (SqNuSeed h j k)) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_moves fun j k => (H j k).elim fun S => sqNuMoveAt_of_seed S

/-- The assembly from the unit slice alone. -/
theorem sqNuClearHypothesis_of_unit_seeds {h : ℕ}
    (H : ∀ (j : Fin h) (k : ℤ_[2]), IsUnit k → Nonempty (SqNuSeed h j k)) :
    SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_unit_moves fun j k hk => (H j k hk).elim fun S =>
    sqNuMoveAt_of_seed S

end Seed

/-! ## §5 Stress pins

`h = 1` and `h = 0` per the lane idiom, so a later reshaping cannot silently become
vacuous. -/

section StressTests

/-- At `h = 0` the χ-free target is a theorem. -/
example : SqNuClearHypothesis 0 := sqNuClearHypothesis_zero

/-- The χ-free target at one handle follows from the χ-preserving stratum at any exponent. -/
example {c : ℤ_[2]} (H : SqHandleMixFixesCore 1 c) : SqNuClearHypothesis 1 :=
  sqNuClearHypothesis_of_fixesCore H

/-- The zero-parameter χ-free move at one handle. -/
example : SqNuMoveAt 1 0 0 := sqNuMoveAt_zero 1 0

/-- The parameter decomposition pin: `2 = 1 + 1` chains two unit moves. -/
example (H : SqNuMoveAt 1 0 1) : SqNuMoveAt 1 0 2 := by
  have h2 := sqNuMoveAt_add H H
  norm_num at h2
  exact h2

/-- The χ-Eichler move at the canonical exponent forgets to the χ-free move. -/
example {k : ℤ_[2]} (H : SqEichlerMoveAt 1 sqPivotExp 0 k) : SqNuMoveAt 1 0 k :=
  sqNuMoveAt_of_eichlerMoveAt H

/-- χ-free unit seeds at one handle discharge the clearing target. -/
example (H : ∀ (j : Fin 1) (k : ℤ_[2]), IsUnit k → Nonempty (SqNuSeed 1 j k)) :
    SqNuClearHypothesis 1 :=
  sqNuClearHypothesis_of_unit_seeds H

/-- A χ-preserving seed at the canonical exponent forgets to a χ-free seed. -/
noncomputable example {k : ℤ_[2]} (S : SqEichlerSeed 1 sqPivotExp 0 k) : SqNuSeed 1 0 k :=
  SqNuSeed.ofEichlerSeed S

/-- The scaffold fixes the `v_j`-slot literally — the slot the class-two balance says never
needs to move, χ-free or not. -/
example (β₁ β₀ β₂ ρ : (DSq 1 : Type)) :
    sqEichlerSub 1 0 β₁ β₀ β₂ ρ (sqHandleIdxV 0) = sqGen 1 (sqHandleIdxV 0) :=
  sqEichlerSub_handleV 0 β₁ β₀ β₂ ρ 0

end StressTests

/-! ## §6 Axiom pins

Committed prints for the headline declarations: the whole file is **std-3**, with no census
axiom reachable.  Census unchanged at **11**. -/

section AxiomPins

#print axioms sqNuClearHypothesis_of_fixesCore
#print axioms sqNuClearHypothesis_zero
#print axioms sqNuClearHypothesis_of_eichler
#print axioms sqNuMoveAt_of_eichlerMoveAt
#print axioms sqNuMoveAt_add
#print axioms sq_nu_clear_one_handle
#print axioms sqNuClearHypothesis_of_moves
#print axioms sqNuClearHypothesis_of_unit_moves
#print axioms sqNuMoveAt_of_seed
#print axioms SqNuSeed.ofEichlerSeed
#print axioms sqNuClearHypothesis_of_seeds
#print axioms sqNuClearHypothesis_of_unit_seeds

end AxiomPins

end SqCore

end Dyadic

end GQ2
