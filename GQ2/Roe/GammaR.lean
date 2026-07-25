/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Words
public import GQ2.GammaA

@[expose] public section

/-!
# `Γ_R` and the Roe-candidate marked quotient  (Roe note §1, Definition 1.1 ⟦def:GammaR⟧)

The Roe-candidate group, defined by the **same marked-quotient construction** as `Γ_A`
(`GQ2/GammaA.lean`, paper §2.1 eq. (7)): let `F₄` be the free profinite group on `σ, τ, x₀, x₁`;
call a finite quotient `φ : F₄ ⟶ G` **`R`-admissible** if the pushed marking generates `G`,
satisfies the tame relation `τ^σ = τ²` and the **Roe wild relation** `r_R = 1` (note eq. (1.2)
⟦eq:relators⟧, verbatim `\rR=(x_0^\sigma)^{-1}a\,x_1^2c`), and the normal closure of the images of
`x₀, x₁` is a 2-group; then

  `N_R = ⋂ {ker φ | φ R-admissible}`,   `Γ_R = F₄ ⧸ N_R`.

Only the wild relation differs from `Γ_A`: the tame relation, the pro-2 condition, and the whole
marked-quotient scaffolding (`univMarking`, `Marking.toHom`, `surjective_of_map_generates`) are
reused verbatim from `GQ2/GammaA.lean`.

This file provides the Roe relation `r_R` in its **profinite reading**: the note's auxiliary words
of eq. (1.1) ⟦eq:defwords⟧ with genuine `ω₂ ∈ ℤ̂` exponents (`Marking.aRHat`, `Marking.y1RHat`,
`Marking.cRHat`, `Marking.wildRelatorR`, via `^ᶻ omega2` from `GQ2/Zhat.lean`; the `σ₂ = σ^{ω₂}`
letter reuses the shared `Marking.sigma2Hat` of `Γ_A`).  The **fidelity bridge**
`Marking.map_wildRelatorR` / `Marking.map_wildRelatorR_eq_one_iff` proves that pushing the
profinite word `wildRelatorR` through a finite quotient computes exactly `Marking.wildValueR` of
`GQ2/Roe/Words.lean` — so killing the profinite relator is the same condition as the finite Roe
wild relation `WildRelR`, and the `R`-admissibility used in `N_R` is exactly the note's.

Alongside `Γ_R` this file supplies `Marking.map_admissibleR` (`R`-admissibility pushes forward
along surjective quotient maps — the Roe counterpart of `Marking.map_admissible`,
`GQ2/Subdirect.lean`) and the certificate `NR_le_ker` (every `R`-admissible continuous hom to a
finite group has `N_R` in its kernel).  The limit facts about `Γ_R` itself (relators die,
admissible-opens characterization, pro-2 wild core) are `GQ2/Roe/AdmissibleLimit.lean`.
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

/-! ## The Roe auxiliary words with genuine profinite `ω₂`-exponents (note eq. (1.1)) -/

namespace Marking

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking G)

noncomputable section

/-- `a = (x₀⁻³ τ)^{ω₂}` (note eq. (1.1) ⟦eq:defwords⟧, verbatim `a=(x_0^{-3}\tau)^{\omegaTwo}`),
**profinite reading** with the genuine profinite exponent `ω₂ ∈ ℤ̂`.  The finite counterpart is
`Marking.aR` (`GQ2/Roe/Words.lean`). -/
def aRHat : G := ((t.x₀ ^ 3)⁻¹ * t.τ) ^ᶻ omega2

/-- `y₁ = x₁^{σ₂}` (note eq. (1.1) ⟦eq:defwords⟧, verbatim `y_1=x_1^{\sigma_2}`), **profinite
reading**, reusing the shared `σ₂ = σ^{ω₂} = Marking.sigma2Hat` of `Γ_A`.  Finite counterpart
`Marking.y1R`. -/
def y1RHat : G := conjP t.x₁ t.sigma2Hat

/-- `c = [x₁, y₁]` (note eq. (1.1) ⟦eq:defwords⟧, verbatim `c=[x_1,y_1]`), **profinite reading**.
Finite counterpart `Marking.cR`. -/
def cRHat : G := commP t.x₁ t.y1RHat

/-- The **Roe wild relator word** `r_R = (x₀^σ)⁻¹ · a · x₁² · c` (note eq. (1.2) ⟦eq:relators⟧,
verbatim `\rR=(x_0^\sigma)^{-1}a\,x_1^2c`), in the profinite reading — its `ω₂`-letters (inside
`aRHat` and inside `cRHat`'s `sigma2Hat`) use the genuine profinite exponents above.  The `Γ_A`
analogue is `Marking.wildRelator`; the finite value is `Marking.wildValueR`
(`GQ2/Roe/Words.lean`). -/
def wildRelatorR : G := (conjP t.x₀ t.σ)⁻¹ * t.aRHat * t.x₁ ^ 2 * t.cRHat

end

/-! ### Faithfulness bridge: the profinite Roe word evaluates to the finite Roe word

Through any continuous homomorphism to a finite group, the `^ᶻ omega2`-ledger of `wildRelatorR`
computes the `powOmega2`-ledger `wildValueR` of `GQ2/Roe/Words.lean` — via the profinite-
exponentiation headline `map_zpowHat_omega2`, pushed through the three Roe letters.  In particular
the Roe relation read profinitely (relator dies) and finitely (`WildRelR` of the pushed marking)
are the same condition (`map_wildRelatorR_eq_one_iff`) — the fidelity-critical lemma, exactly
mirroring `GQ2.Marking.map_wildRelator_eq_one_iff`. -/

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
  (f : ContinuousMonoidHom G P) (t : Marking G)

/-- Local copy of `GQ2.Marking.map_sigma2Hat` (private there): through a finite quotient,
`σ₂ = powOmega2 σ` of the pushed marking is the image of the profinite `σ₂ = σ^{ω₂}`. -/
@[simp] private lemma map_sigma2Hat' : (t.map f.toMonoidHom).sigma2 = f.toMonoidHom t.sigma2Hat := by
  simp only [sigma2, map_σ, sigma2Hat]
  exact (map_zpowHat_omega2 f t.σ).symm

@[simp] private lemma map_aRHat : (t.map f.toMonoidHom).aR = f.toMonoidHom t.aRHat := by
  simp only [aR, map_x₀, map_τ, ← map_pow, ← map_inv, ← map_mul, aRHat]
  exact (map_zpowHat_omega2 f _).symm

@[simp] private lemma map_y1RHat : (t.map f.toMonoidHom).y1R = f.toMonoidHom t.y1RHat := by
  simp only [y1R, map_x₁, map_sigma2Hat', y1RHat, map_conjP]

@[simp] private lemma map_cRHat : (t.map f.toMonoidHom).cR = f.toMonoidHom t.cRHat := by
  simp only [cR, map_x₁, map_y1RHat, cRHat, map_commP]

/-- **Word-for-word fidelity**: the profinite Roe wild relator evaluates, through any finite
quotient, to the finite Roe wild relator value `Marking.wildValueR` of the pushed marking — the
content underlying `map_wildRelatorR_eq_one_iff`.  (The `Γ_A` monolithic analogue is folded into
`GQ2.Marking.map_wildRelator_eq_one_iff`; here it is exposed separately as a stress test.) -/
lemma map_wildRelatorR :
    f.toMonoidHom t.wildRelatorR = (t.map f.toMonoidHom).wildValueR := by
  simp only [wildValueR, wildRelatorR, map_mul, map_inv, map_pow, map_conjP,
    map_aRHat, map_cRHat, map_x₀, map_x₁, map_σ]

/-- **Roe relation `r_R`, profinite = finite**: the Roe wild relator word dies in a finite
quotient iff the pushed marking satisfies the Roe wild relation `WildRelR` of
`GQ2/Roe/Words.lean`.  Direct analogue of `GQ2.Marking.map_wildRelator_eq_one_iff`. -/
lemma map_wildRelatorR_eq_one_iff :
    f.toMonoidHom t.wildRelatorR = 1 ↔ (t.map f.toMonoidHom).WildRelR := by
  rw [map_wildRelatorR]
  exact (t.map f.toMonoidHom).wildValueR_eq_one_iff

end Bridge

/-! ### `R`-admissibility pushes forward (Roe counterpart of `Marking.map_admissible`) -/

section MapAdmissible

variable {G H : Type*} [Group G] [Group H]

/-- **`R`-admissibility pushes forward along surjective quotient maps** (Roe counterpart of
`GQ2.Marking.map_admissible`, paper §2 Lemmas 2.1–2.2).  If `t` is an `R`-admissible marking of a
finite group `G` and `f : G ↠ H` is a surjective homomorphism of finite groups, then `t.map f` is
`R`-admissible.  Only the wild clause differs from `map_admissible`: `map_wildRelR` (of
`GQ2/Roe/Words.lean`) replaces `map_wildRel`; generation, the tame relation and the 2-core clause
are word-independent (R1 report). -/
theorem map_admissibleR [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (t : Marking G) (ht : t.AdmissibleR) :
    (t.map f).AdmissibleR := by
  obtain ⟨hgen, htame, hwild, hcore⟩ := ht
  refine ⟨?_, map_tameRel f t htame, map_wildRelR f t hwild, ?_⟩
  · -- generation is preserved by surjective images
    rw [Generates] at hgen ⊢
    rw [show ({(t.map f).σ, (t.map f).τ, (t.map f).x₀, (t.map f).x₁} : Set H)
          = f '' {t.σ, t.τ, t.x₀, t.x₁} by simp [map, Set.image_insert_eq, Set.image_singleton],
      ← MonoidHom.map_closure, hgen, Subgroup.map_top_of_surjective f hf]
  · -- the wild generators still have 2-group normal closure
    have himg : Subgroup.normalClosure {(t.map f).x₀, (t.map f).x₁}
        = (Subgroup.normalClosure {t.x₀, t.x₁}).map f := by
      rw [show ({(t.map f).x₀, (t.map f).x₁} : Set H) = f '' {t.x₀, t.x₁} by
            simp [map, Set.image_insert_eq, Set.image_singleton]]
      exact (Subgroup.map_normalClosure {t.x₀, t.x₁} f hf).symm
    rw [Pro2Core] at hcore ⊢
    rw [himg]
    exact hcore.map f

end MapAdmissible

end Marking

/-! ## `N_R` and `Γ_R` (Roe note Definition 1.1 ⟦def:GammaR⟧; same shape as paper §2.1 eq. (7)) -/

/-- An open normal subgroup `U ≤ F₄` is **`R`-admissible** (note Definition 1.1 ⟦def:GammaR⟧) if
the canonical finite quotient `F₄ ⧸ U` carries an `R`-admissible pushed marking: the images of
`σ, τ, x₀, x₁` generate, satisfy the tame relation and the Roe wild relation — equivalently (by
`map_tameRelator_eq_one_iff` / `map_wildRelatorR_eq_one_iff`) the profinite relator words die —
and the normal closure of the images of `x₀, x₁` is a 2-group.  Roe counterpart of
`GQ2.IsAdmissibleU`. -/
def IsAdmissibleUR (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) : Prop :=
  (univMarking.map (QuotientGroup.mk' U.toSubgroup)).AdmissibleR

/-- **`N_R`** (note Definition 1.1 ⟦def:GammaR⟧): the intersection of the kernels of all
`R`-admissible finite quotients of `F₄`, encoded as the intersection of all `R`-admissible open
normal subgroups.  Roe counterpart of `GQ2.NA`. -/
noncomputable def NR : Subgroup (FreeProfiniteGroup (Fin 4)) :=
  ⨅ U : {U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) // IsAdmissibleUR U}, U.1.toSubgroup

instance NR_normal : NR.Normal :=
  Subgroup.normal_iInf_normal fun U => U.1.isNormal'

lemma NR_isClosed : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := by
  unfold NR
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun U => U.1.toOpenSubgroup.isClosed

/-- **`Γ_R`** (note Definition 1.1 ⟦def:GammaR⟧): the marked quotient `F₄ ⧸ N_R` — the largest
quotient of `F₄` all of whose finite quotients are `R`-admissible, constructed exactly as `Γ_A`
but with the Roe wild relation.  Roe counterpart of `GQ2.GammaA`. -/
noncomputable def GammaR : ProfiniteGrp :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  profiniteQuotient NR

/-- **`N_R` is the note's intersection** (Definition 1.1 ⟦def:GammaR⟧): the kernel of *every*
`R`-admissible continuous hom to a finite (discrete) group — not just the canonical quotients
`F₄ ⧸ U` — contains `N_R`.  (The pushed marking being `R`-admissible forces `f` surjective, and
`R`-admissibility transfers to the canonical quotient by the induced isomorphism
`F₄ ⧸ ker f ≃* P`.)  Roe counterpart of `GQ2.NA_le_ker`. -/
theorem NR_le_ker {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
    (f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) P)
    (hf : (univMarking.map f.toMonoidHom).AdmissibleR) :
    NR ≤ f.toMonoidHom.ker := by
  have hsurj : Function.Surjective f := surjective_of_map_generates f.toMonoidHom hf.1
  -- the kernel, as an open normal subgroup
  have hker_open :
      IsOpen ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
        = f ⁻¹' {1} := by
      ext g; simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set P)).preimage f.continuous_toFun
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := f.toMonoidHom.ker, isOpen' := hker_open }
  -- the induced isomorphism with the canonical quotient
  let e : (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) ≃* P :=
    QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hsurj
  have hcomp : ∀ x : FreeProfiniteGroup (Fin 4),
      e.symm (f x) = QuotientGroup.mk' U.toSubgroup x := fun x =>
    e.injective (by rw [MulEquiv.apply_symm_apply]; rfl)
  have hadm : IsAdmissibleUR U := by
    have h1 : univMarking.map (QuotientGroup.mk' U.toSubgroup)
        = (univMarking.map f.toMonoidHom).map e.symm.toMonoidHom := by
      simp only [Marking.map]
      congr 1 <;> exact (hcomp _).symm
    show (univMarking.map (QuotientGroup.mk' U.toSubgroup)).AdmissibleR
    rw [h1]
    haveI : Finite (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) :=
      Finite.of_equiv P e.symm.toEquiv
    exact Marking.map_admissibleR e.symm.toMonoidHom e.symm.surjective _ hf
  exact iInf_le
    (fun V : {V : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) // IsAdmissibleUR V} =>
      V.1.toSubgroup) ⟨U, hadm⟩

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.1) = ⟦eq:defwords⟧
  * eq. (1.2) = ⟦eq:relators⟧
  * Definition 1.1 = ⟦def:GammaR⟧
-/
