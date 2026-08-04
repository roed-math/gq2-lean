/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.GammaRHom
import GQ2.Dyadic.Count.H2MaxProTwoTransport

/-!
# When an open subgroup has the same maximal pro-2 quotient

Odd index makes the map from the maximal pro-`2` quotient of an open subgroup onto every
ambient pro-`2` quotient surjective.  It does **not** make that map injective.  This file records
the exact missing condition: the subgroup must acquire no new pro-`2` kernel.

This is the group-theoretic boundary a Reidemeister--Schreier argument for a Sylow preimage has
to cross.  It is sharper than postulating an isomorphism with the ambient improved core, and it
keeps the subgroup-dependent information visible.
-/

namespace GQ2

noncomputable section

open GQ2.ContCoh

/-! ## The universal kernel criterion -/

/-- A map from `G(p)` induced by `f : G → P` is injective exactly when `f` kills no more than
the pro-`p` kernel of `G`.

Together with `maxProPHomEquiv`, this is the precise uniqueness statement behind any proposed
identification of a maximal pro-`p` quotient with a concrete pro-`p` target. -/
theorem maxProPFactor_injective_iff_ker
    {p : ℕ} {G P : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (f : ContinuousMonoidHom G P) :
    Function.Injective ((maxProPHomEquiv hP).symm f) ↔
      f.toMonoidHom.ker = proPKernel p G := by
  constructor
  · intro hinj
    apply le_antisymm
    · intro g hg
      have hfac : ((maxProPHomEquiv hP).symm f) (maxProPMk p G g) = 1 := by
        calc
          ((maxProPHomEquiv hP).symm f) (maxProPMk p G g) = f g :=
            DFunLike.congr_fun ((maxProPHomEquiv hP).apply_symm_apply f) g
          _ = 1 := MonoidHom.mem_ker.mp hg
      have hmk : maxProPMk p G g = 1 := hinj (hfac.trans (map_one _).symm)
      exact (quotientMk_eq_one_iff (proPKernel p G)).mp hmk
    · exact proPKernel_le_ker hP f
  · intro hker x y hxy
    obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel p G) x
    obtain ⟨k, rfl⟩ := quotientMk_surjective (proPKernel p G) y
    have hfk : f g = f k := by
      calc
        f g = ((maxProPHomEquiv hP).symm f) (maxProPMk p G g) :=
          (DFunLike.congr_fun ((maxProPHomEquiv hP).apply_symm_apply f) g).symm
        _ = ((maxProPHomEquiv hP).symm f) (maxProPMk p G k) := hxy
        _ = f k := DFunLike.congr_fun ((maxProPHomEquiv hP).apply_symm_apply f) k
    have hgk : g / k ∈ f.toMonoidHom.ker := by
      rw [MonoidHom.mem_ker, map_div]
      exact div_eq_one.mpr hfk
    apply div_eq_one.mp
    calc
      maxProPMk p G g / maxProPMk p G k = maxProPMk p G (g / k) :=
        (map_div (maxProPMk p G) g k).symm
      _ = 1 := (quotientMk_eq_one_iff (proPKernel p G)).mpr (hker ▸ hgk)

/-! ## Open-subgroup specialization -/

section Subgroup

variable {p : ℕ} {G P : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [TotallyDisconnectedSpace G]
  [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- For a subgroup `U`, the induced map `U(p) → P` is injective exactly when the pro-`p`
kernel intrinsic to `U` is the pullback of the kernel of the chosen ambient quotient.

For a genuine maximal pro-`p` ambient quotient (`ker f = K_p(G)`), the right side becomes
`K_p(U) = U ∩ K_p(G)`.  Failure of that equality is exactly the extra
Reidemeister--Schreier kernel which a presentation argument must control. -/
theorem subgroupMaxProPFactor_injective_iff
    (U : Subgroup G) [CompactSpace U]
    (hP : IsProP p P) (f : ContinuousMonoidHom G P) :
    Function.Injective
        ((maxProPHomEquiv hP).symm (f.comp (subgroupIncl G U))) ↔
      proPKernel p U =
        Subgroup.comap (subgroupIncl G U).toMonoidHom f.toMonoidHom.ker := by
  rw [maxProPFactor_injective_iff_ker]
  rw [show (f.comp (subgroupIncl G U)).toMonoidHom.ker =
      Subgroup.comap (subgroupIncl G U).toMonoidHom f.toMonoidHom.ker by
        exact MonoidHom.comap_ker f.toMonoidHom (subgroupIncl G U).toMonoidHom]
  exact eq_comm

/-- The criterion in its ambient-maximal-quotient form. -/
theorem subgroupMaxProPFactor_injective_iff_proPKernel
    (U : Subgroup G) [CompactSpace U]
    (hP : IsProP p P) (f : ContinuousMonoidHom G P)
    (hf : f.toMonoidHom.ker = proPKernel p G) :
    Function.Injective
        ((maxProPHomEquiv hP).symm (f.comp (subgroupIncl G U))) ↔
      proPKernel p U =
        Subgroup.comap (subgroupIncl G U).toMonoidHom (proPKernel p G) := by
  rw [subgroupMaxProPFactor_injective_iff U hP f, hf]

end Subgroup

end

end GQ2
