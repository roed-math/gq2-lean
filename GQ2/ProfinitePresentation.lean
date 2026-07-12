import GQ2.FreeProfinite
import GQ2.ProfiniteQuotient

/-!
# Profinite presentations

Combining the free profinite group (`GQ2/FreeProfinite.lean`) with the profinite quotient by a
closed normal subgroup (`GQ2/ProfiniteQuotient.lean`), we can form the profinite group **presented**
by a set of generators and relators: the free profinite group modulo the *closed* normal closure of
the relators.  This is the shape of the paper's group `Γ_A` (generators `σ, τ, x₀, x₁`, i.e.
`X = Fin 4`, and the four relators).  Writing the literal relators still needs a genuine profinite
`ω₂`-exponent (`ZHat`, absent from Mathlib — see `docs/foundations-audit.md`), but the presentation
construction itself is now available.
-/

open scoped Pointwise

namespace GQ2

universe u

/-- The **closed normal closure** of a set `rels` in the free profinite group on `X`: the smallest
closed normal subgroup containing the relators.  (Closedness is what makes the quotient profinite;
in a profinite group the *algebraic* normal closure need not be closed.) -/
noncomputable def relatorSubgroup {X : Type u} (rels : Set (FreeProfiniteGroup X)) :
    Subgroup (FreeProfiniteGroup X) :=
  (Subgroup.normalClosure rels).topologicalClosure

instance {X : Type u} (rels : Set (FreeProfiniteGroup X)) : (relatorSubgroup rels).Normal :=
  Subgroup.is_normal_topologicalClosure _

/-- The profinite group **presented** by generators `X` and relators `rels`: the free profinite
group on `X` modulo the closed normal closure of the relators. -/
noncomputable def profinitePresentation {X : Type u} (rels : Set (FreeProfiniteGroup X)) :
    ProfiniteGrp.{u} :=
  haveI : IsClosed ((relatorSubgroup rels) : Set (FreeProfiniteGroup X)) :=
    Subgroup.isClosed_topologicalClosure _
  profiniteQuotient (relatorSubgroup rels)

/-- The presentation does impose the relations: each relator maps to `1` under the quotient
projection `FreeProfiniteGroup X → FreeProfiniteGroup X ⧸ relatorSubgroup rels`. -/
theorem relator_quotientMk_eq_one {X : Type u} (rels : Set (FreeProfiniteGroup X))
    {r : FreeProfiniteGroup X} (hr : r ∈ rels) :
    quotientMk (relatorSubgroup rels) r = 1 := by
  rw [quotientMk_eq_one_iff]
  exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hr)

end GQ2
