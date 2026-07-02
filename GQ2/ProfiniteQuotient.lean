import Mathlib

/-!
# Quotients of profinite groups by closed normal subgroups are profinite

The paper's presented group `Γ_A` is a quotient of a free profinite group by the closed normal
closure of the relators.  Mathlib already provides `CompactSpace`, `T3Space` (hence `T2Space`), and
`IsTopologicalGroup` instances for `G ⧸ N`; the missing ingredient of profiniteness is total
disconnectedness (see `docs/foundations-audit.md`, "profinite presentations" gap).

This file supplies it: for `G` profinite and `N` a *closed* normal subgroup, `G ⧸ N` is totally
disconnected.  The clopen subsets of `G ⧸ N` form a topological basis — for `x ∈ u` open, lift `x`
to `p ∈ G`, take an open normal subgroup `U ⊆ G` with `p · U` inside the preimage of `u` (possible
since `G` is profinite), and push forward: `q '' (p · U)` is clopen (the quotient map `q` is open,
and closed because `N` is compact) and lies between `x` and `u`.  A T0 space with a clopen basis is
totally separated, hence totally disconnected.
-/

open scoped Pointwise

namespace GQ2

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal]

/-- For `G` profinite and `N` a closed normal subgroup, the clopen subsets of `G ⧸ N` form a
topological basis. -/
theorem isTopologicalBasis_clopen_quotient [IsClosed (N : Set G)] :
    TopologicalSpace.IsTopologicalBasis {s : Set (G ⧸ N) | IsClopen s} := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds (fun s hs => hs.2) ?_
  intro x u hxu hu
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective x
  -- `W = {g | p * g ∈ q⁻¹ u}` is an open neighbourhood of `1`.
  have hpre : IsOpen (QuotientGroup.mk ⁻¹' u : Set G) := hu.preimage continuous_coinduced_rng
  set W : Set G := (Homeomorph.mulLeft p) ⁻¹' (QuotientGroup.mk ⁻¹' u) with hW
  have hWopen : IsOpen W := hpre.preimage (Homeomorph.mulLeft p).continuous
  have hW1 : (1 : G) ∈ W := by simpa [hW] using hxu
  -- `G` profinite: some open normal subgroup `U` sits inside `W`.
  obtain ⟨U, hUW⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hWopen hW1
  -- The clopen coset `p · U` in `G`, pushed to `G ⧸ N`.
  set C : Set (G ⧸ N) := QuotientGroup.mk '' ((Homeomorph.mulLeft p) '' (U : Set G)) with hC
  have hNcompact : IsCompact (N : Set G) := IsClosed.isCompact ‹IsClosed (N : Set G)›
  have hcosetClopen : IsClopen ((Homeomorph.mulLeft p) '' (U : Set G)) :=
    ⟨(Homeomorph.mulLeft p).isClosedMap _ U.isClopen.1,
      (Homeomorph.mulLeft p).isOpenMap _ U.isClopen.2⟩
  have hCclopen : IsClopen C := by
    refine ⟨?_, ?_⟩
    · exact (QuotientGroup.isClosedMap_coe hNcompact) _ hcosetClopen.1
    · exact QuotientGroup.isOpenMap_coe _ hcosetClopen.2
  refine ⟨C, hCclopen, ?_, ?_⟩
  · -- `x = q p ∈ C` since `p = p * 1 ∈ p · U`.
    exact ⟨p, ⟨1, U.one_mem, by simp⟩, rfl⟩
  · -- `C ⊆ u`: any `q (p * g)` with `g ∈ U ⊆ W` lands in `u`.
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have : p * g ∈ QuotientGroup.mk ⁻¹' u := hUW hg
    simpa using this

/-- **Total disconnectedness of `G ⧸ N`** for `G` profinite and `N` closed normal.  Together with
the ambient `CompactSpace`, `T2Space`, and `IsTopologicalGroup` instances this is the last piece of
profiniteness. -/
instance instTotallyDisconnectedSpace_quotient [IsClosed (N : Set G)] :
    TotallyDisconnectedSpace (G ⧸ N) :=
  haveI : TotallySeparatedSpace (G ⧸ N) :=
    totallySeparatedSpace_of_t0_of_basis_clopen (isTopologicalBasis_clopen_quotient N)
  inferInstance

/-- The quotient of a profinite group `G` by a closed normal subgroup `N`, packaged as an object of
`ProfiniteGrp`.  This is the construction underlying profinite presentations (e.g. the paper's
`Γ_A`): quotient the free profinite group by the closed normal closure of the relators. -/
def profiniteQuotient [IsClosed (N : Set G)] : ProfiniteGrp :=
  ProfiniteGrp.of (G ⧸ N)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The quotient projection `G → G ⧸ N` as a continuous homomorphism. -/
def quotientMk : ContinuousMonoidHom G (G ⧸ N) :=
  ⟨QuotientGroup.mk' N, QuotientGroup.continuous_mk⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem quotientMk_surjective : Function.Surjective (quotientMk N) :=
  QuotientGroup.mk_surjective

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
@[simp] theorem quotientMk_apply (g : G) : quotientMk N g = QuotientGroup.mk g := rfl

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- An element lies in the kernel of the quotient projection iff it lies in `N`. -/
theorem quotientMk_eq_one_iff {g : G} : quotientMk N g = 1 ↔ g ∈ N :=
  QuotientGroup.eq_one_iff g

section Lift
variable {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **Universal property of the profinite quotient.**  A continuous homomorphism `f : G →ₜ* P`
whose kernel contains `N` factors through the quotient projection as a continuous homomorphism
`G ⧸ N →ₜ* P`.  (Continuity is automatic: `G → G ⧸ N` is a quotient map.) -/
noncomputable def quotientLift (f : ContinuousMonoidHom G P)
    (hf : N ≤ f.toMonoidHom.ker) : ContinuousMonoidHom (G ⧸ N) P :=
  ⟨QuotientGroup.lift N f.toMonoidHom hf,
    (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr f.continuous_toFun⟩

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] [IsTopologicalGroup P] in
@[simp] theorem quotientLift_quotientMk (f : ContinuousMonoidHom G P)
    (hf : N ≤ f.toMonoidHom.ker) (g : G) : quotientLift N f hf (quotientMk N g) = f g := rfl

end Lift

end GQ2
