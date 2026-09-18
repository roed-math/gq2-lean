import GQ2.Dyadic.MarkedCore.NScalingAudit
import GQ2.Reconstruction

/-!
# Free pro-two commutator shears at arbitrary rank

The substitution c maps to c[c,b]^s and fixes every other marked generator. It
is a genuine automorphism and fixes every ordinary Z2 character simultaneously.
No N-relator or relative boundary preservation is asserted.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2

abbrev FreeTwoRank (n : ℕ) : ProfiniteGrp := presPro2 (1 : FreeProfiniteGroup (Fin n))
def freeTwoRankGen (n : ℕ) (i : Fin n) : FreeTwoRank n := presGen 1 i

private theorem isProP_freeTwoRank (n : ℕ) : IsProP 2 (FreeTwoRank n : Type) :=
  isProP_presPro2 1

def freeTwoCommutatorShearMark (n : ℕ) (c b : Fin n) (s : ℤ_[2])
    (i : Fin n) : FreeTwoRank n :=
  if i = c then freeTwoRankGen n c * zpowZtwo (isProP_freeTwoRank n)
      (commP (freeTwoRankGen n c) (freeTwoRankGen n b)) s
  else freeTwoRankGen n i

def freeTwoCommutatorShearHom (n : ℕ) (c b : Fin n) (s : ℤ_[2]) :
    ContinuousMonoidHom (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  presLiftHom 1 (isProP_freeTwoRank n) (freeTwoCommutatorShearMark n c b s) (map_one _)

theorem freeTwoCommutatorShearHom_gen (n : ℕ) (c b i : Fin n) (s : ℤ_[2]) :
    freeTwoCommutatorShearHom n c b s (freeTwoRankGen n i) =
      freeTwoCommutatorShearMark n c b s i :=
  presLiftHom_gen _ _ _ _ _

private theorem map_zpow_of_map_eq_one {P Q : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
    (hP : IsProP 2 P) (f : ContinuousMonoidHom P Q) (z : P) (hz : f z = 1) (s : ℤ_[2]) :
    f (zpowZtwo hP z s) = 1 := by
  refine PadicInt.denseRange_natCast.induction_on s ?_ ?_
  · exact isClosed_eq (f.continuous_toFun.comp (continuous_zpowZtwo hP z)) continuous_const
  · intro k
    rw [zpowZtwo_natCast, map_pow, hz, one_pow]

private theorem shear_character {Q : Type} [CommGroup Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [T2Space Q] (n : ℕ) (c b : Fin n) (s : ℤ_[2])
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) Q) :
    f.comp (freeTwoCommutatorShearHom n c b s) = f := by
  apply presPro2_hom_ext
  intro i
  change f (freeTwoCommutatorShearHom n c b s (freeTwoRankGen n i)) = f (freeTwoRankGen n i)
  rw [freeTwoCommutatorShearHom_gen, freeTwoCommutatorShearMark]
  split_ifs with hi
  · subst i
    rw [map_mul, map_zpow_of_map_eq_one (isProP_freeTwoRank n) f _
      (by simp [commP, mul_comm]) s, mul_one]
  · rfl

theorem freeTwoCommutatorShearHom_surjective (n : ℕ) (c b : Fin n) (s : ℤ_[2]) :
    Function.Surjective (freeTwoCommutatorShearHom n c b s) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine surjective_of_forall_index_p_quotient_surjective (isProP_freeTwoRank n) _ ?_
  intro M hM
  letI : Finite ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ M.isOpen'
  have hc : Nat.card ((FreeTwoRank n : Type) ⧸ M.toSubgroup) = 2 := by
    rwa [← Subgroup.index_eq_card]
  have hi := isCyclic_of_prime_card (p := 2) hc
  letI : CommGroup ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    { (inferInstance : Group ((FreeTwoRank n : Type) ⧸ M.toSubgroup)) with
      mul_comm := fun x y => IsMulCommutative.is_comm.comm x y }
  let q : ContinuousMonoidHom (FreeTwoRank n : Type)
      ((FreeTwoRank n : Type) ⧸ M.toSubgroup) :=
    ⟨QuotientGroup.mk' M.toSubgroup, continuous_quot_mk⟩
  have he := shear_character n c b s q
  intro z
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup z
  refine ⟨x, ?_⟩
  exact congrArg (fun f : ContinuousMonoidHom _ _ => f x) he

private theorem freeTwoRank_topologicallyFinGen (n : ℕ) :
    ∃ t : Finset (FreeTwoRank n : Type),
      (Subgroup.closure (t : Set (FreeTwoRank n : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨Finset.univ.image (freeTwoRankGen n), ?_⟩
  have ht : (↑(Finset.univ.image (freeTwoRankGen n)) : Set (FreeTwoRank n : Type)) =
      Set.range (freeTwoRankGen n) := by simp
  rw [ht]
  exact presPro2_topGen _

/-- This is an automorphism of the free pro-two group, not an asserted
automorphism of the N quotient. No condition c ≠ b is needed. -/
def freeTwoCommutatorShearEquiv (n : ℕ) (c b : Fin n) (s : ℤ_[2]) :
    ContinuousMulEquiv (FreeTwoRank n : Type) (FreeTwoRank n : Type) :=
  continuousMulEquivOfBijective (freeTwoCommutatorShearHom n c b s)
    ⟨profinite_hopfian (freeTwoRank_topologicallyFinGen n) _
      (freeTwoCommutatorShearHom_surjective n c b s),
      freeTwoCommutatorShearHom_surjective n c b s⟩

theorem freeTwoCommutatorShearEquiv_gen (n : ℕ) (c b i : Fin n) (s : ℤ_[2]) :
    freeTwoCommutatorShearEquiv n c b s (freeTwoRankGen n i) =
      freeTwoCommutatorShearMark n c b s i :=
  freeTwoCommutatorShearHom_gen n c b i s

/-- Simultaneous equality for every ordinary character, on every group element,
not merely a statement for a character chosen before constructing the shear. -/
theorem freeTwoCommutatorShearEquiv_character (n : ℕ) (c b : Fin n) (s : ℤ_[2])
    (f : ContinuousMonoidHom (FreeTwoRank n : Type) (Multiplicative ℤ_[2]))
    (x : FreeTwoRank n) :
    f (freeTwoCommutatorShearEquiv n c b s x) = f x :=
  congrArg (fun g : ContinuousMonoidHom _ _ => g x) (shear_character n c b s f)

#print axioms FreeTwoRank
#print axioms freeTwoRankGen
#print axioms freeTwoCommutatorShearMark
#print axioms freeTwoCommutatorShearHom
#print axioms freeTwoCommutatorShearHom_gen
#print axioms freeTwoCommutatorShearHom_surjective
#print axioms freeTwoCommutatorShearEquiv
#print axioms freeTwoCommutatorShearEquiv_gen
#print axioms freeTwoCommutatorShearEquiv_character

end
end GQ2.Dyadic.MarkedCore

