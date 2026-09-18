import GQ2.MaxProP

/-!
# Products of profinite pro-p groups

The coordinate projections kill the pro-p kernel of the product, so that
kernel is trivial. Compactness then gives the pro-p property of every open
normal quotient. The proof actually works for arbitrary dependent products;
finite pro-two tuples are its intended consumer here.
-/

namespace GQ2

theorem isProP_pi {p : ℕ} {I : Type*} (P : I → Type*)
    [∀ i, Group (P i)] [∀ i, TopologicalSpace (P i)]
    [∀ i, IsTopologicalGroup (P i)] [∀ i, CompactSpace (P i)]
    [∀ i, T2Space (P i)] [∀ i, TotallyDisconnectedSpace (P i)]
    (hP : ∀ i, IsProP p (P i)) : IsProP p (∀ i, P i) := by
  have hker : proPKernel p (∀ i, P i) = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    change x = 1
    funext i
    let ev : ContinuousMonoidHom (∀ j, P j) (P i) :=
      { toFun := fun y => y i
        map_one' := rfl
        map_mul' := fun _ _ => rfl
        continuous_toFun := continuous_apply i }
    exact proPKernel_le_ker (hP i) ev hx
  intro U
  apply isPGroup_quotient_of_proPKernel_le U
  rw [hker]
  exact bot_le

/-- Uniform finite tuple specialization, including the empty tuple. -/
theorem isProP_fin_tuple {p : ℕ} {P : Type*} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP p P) (n : ℕ) : IsProP p (Fin n → P) :=
  isProP_pi (fun _ : Fin n => P) (fun _ => hP)

#print axioms isProP_pi
#print axioms isProP_fin_tuple

end GQ2
