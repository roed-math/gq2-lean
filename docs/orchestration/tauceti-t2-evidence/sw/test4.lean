module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension
public import GQ2.TraceForm

set_option synthInstance.maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (k : IntermediateField ℚ_[2] ℚ̄₂) {δ : ℚ̄₂}

/-- the generator `δ` of `quadExt k δ` is not in `k` once `[k(δ):k] = 2` -/
theorem gen_notMem_range (hdeg : Module.finrank ↥k ↥(GQ2.quadExt k δ) = 2) :
    IntermediateField.AdjoinSimple.gen ↥k δ ∉
      Set.range (algebraMap ↥k ↥(GQ2.quadExt k δ)) := by
  rintro ⟨c, hc⟩
  have hmem : δ ∈ (⊥ : IntermediateField ↥k ℚ̄₂) := by
    rw [IntermediateField.mem_bot]
    exact ⟨c, by simpa [IntermediateField.AdjoinSimple.coe_gen] using congrArg Subtype.val hc⟩
  have := IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr hmem
  rw [GQ2.quadExt] at hdeg
  omega

/-- For any `↥k`-embedding `σ` of `L = ↥(quadExt k δ)`, `G_L` is the stabilizer of `σ δ`. -/
example [FiniteDimensional ↥k ↥(GQ2.quadExt k δ)]
    (hdeg : Module.finrank ↥k ↥(GQ2.quadExt k δ) = 2)
    (σ : ↥(GQ2.quadExt k δ) →ₐ[↥k] SeparableClosure ↥k) (g : TauCeti.AbsoluteGaloisGroup ↥k) :
    g ∈ TauCeti.galoisSubgroup ↥k ↥(GQ2.quadExt k δ) σ ↔
      g (σ (IntermediateField.AdjoinSimple.gen ↥k δ)) = σ (IntermediateField.AdjoinSimple.gen ↥k δ) :=
  TauCeti.mem_galoisSubgroup_iff_apply_eq_of_finrank_eq_two _ _ σ hdeg (gen_notMem_range k hdeg)
