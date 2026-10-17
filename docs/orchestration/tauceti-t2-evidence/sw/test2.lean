module

public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.Transfer
public import TauCeti.FieldTheory.QuadraticForm.StiefelWhitney.QuadraticExtension
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Evens.Cochain
public import GQ2.TraceForm

set_option synthInstance.maxHeartbeats 400000

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ### cochain-level comparison of the Evens/corestriction formulas -/

section Cochain

variable {G : Type} [Group G] (U : Subgroup G) (s : G) (α : U → ZMod 2)
  (hα : ∀ u v : U, α (u * v) = α u + α v)

/-- gq2's additive homomorphism `α : U → 𝔽₂`, as Tau Ceti's `U →* Multiplicative (ZMod 2)`. -/
noncomputable def toMultHom : U →* Multiplicative (ZMod 2) where
  toFun u := Multiplicative.ofAdd (α u)
  map_one' := by
    have h := hα 1 1
    rw [mul_one] at h
    have : α 1 = 0 := by simpa using h
    simp [this]
  map_mul' u v := by simp [hα u v, ofAdd_add]

theorem evensAux_eq_evensB1 (x : G) :
    GQ2.evensAux U s α x = TauCeti.ContCohomology.evensB1 U s (toMultHom U α hα) x := by
  open TauCeti.ContCohomology in
  by_cases hx : x ∈ U
  · rw [GQ2.evensAux_of_mem α hx, evensB1_of_mem hx, evensExtend_of_mem hx]; rfl
  · rw [evensB1_of_notMem hx]
    by_cases hxs : x * s ∈ U
    · rw [GQ2.evensAux, dif_neg hx, dif_pos hxs, evensExtend_of_mem hxs]; rfl
    · rw [GQ2.evensAux, dif_neg hx, dif_neg hxs, evensExtend_of_notMem hxs]

theorem bS_eq_evensBs (x : G) :
    GQ2.bS U s α x = TauCeti.ContCohomology.evensBs U s (toMultHom U α hα) x := by
  rw [TauCeti.ContCohomology.evensBs_apply, ← evensAux_eq_evensB1 U s α hα]; rfl

theorem corFun_eq_evensCorCochain :
    GQ2.corFun U s α = TauCeti.ContCohomology.evensCorCochain U s (toMultHom U α hα) := by
  funext x
  rw [TauCeti.ContCohomology.evensCorCochain_apply, GQ2.corFun, evensAux_eq_evensB1 U s α hα,
    bS_eq_evensBs U s α hα]

theorem evensNormFun_eq_evensGraphCochain :
    GQ2.evensNormFun U s α = TauCeti.ContCohomology.evensGraphCochain U s (toMultHom U α hα) := by
  funext ⟨γ, η⟩
  by_cases hγ : γ ∈ U
  · rw [TauCeti.ContCohomology.evensGraphCochain_of_mem hγ, GQ2.evensNormFun, if_pos hγ,
      evensAux_eq_evensB1 U s α hα, bS_eq_evensBs U s α hα]
  · rw [TauCeti.ContCohomology.evensGraphCochain_of_notMem hγ, GQ2.evensNormFun, if_neg hγ,
      evensAux_eq_evensB1 U s α hα, evensAux_eq_evensB1 U s α hα, bS_eq_evensBs U s α hα]

end Cochain

/-! ### quadratic forms -/

section Forms

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

theorem diagForm_eq_weightedSumSquares (x y : (↥k)ˣ) :
    GQ2.diagForm k x y = QuadraticMap.weightedSumSquares ↥k fun i => ((![x, y] i : (↥k)ˣ) : ↥k) := by
  ext v
  simp [GQ2.diagForm, QuadraticMap.weightedSumSquares_apply, Units.smul_def]

theorem isDiagonalization_iff (V : Type*) [AddCommGroup V] [Module ↥k V]
    (Q : QuadraticForm ↥k V) (x y : (↥k)ˣ) :
    GQ2.IsDiagonalization k Q x y ↔
      Q.Equivalent (QuadraticMap.weightedSumSquares ↥k fun i => ((![x, y] i : (↥k)ˣ) : ↥k)) := by
  rw [GQ2.IsDiagonalization, diagForm_eq_weightedSumSquares]

variable [FiniteDimensional ℚ_[2] k] {δ : ℚ̄₂}

/-- nondegeneracy of the twisted trace form, in the shape gq2's `exists_isDiagonalization` needs -/
theorem traceFormTwisted_separatingLeft (d : (↥k)ˣ) (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) (a : (↥(GQ2.quadExt k δ))ˣ) :
    (QuadraticMap.associated (R := ↥k) (GQ2.traceFormTwisted k δ ↑a)).SeparatingLeft := by
  haveI := GQ2.finiteDimensional_quadExt k d hδ
  have h1 : (QuadraticMap.traceTransfer ↥k ((a : ↥(GQ2.quadExt k δ)) •
      QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ)))).Nondegenerate :=
    (QuadraticMap.nondegenerate_traceTransfer_iff _).2 (QuadraticMap.nondegenerate_smul_sq a.ne_zero)
  have heq : GQ2.traceFormTwisted k δ ↑a = QuadraticMap.traceTransfer ↥k
      ((a : ↥(GQ2.quadExt k δ)) •
        QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) := by
    ext z
    rw [GQ2.traceFormTwisted_apply, QuadraticMap.traceTransfer_apply, smul_apply,
      QuadraticMap.sq_apply, smul_eq_mul, mul_assoc]
  rw [heq]
  exact (QuadraticMap.nondegenerate_associated_iff.mpr h1).1

/-- The Tau Ceti diagonal-presentation identities instantiate at `K = ↥k`, `L = ↥(quadExt k δ)`,
for any `σ`. -/
example [FiniteDimensional ↥k ↥(GQ2.quadExt k δ)] (hdeg : Module.finrank ↥k ↥(GQ2.quadExt k δ) = 2) (a : (↥(GQ2.quadExt k δ))ˣ)
    (σ : ↥(GQ2.quadExt k δ) →ₐ[↥k] SeparableClosure ↥k) (x y x' y' : (↥k)ˣ)
    (h1 : GQ2.IsDiagonalization k (GQ2.traceFormOne k δ) x y)
    (ha : GQ2.IsDiagonalization k (GQ2.traceFormTwisted k δ ↑a) x' y') :
    TauCeti.kummerClass x' + TauCeti.kummerClass y' =
        TauCeti.kummerClass x + TauCeti.kummerClass y +
          TauCeti.galoisCor ↥k ↥(GQ2.quadExt k δ) σ 1 (TauCeti.kummerClass a) ∧
      (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
          (TauCeti.kummerClass x') (TauCeti.kummerClass y') =
        (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x) (TauCeti.kummerClass y) +
          TauCeti.galoisEvens ↥k ↥(GQ2.quadExt k δ) σ hdeg (TauCeti.kummerClass a) +
          (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x + TauCeti.kummerClass y)
            (TauCeti.galoisCor ↥k ↥(GQ2.quadExt k δ) σ 1 (TauCeti.kummerClass a)) := by
  have heq1 : GQ2.traceFormOne k δ = QuadraticMap.traceTransfer ↥k
      (QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) :=
    QuadraticMap.traceTransfer_sq.symm
  have heqa : GQ2.traceFormTwisted k δ ↑a = QuadraticMap.traceTransfer ↥k
      ((a : ↥(GQ2.quadExt k δ)) •
        QuadraticMap.sq (R := ↥(GQ2.quadExt k δ)) (A := ↥(GQ2.quadExt k δ))) := by
    ext z
    rw [GQ2.traceFormTwisted_apply, QuadraticMap.traceTransfer_apply, smul_apply,
      QuadraticMap.sq_apply, smul_eq_mul, mul_assoc]
  rw [isDiagonalization_iff] at h1 ha
  rw [heq1] at h1
  rw [heqa] at ha
  have e1 := TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer σ a h1 ha
  have e2 := TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer σ hdeg a h1 ha
  rw [TauCeti.sw1_fin_two, TauCeti.sw1_fin_two] at e1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e1
  have hs2 : ∀ u v : (↥k)ˣ, TauCeti.sw2 ![u, v] = (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
          (TauCeti.kummerClass u) (TauCeti.kummerClass v) := fun u v => TauCeti.sw2_fin_two _
  have hs1 : ∀ u v : (↥k)ˣ, TauCeti.sw1 ![u, v] = TauCeti.kummerClass u + TauCeti.kummerClass v :=
    fun u v => TauCeti.sw1_fin_two _
  refine ⟨e1, ?_⟩
  simp only [hs2, hs1] at e2
  exact e2

open GQ2 in
/-- gq2's `swOne` is the sum of the Kummer classes of its *chosen* diagonalization, with no
`hnorm` hypothesis (this is `dif_pos`); the chosen pair is a genuine diagonalization. -/
example {V : Type*} [AddCommGroup V] [Module ↥k V] (Q : QuadraticForm ↥k V)
    (h : ∃ x y : (↥k)ˣ, GQ2.IsDiagonalization k Q x y)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
    GQ2.swOne k Q = GQ2.kummerClassK k h.choose + GQ2.kummerClassK k h.choose_spec.choose ∧
      GQ2.swTwo k htriv Q =
        GQ2.kummerClassK k h.choose ⌣[htriv] GQ2.kummerClassK k h.choose_spec.choose ∧
      GQ2.IsDiagonalization k Q h.choose h.choose_spec.choose :=
  ⟨dif_pos h, dif_pos h, h.choose_spec.choose_spec⟩

end Forms
