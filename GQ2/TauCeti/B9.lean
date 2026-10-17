/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import GQ2.TauCeti.StiefelWhitneyDict

@[expose] public section

/-!
# B9: the relative Stiefel–Whitney identity, discharged from Tau Ceti

Ticket **B9** of the Tau Ceti discharge campaign
(`docs/orchestration/tauceti-tickets.md`, memo `docs/orchestration/tauceti-t2-recon.md` §B9).
This file provides

* `GQ2.TauCetiBridge.relativeStiefelWhitney_dyadic_tauceti`, whose statement is the
  `relativeStiefelWhitney_dyadic` field of `GQ2.LiteratureInputs` verbatim, proved from Tau Ceti's
  `sw1_eq_add_galoisCor_of_equivalent_traceTransfer` and
  `sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer` through the dictionary of
  `GQ2/TauCeti/StiefelWhitneyDict.lean`, with no `sorry` and at the standard three axioms;
* the identities on arbitrary unit diagonalizations `Tr⟨1⟩ ≃ ⟨x, y⟩`, `Tr⟨a⟩ ≃ ⟨x', y'⟩`, in
  Tau Ceti's classes (`kummerClass_add_kummerClass_eq_add_galoisCor`,
  `cup_kummerClass_kummerClass_eq_add_galoisEvens_add_cup`) and in gq2's
  (`kummerClassK_add_kummerClassK_eq_add_corH1_of_isDiagonalization`,
  `cup_kummerClassK_kummerClassK_eq_of_isDiagonalization`), with the hypothesis shapes
  `traceTransfer_sq_equivalent_of_isDiagonalization`,
  `traceTransfer_smul_sq_equivalent_of_isDiagonalization`.

## Translation (memo §B9)

Base `K = ↥k`, layer `L = ↥(quadExt k δ)` itself (no module identification), Tau Ceti's embedding
`σ = layerEmb k L` (A1), group dictionary `Φ = fixingEquivAbsGal k` (A1), cohomology dictionary
`cont1F2`/`cont2F2` (A2).

* gq2's `swOne`/`swTwo` are `dite` on a chosen unit diagonalization, so `dite_eq_left` reads them
  off at the chosen pair (`swOne_eq_of_exists`, `swTwo_eq_of_exists`); existence is
  `traceFormOne_isDiagonalization` for `Tr⟨1⟩` and `exists_isDiagonalization_traceFormTwisted`
  for `Tr⟨a⟩`.  Feeding the chosen pairs `![x, y]`, `![x', y']` to Tau Ceti's two
  diagonal-presentation theorems (with `traceFormOne_eq_traceTransfer_sq`,
  `traceFormTwisted_eq_traceTransfer_smul_sq`) and reading `sw1_fin_two`/`sw2_fin_two` gives
  `(x') + (y') = (x) + (y) + cor (a)` and
  `(x') ∪ (y') = (x) ∪ (y) + N^{Ev}(a) + ((x) + (y)) ∪ cor (a)` over `G_k = Gal(kˢᵉᵖ/k)`.
  No `hnorm` (B11a) is needed.
* Both identities are pulled back along `Φ` with `trivialF2Map`, where
  `trivialF2Map_fixingEquivAbsGal_kummerClass` (A2) turns `kummerClass x` into
  `cont1F2 _ (kummerClassK k x)`, `trivialF2Map_galoisCor_kummerClass` turns `cor (a)` into
  `cont1F2 _ (corH1 …)`, `trivialF2Map_galoisEvens_kummerClass` turns `N^{Ev}(a)` into
  `cont2F2 _ (evensNormH2 …)`, and `trivialF2Map_cup_one_one` with `cont2F2_trivialCupPairing`
  (A2) match the cups.  Injectivity of `cont1F2`/`cont2F2` finishes; the degree-two summand
  orders differ by `add_right_comm`.
* The field's `hidx`, `hUo` are consumed only through gq2's `corH1`/`evensNormH2` (the Tau Ceti
  side takes the index from `galoisSubgroup_index` and `hdeg`); `hβ0` is unused.
* The calc chains use term-mode `map_add`/`congrArg` and `simp only` for the dictionary
  substitutions; `rw` on these cohomology terms exhausts the heartbeat budget (the diagonalization
  lemmas are stated for variables `x y x' y'` so that no `Exists.choose` is unfolded by `isDefEq`).
-/

set_option synthInstance.maxHeartbeats 400000

open GQ2.ContCoh

namespace GQ2.TauCetiBridge

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

section Diagonalizations

variable (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k] (δ : ℚ̄₂)
  (a : (↥(quadExt k δ))ˣ) {x y x' y' : (↥k)ˣ}
  (hxy : IsDiagonalization k (traceFormOne k δ) x y)
  (hx'y' : IsDiagonalization k (traceFormTwisted k δ ↑a) x' y')

omit [FiniteDimensional ℚ_[2] k] in
include hxy in
/-- Tau Ceti's hypothesis shape for `Tr⟨1⟩`: `Tr_*⟨1⟩ ≃ weightedSumSquares ↥k ![x, y]`. -/
theorem traceTransfer_sq_equivalent_of_isDiagonalization :
    (QuadraticMap.traceTransfer ↥k
      (QuadraticMap.sq (R := ↥(quadExt k δ)) (A := ↥(quadExt k δ)))).Equivalent
        (QuadraticMap.weightedSumSquares ↥k fun i => ((![x, y] i : (↥k)ˣ) : ↥k)) := by
  rw [← traceFormOne_eq_traceTransfer_sq]
  exact (isDiagonalization_iff_equivalent_weightedSumSquares k _ x y).1 hxy

omit [FiniteDimensional ℚ_[2] k] in
include hx'y' in
/-- Tau Ceti's hypothesis shape for `Tr⟨a⟩`: `Tr_*⟨a⟩ ≃ weightedSumSquares ↥k ![x', y']`. -/
theorem traceTransfer_smul_sq_equivalent_of_isDiagonalization :
    (QuadraticMap.traceTransfer ↥k ((a : ↥(quadExt k δ)) •
      QuadraticMap.sq (R := ↥(quadExt k δ)) (A := ↥(quadExt k δ)))).Equivalent
        (QuadraticMap.weightedSumSquares ↥k fun i => ((![x', y'] i : (↥k)ˣ) : ↥k)) := by
  rw [← traceFormTwisted_eq_traceTransfer_smul_sq]
  exact (isDiagonalization_iff_equivalent_weightedSumSquares k _ x' y').1 hx'y'

variable [FiniteDimensional ↥k ↥(quadExt k δ)]

omit [FiniteDimensional ℚ_[2] k] in
include hxy hx'y' in
/-- **Tau Ceti's degree-one identity on the diagonalizations**, over `G_k = Gal(kˢᵉᵖ/k)` with
`σ = layerEmb k L`: `(x') + (y') = (x) + (y) + cor (a)`
(`sw1_eq_add_galoisCor_of_equivalent_traceTransfer` read through `sw1_fin_two`). -/
theorem kummerClass_add_kummerClass_eq_add_galoisCor :
    TauCeti.kummerClass x' + TauCeti.kummerClass y' =
      TauCeti.kummerClass x + TauCeti.kummerClass y +
        TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
          (TauCeti.kummerClass a) := by
  have hs1 : ∀ u v : (↥k)ˣ, TauCeti.sw1 ![u, v] = TauCeti.kummerClass u + TauCeti.kummerClass v :=
    fun u v => TauCeti.sw1_fin_two _
  have := TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer (layerEmb k (quadExt k δ)) a
    (traceTransfer_sq_equivalent_of_isDiagonalization k δ hxy)
    (traceTransfer_smul_sq_equivalent_of_isDiagonalization k δ a hx'y')
  simp only [hs1] at this
  exact this

variable (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)

omit [FiniteDimensional ℚ_[2] k] in
include hxy hx'y' in
/-- **Tau Ceti's degree-two identity on the diagonalizations**, over `G_k = Gal(kˢᵉᵖ/k)` with
`σ = layerEmb k L`: `(x') ∪ (y') = (x) ∪ (y) + N^{Ev}(a) + ((x) + (y)) ∪ cor (a)`
(`sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer` read through `sw2_fin_two`,
`sw1_fin_two`). -/
theorem cup_kummerClass_kummerClass_eq_add_galoisEvens_add_cup :
    (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
        (TauCeti.kummerClass x') (TauCeti.kummerClass y') =
      (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
          (TauCeti.kummerClass x) (TauCeti.kummerClass y) +
        TauCeti.galoisEvens ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) hdeg
          (TauCeti.kummerClass a) +
        (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
          (TauCeti.kummerClass x + TauCeti.kummerClass y)
          (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
            (TauCeti.kummerClass a)) := by
  have hs1 : ∀ u v : (↥k)ˣ, TauCeti.sw1 ![u, v] = TauCeti.kummerClass u + TauCeti.kummerClass v :=
    fun u v => TauCeti.sw1_fin_two _
  have hs2 : ∀ u v : (↥k)ˣ, TauCeti.sw2 ![u, v] =
      (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
        (TauCeti.kummerClass u) (TauCeti.kummerClass v) :=
    fun u v => TauCeti.sw2_fin_two _
  have := TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer
    (layerEmb k (quadExt k δ)) hdeg a
    (traceTransfer_sq_equivalent_of_isDiagonalization k δ hxy)
    (traceTransfer_smul_sq_equivalent_of_isDiagonalization k δ a hx'y')
  simp only [hs2, hs1] at this
  exact this

variable {β : ℚ̄₂} (hβ : β ^ 2 = ((a : ↥(quadExt k δ)) : ℚ̄₂))
  (s : k.fixingSubgroup)
  (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
  (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
  (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
    k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
  (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
    k.fixingSubgroup).index = 2)
  (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup) → ZMod 2)
  (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
    ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
  (hα : ∀ g h, α (g * h) = α g + α h) (hαc : Continuous α)

omit [FiniteDimensional ↥k ↥(quadExt k δ)] in
include hdeg hβ hs hUo hidx hαdef hα hαc hxy hx'y' in
/-- **The degree-one relative Stiefel–Whitney identity on unit diagonalizations**
`Tr⟨1⟩ ≃ ⟨x, y⟩`, `Tr⟨a⟩ ≃ ⟨x', y'⟩`, in gq2's Kummer classes over `G_k = ↥k.fixingSubgroup`:
`(x') + (y') = (x) + (y) + cor`.  Tau Ceti's identity pulled back along
`Φ = fixingEquivAbsGal k` through the dictionary. -/
theorem kummerClassK_add_kummerClassK_eq_add_corH1_of_isDiagonalization :
    kummerClassK k x' + kummerClassK k y' =
      kummerClassK k x + kummerClassK k y + corH1 htriv hUo hidx hs α hα hαc := by
  have : FiniteDimensional ↥k ↥(quadExt k δ) := finiteDimensional_quadExt_of_finrank_eq_two k δ hdeg
  have K : ∀ u : (↥k)ˣ,
      cont1F2 k.fixingSubgroup htriv (kummerClassK k u) =
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass u) :=
    fun u => (trivialF2Map_fixingEquivAbsGal_kummerClass k htriv u).symm
  have C := (trivialF2Map_galoisCor_kummerClass k δ a hβ α hαdef hdeg s hs htriv hUo hidx hα
    hαc).symm
  apply (cont1F2 k.fixingSubgroup htriv).injective
  calc cont1F2 k.fixingSubgroup htriv (kummerClassK k x' + kummerClassK k y')
      = cont1F2 k.fixingSubgroup htriv (kummerClassK k x') +
          cont1F2 k.fixingSubgroup htriv (kummerClassK k y') := map_add _ _ _
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x') +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y') := by simp only [K]
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x' + TauCeti.kummerClass y') :=
        (map_add _ _ _).symm
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
          (TauCeti.kummerClass x + TauCeti.kummerClass y +
            TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
              (TauCeti.kummerClass a)) :=
        congrArg (fun z => TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 z)
          (kummerClass_add_kummerClass_eq_add_galoisCor k δ a hxy hx'y')
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x + TauCeti.kummerClass y) +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
          (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
            (TauCeti.kummerClass a)) := map_add _ _ _
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x) +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y) +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
          (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
            (TauCeti.kummerClass a)) :=
        congrArg (· + TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
          (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
            (TauCeti.kummerClass a))) (map_add _ _ _)
    _ = cont1F2 k.fixingSubgroup htriv (kummerClassK k x) +
          cont1F2 k.fixingSubgroup htriv (kummerClassK k y) +
          cont1F2 k.fixingSubgroup htriv (corH1 htriv hUo hidx hs α hα hαc) := by
        simp only [K, C]
    _ = cont1F2 k.fixingSubgroup htriv (kummerClassK k x + kummerClassK k y) +
          cont1F2 k.fixingSubgroup htriv (corH1 htriv hUo hidx hs α hα hαc) :=
        congrArg (· + cont1F2 k.fixingSubgroup htriv (corH1 htriv hUo hidx hs α hα hαc))
          (map_add _ _ _).symm
    _ = cont1F2 k.fixingSubgroup htriv
          (kummerClassK k x + kummerClassK k y + corH1 htriv hUo hidx hs α hα hαc) :=
        (map_add _ _ _).symm

omit [FiniteDimensional ↥k ↥(quadExt k δ)] in
include hdeg hβ hs hUo hidx hαdef hα hαc hxy hx'y' in
/-- **The degree-two relative Stiefel–Whitney identity on unit diagonalizations**
`Tr⟨1⟩ ≃ ⟨x, y⟩`, `Tr⟨a⟩ ≃ ⟨x', y'⟩`, in gq2's Kummer classes over `G_k = ↥k.fixingSubgroup`:
`(x') ⌣ (y') = (x) ⌣ (y) + ((x) + (y)) ⌣ cor + N^{Ev}`.  Tau Ceti's identity pulled back along
`Φ = fixingEquivAbsGal k` through the dictionary; the summand order is `add_right_comm`. -/
theorem cup_kummerClassK_kummerClassK_eq_of_isDiagonalization :
    kummerClassK k x' ⌣[htriv] kummerClassK k y' =
      kummerClassK k x ⌣[htriv] kummerClassK k y +
        (kummerClassK k x + kummerClassK k y) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc +
          evensNormH2 htriv hUo hidx hs α hα hαc := by
  have : FiniteDimensional ↥k ↥(quadExt k δ) := finiteDimensional_quadExt_of_finrank_eq_two k δ hdeg
  have K : ∀ u : (↥k)ˣ,
      cont1F2 k.fixingSubgroup htriv (kummerClassK k u) =
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass u) :=
    fun u => (trivialF2Map_fixingEquivAbsGal_kummerClass k htriv u).symm
  have C := (trivialF2Map_galoisCor_kummerClass k δ a hβ α hαdef hdeg s hs htriv hUo hidx hα
    hαc).symm
  have E := (trivialF2Map_galoisEvens_kummerClass k δ a hβ α hαdef hdeg s hs htriv hUo hidx hα
    hαc).symm
  apply (cont2F2 k.fixingSubgroup htriv).injective
  calc cont2F2 k.fixingSubgroup htriv (kummerClassK k x' ⌣[htriv] kummerClassK k y')
      = (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
          (cont1F2 k.fixingSubgroup htriv (kummerClassK k x'))
          (cont1F2 k.fixingSubgroup htriv (kummerClassK k y')) :=
        cont2F2_trivialCupPairing k.fixingSubgroup htriv _ _
    _ = (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
          (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x'))
          (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y')) := by simp only [K]
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x') (TauCeti.kummerClass y')) :=
        (trivialF2Map_cup_one_one _ _ _).symm
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
              (TauCeti.kummerClass x) (TauCeti.kummerClass y) +
            TauCeti.galoisEvens ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) hdeg
              (TauCeti.kummerClass a) +
            (TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
              (TauCeti.kummerClass x + TauCeti.kummerClass y)
              (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
                (TauCeti.kummerClass a))) :=
        congrArg (fun z => TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2 z)
          (cup_kummerClass_kummerClass_eq_add_galoisEvens_add_cup k δ a hxy hx'y' hdeg)
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
              (TauCeti.kummerClass x) (TauCeti.kummerClass y) +
            TauCeti.galoisEvens ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) hdeg
              (TauCeti.kummerClass a)) +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x + TauCeti.kummerClass y)
            (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
              (TauCeti.kummerClass a))) := map_add _ _ _
    _ = TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x) (TauCeti.kummerClass y)) +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          (TauCeti.galoisEvens ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) hdeg
            (TauCeti.kummerClass a)) +
        TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x + TauCeti.kummerClass y)
            (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
              (TauCeti.kummerClass a))) :=
        congrArg (· + TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 2
          ((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup ↥k)).cup 1 1
            (TauCeti.kummerClass x + TauCeti.kummerClass y)
            (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
              (TauCeti.kummerClass a)))) (map_add _ _ _)
    _ = (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x))
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y)) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x + TauCeti.kummerClass y))
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
              (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
                (TauCeti.kummerClass a))) := by
        simp only [trivialF2Map_cup_one_one, E]
    _ = (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x))
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y)) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x) +
              TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y))
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
              (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
                (TauCeti.kummerClass a))) :=
        congrArg (fun z => (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass x))
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1 (TauCeti.kummerClass y)) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1 z
            (TauCeti.trivialF2Map (fixingEquivAbsGal k : k.fixingSubgroup →ₜ* TauCeti.AbsoluteGaloisGroup k) 1
              (TauCeti.galoisCor ↥k ↥(quadExt k δ) (layerEmb k (quadExt k δ)) 1
                (TauCeti.kummerClass a)))) (map_add _ _ _)
    _ = (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k x))
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k y)) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k x) +
              cont1F2 k.fixingSubgroup htriv (kummerClassK k y))
            (cont1F2 k.fixingSubgroup htriv (corH1 htriv hUo hidx hs α hα hαc)) := by
        simp only [K, C]
    _ = (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k x))
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k y)) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k x + kummerClassK k y))
            (cont1F2 k.fixingSubgroup htriv (corH1 htriv hUo hidx hs α hα hαc)) :=
        congrArg (fun z => (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k x))
            (cont1F2 k.fixingSubgroup htriv (kummerClassK k y)) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1 z
            (cont1F2 k.fixingSubgroup htriv (corH1 htriv hUo hidx hs α hα hαc)))
          (map_add _ _ _).symm
    _ = cont2F2 k.fixingSubgroup htriv (kummerClassK k x ⌣[htriv] kummerClassK k y) +
          cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc) +
          cont2F2 k.fixingSubgroup htriv
            ((kummerClassK k x + kummerClassK k y) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc) := by
        simp only [cont2F2_trivialCupPairing]
    _ = cont2F2 k.fixingSubgroup htriv
          (kummerClassK k x ⌣[htriv] kummerClassK k y +
            (kummerClassK k x + kummerClassK k y) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc +
              evensNormH2 htriv hUo hidx hs α hα hαc) :=
        (add_right_comm _ _ _).trans
          ((map_add (cont2F2 k.fixingSubgroup htriv)
              (kummerClassK k x ⌣[htriv] kummerClassK k y +
                (kummerClassK k x + kummerClassK k y) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc)
              (evensNormH2 htriv hUo hidx hs α hα hαc)).trans
            (congrArg (· + cont2F2 k.fixingSubgroup htriv (evensNormH2 htriv hUo hidx hs α hα hαc))
              (map_add (cont2F2 k.fixingSubgroup htriv)
                (kummerClassK k x ⌣[htriv] kummerClassK k y)
                ((kummerClassK k x + kummerClassK k y) ⌣[htriv]
                  corH1 htriv hUo hidx hs α hα hαc)))).symm

end Diagonalizations

-- The binders are the field's, verbatim; `hβ0` is not needed (the Tau Ceti side derives `r ≠ 0`
-- from `r ^ 2 = σ a`), so the unused-variable linter is silenced for this one declaration.
set_option linter.unusedVariables false in
/-- **B9: the relative Stiefel–Whitney identity over finite dyadic bases**, the
`relativeStiefelWhitney_dyadic` field of `GQ2.LiteratureInputs`, from Tau Ceti. -/
theorem relativeStiefelWhitney_dyadic_tauceti
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (d : (↥k)ˣ) (δ β : AlgebraicClosure ℚ_[2])
    (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
    (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
    (a : (↥(quadExt k δ))ˣ)
    (hβ : β ^ 2 = ((a : ↥(quadExt k δ)) : AlgebraicClosure ℚ_[2]))
    (hβ0 : β ≠ 0)
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (s : k.fixingSubgroup)
    (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup) → ZMod 2)
    (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
        ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hα : ∀ g h, α (g * h) = α g + α h)
    (hαc : Continuous α) :
    (swOne k (traceFormTwisted k δ ↑a) =
        swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc) ∧
      (swTwo k htriv (traceFormTwisted k δ ↑a) =
        swTwo k htriv (traceFormOne k δ) +
          swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc +
            evensNormH2 htriv hUo hidx hs α hα hαc) := by
  have : FiniteDimensional ↥k ↥(quadExt k δ) := finiteDimensional_quadExt_of_finrank_eq_two k δ hdeg
  -- the chosen diagonalizations `Tr⟨1⟩ ≃ ⟨x, y⟩`, `Tr⟨a⟩ ≃ ⟨x', y'⟩` of gq2's `swOne`/`swTwo`
  have hex1 : ∃ x y : (↥k)ˣ, IsDiagonalization k (traceFormOne k δ) x y :=
    ⟨_, _, traceFormOne_isDiagonalization k d hδ hdeg⟩
  have hexa : ∃ x y : (↥k)ˣ, IsDiagonalization k (traceFormTwisted k δ ↑a) x y :=
    exists_isDiagonalization_traceFormTwisted k δ hdeg a
  rw [swOne_eq_of_exists k _ hexa, swOne_eq_of_exists k _ hex1, swTwo_eq_of_exists k htriv _ hexa,
    swTwo_eq_of_exists k htriv _ hex1]
  exact ⟨kummerClassK_add_kummerClassK_eq_add_corH1_of_isDiagonalization k δ a
      (isDiagonalization_choose k _ hex1) (isDiagonalization_choose k _ hexa) hdeg hβ s hs htriv
      hUo hidx α hαdef hα hαc,
    cup_kummerClassK_kummerClassK_eq_of_isDiagonalization k δ a
      (isDiagonalization_choose k _ hex1) (isDiagonalization_choose k _ hexa) hdeg hβ s hs htriv
      hUo hidx α hαdef hα hαc⟩

end GQ2.TauCetiBridge
