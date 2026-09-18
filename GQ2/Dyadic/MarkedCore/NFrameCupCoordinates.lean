import GQ2.Dyadic.MarkedCore.NFrameMatrixLift
import GQ2.Dyadic.MarkedCore.NInitialCupDepth
import GQ2.Dyadic.Instances.DNAutomorphismCup

/-!
# The full frame cup condition and actual free reduced coordinates

The semantic cup-isometry predicate quantifies over every continuous mod-two
character of the actual full N frame. It does not assume a group lift or a
matrix realization. Coordinate characters of this frame pull back to the
reduced ordinary coordinates of the free pro-two group, including coordinate
zero (the torsion character). Consequently the chosen free lift of a frame
cup isometry has exactly the all-rank row-cup equality used by the initial
degree-two relator calculation.
-/

namespace GQ2.Dyadic.MarkedCore
noncomputable section
open GQ2 GQ2.SectionThree Multiplicative GQ2.Dyadic.EvenModel
open GQ2.Dyadic.Instances.DNAutomorphismCup
open scoped GQ2.SectionThree.TopAbInstances

/-- The actual canonical columns of the full topological abelianization. -/
def nFrameCanonicalMark {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (i : Fin (coreRank h)) : NFrameModel h :=
  nPhiHom ha h (abMk (dnGen alpha h i))

/-- Full mod-two cup preservation, stated on actual continuous frame
characters. There is no orientation condition here; it is a separate input
to the eventual group-lifting theorem. No identity-handle condition occurs. -/
def NFrameCupIsometry {alpha h : ℕ} (ha : 2 ≤ alpha)
    (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) : Prop :=
  ∀ c d : ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2)),
    evenCupForm (fun i => toAdd (c (phi (nFrameCanonicalMark ha h i))))
        (fun i => toAdd (d (phi (nFrameCanonicalMark ha h i)))) =
      evenCupForm (fun i => toAdd (c (nFrameCanonicalMark ha h i)))
        (fun i => toAdd (d (nFrameCanonicalMark ha h i)))

private theorem nFrameCoordinate_head_relation {alpha h : ℕ} (ha : 2 ≤ alpha)
    (i : Fin (coreRank h)) :
    (ofAdd (if (0 : Fin (coreRank h)) = i then (1 : ZMod 2) else 0)) ^
      (2 + 2 ^ alpha) = 1 := by
  have hs : ∀ z : Multiplicative (ZMod 2), z ^ 2 = 1 := by decide
  obtain ⟨a, rfl⟩ : ∃ a, alpha = a+1 := ⟨alpha-1, by omega⟩
  rw [show 2+2^(a+1) = 2*(1+2^a) by ring, pow_mul, hs, one_pow]

/-- Coordinate i on the full frame, including its torsion coordinate, as a
genuine continuous F2 character. -/
def nFrameModTwoCoordinate {alpha : ℕ} (ha : 2 ≤ alpha) (h : ℕ)
    (i : Fin (coreRank h)) :
    ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2)) :=
  (nCoordHom alpha h isProP_two_multZMod2
    (fun j => ofAdd (if j=i then (1 : ZMod 2) else 0))
    (nFrameCoordinate_head_relation ha i)).comp
      ⟨(nFrameExists_phiEquiv ha h).symm.toMulEquiv.toMonoidHom,
        (nFrameExists_phiEquiv ha h).symm.continuous_toFun⟩

theorem nFrameModTwoCoordinate_canonicalMark {alpha : ℕ} (ha : 2 ≤ alpha)
    (h : ℕ) (i j : Fin (coreRank h)) :
    toAdd (nFrameModTwoCoordinate ha h i (nFrameCanonicalMark ha h j)) =
      if j=i then 1 else 0 := by
  change toAdd (nCoordHom alpha h isProP_two_multZMod2
    (fun k => ofAdd (if k=i then (1 : ZMod 2) else 0))
    (nFrameCoordinate_head_relation ha i)
    ((nFrameExists_phiEquiv ha h).symm
      (nFrameExists_phiEquiv ha h (abMk (dnGen alpha h j))))) = _
  rw [ContinuousMulEquiv.symm_apply_apply, nCoordHom_gen, toAdd_ofAdd]

def freeTwoReducedCoordinate (N : ℕ) (i : Fin N) :
    ContinuousMonoidHom (FreeTwoRank N : Type) (Multiplicative (ZMod 2)) where
  toMonoidHom := (AddMonoidHom.toMultiplicative nRed.toAddMonoidHom).comp
    (freeTwoCoordinate N i).toMonoidHom
  continuous_toFun := continuous_ofAdd.comp
    (continuous_nRed.comp (continuous_toAdd.comp (freeTwoCoordinate N i).continuous))

/-- Exact pullback on every free-group element, not just on generators. -/
theorem nFrameModTwoCoordinate_freeNFrameProjection {alpha : ℕ} (ha : 2 ≤ alpha)
    (h : ℕ) (i : Fin (coreRank h)) (x : FreeTwoRank (coreRank h)) :
    toAdd (nFrameModTwoCoordinate ha h i (freeNFrameProjection ha h x)) =
      nRed (toAdd (freeTwoCoordinate (coreRank h) i x)) := by
  have he : (nFrameModTwoCoordinate ha h i).comp (freeNFrameProjection ha h) =
      freeTwoReducedCoordinate (coreRank h) i := by
    apply presPro2_hom_ext
    intro j
    apply toAdd.injective
    change toAdd (nFrameModTwoCoordinate ha h i
      (freeNFrameProjection ha h (freeTwoRankGen (coreRank h) j))) =
        nRed (toAdd (freeTwoCoordinate (coreRank h) i (freeTwoRankGen (coreRank h) j)))
    rw [freeNFrameProjection_gen]
    change toAdd (nFrameModTwoCoordinate ha h i (nFrameCanonicalMark ha h j)) = _
    rw [nFrameModTwoCoordinate_canonicalMark, freeTwoCoordinate_gen, toAdd_ofAdd]
    split_ifs <;> simp
  exact congrArg (fun f : ContinuousMonoidHom _ _ => toAdd (f x)) he

/-- Coordinate form of the semantic cup condition for any tuple projecting
to the prescribed actual frame columns. This is the row-vector variance
`Abar G Abar^T=G`, not its incorrectly transposed alternative. -/
theorem NFrameCupIsometry.reducedRows_of_projection {alpha h : ℕ} {ha : 2 ≤ alpha}
    {phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)}
    (hcup : NFrameCupIsometry ha phi)
    (m : Fin (coreRank h) → FreeTwoRank (coreRank h))
    (hproj : ∀ k, freeNFrameProjection ha h (m k) = phi (nFrameCanonicalMark ha h k))
    (i j : Fin (coreRank h)) :
    evenCupForm (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) i (m k))))
        (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) j (m k)))) =
      evenCupForm (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) i
          (freeTwoRankGen (coreRank h) k))))
        (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) j
          (freeTwoRankGen (coreRank h) k)))) := by
  have hc := hcup (nFrameModTwoCoordinate ha h i) (nFrameModTwoCoordinate ha h j)
  have hleft (l k : Fin (coreRank h)) :
      toAdd (nFrameModTwoCoordinate ha h l (phi (nFrameCanonicalMark ha h k))) =
        nRed (toAdd (freeTwoCoordinate (coreRank h) l (m k))) := by
    rw [← hproj, nFrameModTwoCoordinate_freeNFrameProjection]
  have hright (l k : Fin (coreRank h)) :
      toAdd (nFrameModTwoCoordinate ha h l (nFrameCanonicalMark ha h k)) =
        nRed (toAdd (freeTwoCoordinate (coreRank h) l (freeTwoRankGen (coreRank h) k))) := by
    rw [nFrameModTwoCoordinate_canonicalMark, freeTwoCoordinate_gen, toAdd_ofAdd]
    split_ifs <;> simp
  simpa only [hleft, hright] using hc

theorem NFrameCupIsometry.reducedRows_nFrameLiftEquiv {alpha h : ℕ} {ha : 2 ≤ alpha}
    {phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)}
    (hcup : NFrameCupIsometry ha phi) (i j : Fin (coreRank h)) :
    evenCupForm
        (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) i
          (nFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) k)))))
        (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) j
          (nFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) k))))) =
      evenCupForm
        (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) i (freeTwoRankGen (coreRank h) k))))
        (fun k => nRed (toAdd (freeTwoCoordinate (coreRank h) j (freeTwoRankGen (coreRank h) k)))) := by
  apply hcup.reducedRows_of_projection
  intro k
  rw [nFrameLiftEquiv_projection, freeNFrameProjection_gen]
  rfl

/-- The exact reduced-row interface for the initial relator-depth theorem. -/
theorem nFrameLiftEquiv_cup {alpha h : ℕ} {ha : 2 ≤ alpha}
    {phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)}
    (hcup : NFrameCupIsometry ha phi) (i j : Fin (coreRank h)) :
    evenCupForm
        (NInitialCupDepth.reducedRows
          (fun k => nFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) k)) i)
        (NInitialCupDepth.reducedRows
          (fun k => nFrameLiftEquiv ha h phi (freeTwoRankGen (coreRank h) k)) j) =
      evenCupForm
        (NInitialCupDepth.reducedRows (freeTwoRankGen (coreRank h)) i)
        (NInitialCupDepth.reducedRows (freeTwoRankGen (coreRank h)) j) :=
  hcup.reducedRows_nFrameLiftEquiv i j

#print axioms nFrameCanonicalMark
#print axioms NFrameCupIsometry
#print axioms nFrameModTwoCoordinate
#print axioms nFrameModTwoCoordinate_canonicalMark
#print axioms freeTwoReducedCoordinate
#print axioms nFrameModTwoCoordinate_freeNFrameProjection
#print axioms NFrameCupIsometry.reducedRows_of_projection
#print axioms NFrameCupIsometry.reducedRows_nFrameLiftEquiv
#print axioms nFrameLiftEquiv_cup

end
end GQ2.Dyadic.MarkedCore
