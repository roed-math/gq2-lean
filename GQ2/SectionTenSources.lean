import GQ2.SectionTen
import GQ2.BoundaryMapsWitness

/-!
# §10 — the per-source discharge of Lemma 10.1's hypotheses  (P-18d)

`SectionTen.card_contSurj_eq` (Lemma 10.1, counting form) is stated Γ-generically over the two
hypotheses on a boundary map `b`:

* `htame : Function.Surjective (tameCoord b)` — the tame coordinate `pr₁ ∘ b` is onto `Ttame`;
* `hwild : IsProP 2 (tameCoord b).toMonoidHom.ker` — its kernel (the wild inertia) is pro-2.

This file discharges both for the two real sources, so P-18e's `eq_154` can invoke
`card_contSurj_eq` twice.  Since `tameCoord (B.bA) = B.tameA` and `tameCoord (B.bF) = B.tameF`
(`bA_apply_coe`/`bF_apply_coe`):

* **`G_ℚ₂` (F-side) — generic**, straight from the `BoundaryMaps` clauses `tameF_surjective`
  (surjectivity) and `wild_isProP` (`= W_F = O₂(G_ℚ₂)` pro-2, Lemma 3.3).
* **`Γ_A` (A-side) — for the concrete `boundaryMapsWitness`**: `tameA := φ_A` is surjective
  (`phiA_surjective`), and `ker φ_A = W_A` (the wild core) because the descent
  `φ_A / W_A = ψ_W` is injective (`tameAEquiv`, Prop 3.2's `Γ_A`-side iso), which is pro-2 by
  `isProP_wildPart` (P-04).  So the A-side needs **no `BoundaryMaps` amendment** — the witness
  supplies it.
-/

namespace GQ2

namespace SectionTen

open SectionThree

/-- The tame coordinate of `b_{G_ℚ₂}` is the boundary bundle's tame component `tameF`. -/
theorem tameCoord_bF (B : BoundaryMaps) : tameCoord B.bF = B.tameF := by
  ext g; simp only [tameCoord_apply, B.bF_apply_coe]

/-- The tame coordinate of `b_{Γ_A}` is the boundary bundle's tame component `tameA`. -/
theorem tameCoord_bA (B : BoundaryMaps) : tameCoord B.bA = B.tameA := by
  ext g; simp only [tameCoord_apply, B.bA_apply_coe]

/-! ## `G_ℚ₂` (F-side): from the `BoundaryMaps` fields -/

/-- **`htame` for `G_ℚ₂`**: `tameF` is onto (`BoundaryMaps.tameF_surjective`). -/
theorem tameCoord_bF_surjective (B : BoundaryMaps) :
    Function.Surjective (tameCoord B.bF) := by
  rw [tameCoord_bF]; exact B.tameF_surjective

/-- **`hwild` for `G_ℚ₂`**: the wild inertia `ker tameF = O₂(G_ℚ₂)` is pro-2
(`BoundaryMaps.wild_isProP`). -/
theorem tameCoord_bF_ker_isProP (B : BoundaryMaps) :
    IsProP 2 (tameCoord B.bF).toMonoidHom.ker := by
  rw [tameCoord_bF]; exact B.wild_isProP

/-! ## `Γ_A` (A-side): the kernel of `φ_A` -/

/-- **`ker φ_A = W_A`.**  `⊇` is `wildPartB_le_ker_phiA`; `⊆` because the descent
`ψ_W = φ_A / W_A` is injective — it is the underlying map of the Prop-3.2 iso `tameAEquiv`. -/
theorem ker_phiA : phiA.toMonoidHom.ker = wildPartB := by
  refine le_antisymm (fun x hx => ?_) wildPartB_le_ker_phiA
  have h1 : psiW (quotientMk wildPartB x) = 1 := by
    rw [show psiW (quotientMk wildPartB x) = phiA x from quotientLift_quotientMk _ _ _ _]
    exact MonoidHom.mem_ker.mp hx
  have h2 : quotientMk wildPartB x = 1 :=
    tameAEquiv.injective (h1.trans (map_one psiW).symm)
  exact (quotientMk_eq_one_iff _).mp h2

/- The concrete `Γ_A` witness `boundaryMapsWitness` (Prop 3.14) lives over `AbsGalQ2`, so its
users carry the tower's standing `AbsGalQ2` topology instances. -/
section Witness

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **`htame` for `Γ_A`** (the witness `boundaryMapsWitness`): `tameA = φ_A` is onto
(`phiA_surjective`). -/
theorem tameCoord_bA_surjective :
    Function.Surjective (tameCoord boundaryMapsWitness.bA) := by
  rw [tameCoord_bA]; exact phiA_surjective

/-- **`hwild` for `Γ_A`** (the witness): the wild inertia `ker tameA = ker φ_A = W_A` is pro-2
(`isProP_wildPart`, P-04). -/
theorem tameCoord_bA_ker_isProP :
    IsProP 2 (tameCoord boundaryMapsWitness.bA).toMonoidHom.ker := by
  rw [tameCoord_bA]
  show IsProP 2 phiA.toMonoidHom.ker
  rw [ker_phiA]; exact isProP_wildPart

end Witness

end SectionTen

end GQ2
