/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstraction
import GQ2.Dyadic.Instances.EvenNLabWitness

/-!
# The image-relative sharp filtration and the even-degree row supply  (W51-EV4A)

Ticket EV-4a of `docs/dyadic/ev4b-stage-abstraction.md` (board section 4; architectural
context in sections 2.1(b) and 3).  The committed odd-degree endpoints
`oddDegreeGalKSq_sharpCharacterFiltrationExact` and
`oddDegreeGalKSq_sharpExactLevelFibreLiftSupply` consume surjectivity of `chiCycKTwo`,
which fails in even degree.  This file replaces the surjectivity input by an
*image-relative* filtration identity, produces the row supply from it, recovers the odd
degree case, and then settles the even-degree question the board left open.

## The identity

For any continuous `chi : G → ℤ₂ˣ` the ambient statement of the sharp seam is

`chi(λ_m(G)) = im chi ⊓ (1 + 2^(m+1) ℤ₂)`   (`ImageRelSharpFiltrationExact`),

whose `≤` half is unconditional (`imageRel_map_le`) and whose `≥` half is the whole
content.  At surjective `chi` it *is* the committed `SharpCharacterFiltrationExact`
(`imageRel_iff_sharpCharacterFiltrationExact_of_surjective`), and it implies the
row-relative supply `RowExactLevelFibreLiftSupply v G chi` for every table whose values lie
in `im chi` (`evenRow_rowSupply_of_imageRel`).  Conversely — and this is what makes the
identity the right seam rather than one sufficient condition among many — the supply at a
single row value in `im chi` *forces* the `≥` half at every level
(`evenRow_imageRel_le_of_rowSupply`, `evenRow_rowSupply_iff`).

## The even-degree finding (headline)

**The `≥` half is false at the even-degree images, and therefore so is
`RowExactLevelFibreLiftSupply` itself, for every table, as soon as `α ≥ 3.**  The reason is
structural: the lower two-central series does not restrict to subgroups.  Writing
`U = im chi`, the supply needs `U ⊓ (1 + 2^(m+1)ℤ₂) ≤ λ_m(U)`, while for the committed even
images

* `imChiN α = ⟨-(1+2^α)⁻¹⟩` and `imChiM α = ⟨-1, (1-2^α)⁻¹⟩ = {±1}·(1+2^αℤ₂)`

one has `λ_m(U) ⊆ 1 + 2^(m+α-1)ℤ₂`: the sharp seam is short by exactly `α - 1` digits.  At
`α = 2` nothing is lost (and indeed `imChiM 2 = ⊤`, `imChiN 2 = ⟨-5⟩`); from `α = 3` on the
supply fails at the very first level that uses it.  §5 proves this: from
`mUnit α ∈ Set.range chi` and `im chi ≤ {u ≡ ±1 mod 2^α}` the supply is refuted at `m = 2`
(the witness is the row unit `mUnit α` itself), and from `nUnit α ∈ Set.range chi` at
`m = 3` (witness `(nUnit α)^2`).  No compactness, no campaign axioms, no surjectivity: the
refutation is a two-line 2-adic valuation count once the depth bound is in place.

## The corrected seam (what EV-3f should consume)

§6 supplies the repaired interface, parametrised by the missing digits:

* `evenSharp_deepChiLevel chi m s H` — the depth-`s` character shadow
  `Q_m →* (ZMod 2^(m+s))ˣ`, defined exactly when `chi(λ_m(G)) ≤ 1 + 2^(m+s)ℤ₂`, which
  `evenSharp_map_le_deep_of_modPair` supplies at `s = α - 1` for both even images;
* `ImageRelDeepFiltrationExact s` and `EvenRowDeepFibreLiftSupply s`, with
  `evenRow_deepRowSupply_of_imageRelDeep` the depth-`s` analogue of §2 and
  `evenRow_rowSupply_of_deepRowSupply_one` the bridge back to the committed
  `RowExactLevelFibreLiftSupply` at `s = 1`.

So the even stage climb keeps the whole architecture; what it must strengthen is the
fresh-digit station, which has to deliver `α - 1` digits rather than one.  That is the
single interface change EV-3f inherits from this ticket.

## Numbering

1. the image-relative filtration and its unconditional half;
2. the row supply, and the converse that makes it an iff;
3. odd-degree recovery and the pins;
4. the four row-value memberships, with the branch conditions stated where they bite;
5. the even-degree obstruction;
6. the depth-shifted corrected seam.
-/

namespace GQ2.Dyadic.EvenRowSupply

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.LSquare.SqCyclotomicStageTuple (sharpChiLevel sharpChiLevel_levelMk
  SharpUnitsFiltrationExact sharpUnitsFiltrationExact SharpCharacterFiltrationExact
  SharpExactLevelFibreLiftSupply)

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The image-relative sharp filtration

`SharpCharacterFiltrationExact` reads `chi(λ_m(G)) = 1 + 2^(m+1)ℤ₂`, which forces
`chi` to be surjective onto `1 + 2^(m+1)ℤ₂` at every level and is therefore unavailable in
even degree.  Intersecting the right-hand side with the image is the minimal repair. -/

section ImageRelative

variable {n : ℕ} (v : Fin n → ℤ_[2]ˣ)
variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (chi : ContinuousMonoidHom G ℤ_[2]ˣ)

/-- **The image-relative sharp filtration identity.**  The even-degree replacement for
`SharpCharacterFiltrationExact`: the character carries the lower two-central series onto the
part of the sharp principal-unit filtration that the character can reach at all.  For
surjective `chi` the intersection is vacuous and this is the committed statement
(`imageRel_iff_sharpCharacterFiltrationExact_of_surjective`). -/
structure ImageRelSharpFiltrationExact : Prop where
  /-- `chi(λ_m) = im chi ⊓ (1 + 2^(m+1)ℤ₂)` for every `m ≥ 2`. -/
  map_twoCentralSeries_eq_range_inf_succKernel : ∀ m, 2 ≤ m →
    (twoCentralSeries G m).map chi.toMonoidHom =
      MonoidHom.range chi.toMonoidHom ⊓
        (Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom).ker

variable {G chi}

/-- The unconditional half of the identity: the character image of a layer lands in the image
and, one digit sharper than the index, in the principal-unit filtration.  This is
`map_twoCentralSeries_le` followed by the modulus lemma `twoCentralSeries_units_le`. -/
theorem imageRel_map_le (m : ℕ) (hm : 2 ≤ m) :
    (twoCentralSeries G m).map chi.toMonoidHom ≤
      MonoidHom.range chi.toMonoidHom ⊓
        (Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom).ker := by
  rintro _ ⟨g, hg, rfl⟩
  refine Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩
  exact twoCentralSeries_units_le m hm
    (map_twoCentralSeries_le chi.toMonoidHom chi.continuous_toFun m ⟨g, hg, rfl⟩)

/-- Only the nontrivial half has to be supplied. -/
theorem imageRel_of_le
    (H : ∀ m, 2 ≤ m →
      MonoidHom.range chi.toMonoidHom ⊓
          (Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom).ker ≤
        (twoCentralSeries G m).map chi.toMonoidHom) :
    ImageRelSharpFiltrationExact G chi :=
  ⟨fun m hm ↦ le_antisymm (imageRel_map_le m hm) (H m hm)⟩

/-- At a surjective character the image-relative identity is literally the committed
`SharpCharacterFiltrationExact`: the intersection with `im chi = ⊤` does nothing.  This is
the specialisation demanded by the ticket's odd-degree regression. -/
theorem imageRel_iff_sharpCharacterFiltrationExact_of_surjective
    (hchi : Function.Surjective chi) :
    ImageRelSharpFiltrationExact G chi ↔ SharpCharacterFiltrationExact G chi := by
  have hrange : MonoidHom.range chi.toMonoidHom = ⊤ :=
    MonoidHom.range_eq_top.mpr hchi
  constructor
  · exact fun H ↦ ⟨fun m hm ↦ by
      rw [H.map_twoCentralSeries_eq_range_inf_succKernel m hm, hrange, top_inf_eq]⟩
  · exact fun H ↦ ⟨fun m hm ↦ by
      rw [H.map_twoCentralSeries_eq_succKernel m hm, hrange, top_inf_eq]⟩

end ImageRelative

/-! ## §2 The row supply, image-relatively

The stage machinery lifts only at the row values (board section 2.1(b)), so the supply it
needs is `RowExactLevelFibreLiftSupply`.  Its exact arithmetic content is the `≥` half of
§1 restricted to the rows, and §2 proves that in both directions. -/

section RowSupply

variable {n : ℕ} {v : Fin n → ℤ_[2]ˣ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- **The even-degree row supply.**  Image-relative sharp exactness supplies exact
representatives in every sharp level coset whose fresh digit matches a row value lying in
the image.  The proof is the committed `toSharpExactLevelFibreLiftSupply` with the extra
observation that the correcting unit `(chi g)⁻¹ * v i` is automatically in the image once
`v i` is: this is precisely why intersecting with `im chi` costs nothing at the rows. -/
theorem evenRow_rowSupply_of_imageRel (H : ImageRelSharpFiltrationExact G chi)
    (hv : ∀ i, v i ∈ Set.range chi) :
    RowExactLevelFibreLiftSupply v G chi := by
  constructor
  intro m hm i q hq
  obtain ⟨g, rfl⟩ := levelMk_surjective G m q
  have hmod : Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom (chi g) =
      Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom (v i) := by
    simpa only [sharpChiLevel_levelMk] using hq
  obtain ⟨y, hy⟩ := hv i
  have hdker : (chi g)⁻¹ * v i ∈
      (Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmod, inv_mul_cancel]
  have hdrange : (chi g)⁻¹ * v i ∈ MonoidHom.range chi.toMonoidHom := by
    refine ⟨g⁻¹ * y, ?_⟩
    show chi (g⁻¹ * y) = (chi g)⁻¹ * v i
    rw [map_mul, map_inv, hy]
  have hmem : (chi g)⁻¹ * v i ∈ (twoCentralSeries G m).map chi.toMonoidHom := by
    rw [H.map_twoCentralSeries_eq_range_inf_succKernel m hm]
    exact Subgroup.mem_inf.mpr ⟨hdrange, hdker⟩
  obtain ⟨r, hr, hrd⟩ := hmem
  have hrone : levelMk G m r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
  refine ⟨g * r, ?_, ?_⟩
  · change chi r = (chi g)⁻¹ * v i at hrd
    rw [map_mul, hrd]
    group
  · rw [map_mul, hrone, mul_one]

/-- **The converse.**  A single row value in the image already forces the nontrivial half of
the image-relative identity at every level: given `d` in `im chi ⊓ (1 + 2^(m+1)ℤ₂)`, apply
the supply to the coset of a preimage of `v i * d⁻¹`.  Hence the supply is not merely
implied by the filtration identity, it is equivalent to it — there is no weaker sufficient
arithmetic input hiding behind the row restriction. -/
theorem evenRow_imageRel_le_of_rowSupply (H : RowExactLevelFibreLiftSupply v G chi)
    (i : Fin n) (hvi : v i ∈ Set.range chi) (m : ℕ) (hm : 2 ≤ m) :
    MonoidHom.range chi.toMonoidHom ⊓
        (Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom).ker ≤
      (twoCentralSeries G m).map chi.toMonoidHom := by
  intro d hd
  obtain ⟨hdrange, hdker⟩ := Subgroup.mem_inf.mp hd
  obtain ⟨y, hy⟩ := hvi
  obtain ⟨c, hc⟩ := hdrange
  -- The test element `y * c⁻¹` has character value `v i * d⁻¹`, hence the sharp shadow of
  -- the row `v i`; the supply returns an exact representative differing from it by `d`.
  have hcd : chi c = d := hc
  have hchig : chi (y * c⁻¹) = v i * d⁻¹ := by
    rw [map_mul, map_inv, hy, hcd]
  obtain ⟨x, hxchi, hx⟩ := H.lift m hm i (levelMk G m (y * c⁻¹)) (by
    rw [sharpChiLevel_levelMk, hchig, map_mul, map_inv,
      MonoidHom.mem_ker.mp hdker, inv_one, mul_one])
  have hone : levelMk G m ((y * c⁻¹)⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, ← hx, inv_mul_cancel]
  refine ⟨(y * c⁻¹)⁻¹ * x, (QuotientGroup.eq_one_iff _).mp hone, ?_⟩
  show chi ((y * c⁻¹)⁻¹ * x) = d
  rw [map_mul, map_inv, hchig, hxchi]
  group

/-- **The seam, exactly.**  For a row table with values in the image, the row supply is
equivalent to the nontrivial half of the image-relative filtration identity.  This is the
statement the even lane has to decide, and §5 decides it negatively. -/
theorem evenRow_rowSupply_iff (hv : ∀ i, v i ∈ Set.range chi) (i₀ : Fin n) :
    RowExactLevelFibreLiftSupply v G chi ↔
      ∀ m, 2 ≤ m →
        MonoidHom.range chi.toMonoidHom ⊓
            (Units.map (PadicInt.toZModPow (m + 1)).toMonoidHom).ker ≤
          (twoCentralSeries G m).map chi.toMonoidHom :=
  ⟨fun H m hm ↦ evenRow_imageRel_le_of_rowSupply H i₀ (hv i₀) m hm,
    fun H ↦ evenRow_rowSupply_of_imageRel (imageRel_of_le H) hv⟩

end RowSupply

/-! ## §3 Odd-degree recovery

The ticket's regression: the image-relative machinery, specialised to a surjective
character, re-derives the committed odd-degree endpoints, with statements identical to the
committed ones and (see the axiom pins) equal prints. -/

section OddRecovery

variable {n : ℕ}
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ}

/-- For a continuous epimorphism from a compact group the image-relative identity reduces,
exactly as the committed `SharpCharacterFiltrationExact.of_surjective` does, to the
target-side unit-filtration equality. -/
theorem imageRel_of_surjective (hchi : Function.Surjective chi)
    (Hunits : SharpUnitsFiltrationExact) :
    ImageRelSharpFiltrationExact G chi :=
  (imageRel_iff_sharpCharacterFiltrationExact_of_surjective hchi).mpr
    (SharpCharacterFiltrationExact.of_surjective hchi Hunits)

/-- At a surjective character every row value is in the image, so the row supply holds for
*every* table.  This is `rowSupply_of_sharpSupply` re-proved through §1–§2. -/
theorem evenRow_rowSupply_of_surjective (v : Fin n → ℤ_[2]ˣ)
    (hchi : Function.Surjective chi) :
    RowExactLevelFibreLiftSupply v G chi :=
  evenRow_rowSupply_of_imageRel
    (imageRel_of_surjective hchi sharpUnitsFiltrationExact) fun i ↦ hchi (v i)

end OddRecovery

section OddField

open GQ2.Dyadic.LSquare (chiCycKTwo_surjective_of_odd_finrank)
open GQ2.Dyadic.LSquare.SqCyclotomicStageTuple (oddDegreeGalKSq_sharpCharacterFiltrationExact
  oddDegreeGalKSq_sharpExactLevelFibreLiftSupply)

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The odd-degree field endpoint in image-relative form.  Its content is the committed
`oddDegreeGalKSq_sharpCharacterFiltrationExact`; the point of the pin is that the even lane's
weaker interface is genuinely weaker, and that nothing is lost by moving to it. -/
theorem imageRel_oddDegreeGalKSq {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    ImageRelSharpFiltrationExact (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  (imageRel_iff_sharpCharacterFiltrationExact_of_surjective
      (chiCycKTwo_surjective_of_odd_finrank K B hodd)).mpr
    (oddDegreeGalKSq_sharpCharacterFiltrationExact B hodd)

/-- **The odd-degree recovery.**  Every row table, at odd degree, through the image-relative
route. -/
theorem evenRow_oddDegreeGalKSq_rowSupply {n : ℕ} (v : Fin n → ℤ_[2]ˣ)
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    RowExactLevelFibreLiftSupply v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) :=
  evenRow_rowSupply_of_imageRel (imageRel_oddDegreeGalKSq B hodd)
    fun i ↦ chiCycKTwo_surjective_of_odd_finrank K B hodd (v i)

/-- Statement pin (LSq house pattern): the image-relative odd-degree row supply and the
committed route through
`rowSupply_of_sharpSupply ∘ oddDegreeGalKSq_sharpExactLevelFibreLiftSupply` inhabit the
*same* proposition — the `rfl` typechecks only if the two statements agree on the nose,
instances included. -/
theorem evenRow_pin_oddDegreeGalKSq_rowSupply {n : ℕ} (v : Fin n → ℤ_[2]ˣ)
    {R : LocalReciprocity} (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    evenRow_oddDegreeGalKSq_rowSupply v B hodd =
      rowSupply_of_sharpSupply v (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))
        (oddDegreeGalKSq_sharpExactLevelFibreLiftSupply B hodd) :=
  rfl

end OddField

end

end GQ2.Dyadic.EvenRowSupply
