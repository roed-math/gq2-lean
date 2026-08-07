/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenModelDemushkin
import GQ2.Dyadic.OrientationCorrection

/-!
# EV-0c: an honest witness that the *unguarded* `NLabHypothesis` is too strong

*Status (2026-08-07).*  This file's refutation has been acted on: `NLabHypothesis`
(`GQ2/Dyadic/MarkedCore/N.lean`) now carries the orientation-canonicity guard `nIsCanonical`
that its `M` twin always had (owner memo 2026-08-05, item 3), and the theorems below are stated
against the guarded binder.  `noCanonicityGuard` recovers the pre-memo form, and
`nonempty_equiv_DM_DN_of_unguarded_nLabHypothesis` is the refutation that made the guard
necessary, kept live.

Without the guard, `NLabHypothesis α h` keys on four invariants only: Demushkin at `p = 2`,
`demushkinRank = coreRank h`, `demushkinQ = 2`, and the existence of *some* continuous character
with image `imChiN α`.  This file assembles all four for the **`M` row**.

The point is the fourth clause.  `imChiN α` is the *canonical* orientation image of `D_N`, but
the unguarded binder asks only that some character attain it, and the `M` relator is perfectly
happy to carry the `N` value table: `mRelWord` abelianizes to `m₀² · m₂^{2^α}`
(`mRelWord_comm`), and the `N` marking `coreMark 1 v 1 1` puts `1` in *both* of those slots.  So
`chiNOnDM` below is a continuous character of `D_M` with `MonoidHom.range = imChiN α`, and
`nonempty_equiv_DM_DN_of_unguarded_nLabHypothesis` concludes `D_M ≅ D_N` from the unguarded
binder alone.

That conclusion is false for the intended cores, so `NLabHypothesis` as *literally stated before
the memo* cannot be Labute's theorem: what Labute separates the two rows by is the *canonical*
orientation, and `imChiM α ≠ imChiN α` (`imChiM_ne_imChiN`, §4 below) — `−1 ∈ imChiM α` while
`imChiN α` is the procyclic closure of `⟨v⟩`, `v = −(1+2^α)⁻¹ ≡ −1 + 2^α (mod 2^{α+1})`, whose
reduction mod `2^{α+1}` is the order-two group `{1, −1 + 2^α}` and misses `−1`.  Dropping the
canonicity clause (memo §6.4 deviation (ii)) is therefore not a harmless weakening: it collapses
the two rows.

## Contents

* §1 `chiNOnDM` — the `N` value table on the `M` core, with generator-value simp lemmas.
* §2 `range_chiNOnDM` — its image is exactly `imChiN α` (the `range_chiN` argument, `M`-side).
* §3 `nonempty_equiv_DM_DN_of_nLabHypothesis` — the witness package against the guarded binder,
  and `nonempty_equiv_DM_DN_of_unguarded_nLabHypothesis`, the same package at
  `noCanonicityGuard`.  `demushkinQ (DM α h) = 2` is threaded as an explicit hypothesis: the repo
  has `demushkinQ_DM` only at `h = 0` and only from an `MDecomposition α`
  (`GQ2/Dyadic/MarkedCore/Cores.lean:1946`); there is no general-`h` `M`-frame (the `N`-side
  `demushkinQ_DN_nFrame` has no `M` counterpart).  The `h = 0` specialisation
  `nonempty_equiv_DM_DN_zero_of_nLabHypothesis` discharges it from a frame.
* §4 `imChiM_ne_imChiN` — the separation, proved through the mod-`2^{α+1}` reduction.
* §5 the `N`-side sanity pin.
-/

namespace GQ2.Dyadic.EvenNLab

noncomputable section

open GQ2 GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel

local instance evenScalarActionDM'' (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenContinuousScalarDM'' (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

local instance evenScalarActionDN'' (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenContinuousScalarDN'' (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The `N` value table on the `M` core -/

/-- **The `N`-shaped character of `D_M`**: generator values `(A, B, C₀, D) ↦ (1, v, 1, 1)` with
`v = nUnit α = −(1+2^α)⁻¹`, and `1` on every handle letter — the value table of `χ_N`, carried by
the `M` core.  It is legal there because the abelianized `M` relator `Ā²·C̄₀^{2^α}` only sees
slots `0` and `2`, and this marking is `1` at both. -/
def chiNOnDM (α h : ℕ) : ContinuousMonoidHom (DM α h : Type) ℤ_[2]ˣ :=
  mLiftHom α h isProP_two_unitsPadicInt (coreMark 1 (nUnit α) 1 1) (by
    rw [mRelWord_comm, coreMark_zero, coreMark_two, one_pow, one_pow, one_mul])

@[simp] theorem chiNOnDM_dmA (α h : ℕ) : chiNOnDM α h (dmA α h) = 1 := by
  rw [dmA, chiNOnDM, mLiftHom_gen, coreMark_zero]

@[simp] theorem chiNOnDM_dmB (α h : ℕ) : chiNOnDM α h (dmB α h) = nUnit α := by
  rw [dmB, chiNOnDM, mLiftHom_gen, coreMark_one]

@[simp] theorem chiNOnDM_dmC (α h : ℕ) : chiNOnDM α h (dmC α h) = 1 := by
  rw [dmC, chiNOnDM, mLiftHom_gen, coreMark_two]

@[simp] theorem chiNOnDM_dmD (α h : ℕ) : chiNOnDM α h (dmD α h) = 1 := by
  rw [dmD, chiNOnDM, mLiftHom_gen, coreMark_three]

@[simp] theorem chiNOnDM_handleU (α h : ℕ) (j : Fin h) :
    chiNOnDM α h (dmGen α h (handleIdxU j)) = 1 := by
  rw [chiNOnDM, mLiftHom_gen, coreMark_handleU]

@[simp] theorem chiNOnDM_handleV (α h : ℕ) (j : Fin h) :
    chiNOnDM α h (dmGen α h (handleIdxV j)) = 1 := by
  rw [chiNOnDM, mLiftHom_gen, coreMark_handleV]

/-! ## §2 Its exact image -/

/-- **The `M`-core character `chiNOnDM` has exactly the `N` classification image.**  The proof is
`range_chiN` (`GQ2/Dyadic/OrientationCorrection.lean:209`) with `dnGen`/`dn_topGen` replaced by
`dmGen`/`dm_topGen`. -/
theorem range_chiNOnDM (α h : ℕ) :
    MonoidHom.range (chiNOnDM α h).toMonoidHom = imChiN α := by
  apply le_antisymm
  · let H := Subgroup.comap (chiNOnDM α h).toMonoidHom (imChiN α)
    have hgen : Subgroup.closure (Set.range (dmGen α h)) ≤ H := by
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · change chiNOnDM α h (dmA α h) ∈ imChiN α
        simp
      · change chiNOnDM α h (dmB α h) ∈ imChiN α
        rw [chiNOnDM_dmB, imChiN]
        exact Subgroup.le_topologicalClosure
          (Subgroup.closure {(nUnit α : ℤ_[2]ˣ)})
          (Subgroup.subset_closure (Set.mem_singleton (nUnit α)))
      · change chiNOnDM α h (dmC α h) ∈ imChiN α
        simp
      · change chiNOnDM α h (dmD α h) ∈ imChiN α
        simp
      · change chiNOnDM α h (dmGen α h (handleIdxU j)) ∈ imChiN α
        simp
      · change chiNOnDM α h (dmGen α h (handleIdxV j)) ∈ imChiN α
        simp
    have hclosed : IsClosed (H : Set (DM α h : Type)) :=
      (Subgroup.isClosed_topologicalClosure _).preimage (chiNOnDM α h).continuous_toFun
    have htop : (Subgroup.closure (Set.range (dmGen α h))).topologicalClosure ≤ H :=
      Subgroup.topologicalClosure_minimal _ hgen hclosed
    rw [dm_topGen] at htop
    rintro y ⟨x, rfl⟩
    exact htop (Subgroup.mem_top x)
  · have hclosed : IsClosed (MonoidHom.range (chiNOnDM α h).toMonoidHom : Set ℤ_[2]ˣ) := by
      rw [MonoidHom.coe_range]
      exact (isCompact_range (chiNOnDM α h).continuous_toFun).isClosed
    refine Subgroup.topologicalClosure_minimal _ ?_ hclosed
    rw [Subgroup.closure_le]
    rintro _ rfl
    exact ⟨dmB α h, chiNOnDM_dmB α h⟩

/-! ## §3 The witness package -/

/-- **The honest witness package** (ticket EV-0c): the even `M` core satisfies every *invariant*
hypothesis of `NLabHypothesis α h` — Demushkin, rank `coreRank h`, `q = 2`, and a continuous
character of range exactly `imChiN α`.  The only clause it cannot meet on its own is the
orientation-canonicity guard, so granting the guard for `chiNOnDM` forces `D_M ≅ D_N`.

`demushkinQ (DM α h) = 2` is an explicit hypothesis, as the module docstring records: the repo
proves `demushkinQ (DM α 0) = 2` only from an `MDecomposition α`, and there is no general-`h`
`M`-frame to run `demushkinQ_DN_nFrame`'s argument through. -/
theorem nonempty_equiv_DM_DN_of_nLabHypothesis (α h : ℕ) (hα2 : 2 ≤ α)
    (nIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (hq : demushkinQ (DM α h : Type) = 2)
    (hLab : MarkedCore.NLabHypothesis α h nIsCanonical)
    (hcanon : nIsCanonical (DM α h : Type) (chiNOnDM α h).toMonoidHom) :
    Nonempty (ContinuousMulEquiv (DM α h : Type) (DN α h : Type)) :=
  hLab (DM α h : Type) (isDemushkin_DM α h hα2)
    (demushkinRank_DM α h (le_trans one_le_two hα2)) hq
    ⟨(chiNOnDM α h).toMonoidHom, (chiNOnDM α h).continuous_toFun, hcanon, range_chiNOnDM α h⟩

/-- **The canonicity guard dropped**: the predicate every character satisfies.  Instantiating
`NLabHypothesis` here recovers the binder exactly as it stood before the owner memo of
2026-08-05 (item 3). -/
def noCanonicityGuard :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop :=
  fun _ _ _ _ _ => True

/-- **The refutation the guard exists for.**  With canonicity dropped, `NLabHypothesis` alone
forces `D_M ≅ D_N` — a conclusion refuted unconditionally at `α ≥ 2` by `imChiM_ne_imChiN` (§4).
So the unguarded binder is not Labute's theorem, and this is why `NLabHypothesis` now carries
`nIsCanonical`. -/
theorem nonempty_equiv_DM_DN_of_unguarded_nLabHypothesis (α h : ℕ) (hα2 : 2 ≤ α)
    (hq : demushkinQ (DM α h : Type) = 2)
    (hLab : MarkedCore.NLabHypothesis α h noCanonicityGuard) :
    Nonempty (ContinuousMulEquiv (DM α h : Type) (DN α h : Type)) :=
  nonempty_equiv_DM_DN_of_nLabHypothesis α h hα2 noCanonicityGuard hq hLab trivial

/-- The `h = 0` specialisation, with the `q`-invariant discharged from MC2's rank-four `M`
frame (`GQ2/Dyadic/MarkedCore/Cores.lean:1823`).  The repo proves no `Nonempty (MDecomposition α)`
(the `phiEquiv` route is explicitly out of scope there), so the frame stays a hypothesis. -/
theorem nonempty_equiv_DM_DN_zero_of_nLabHypothesis (α : ℕ) (hα2 : 2 ≤ α)
    (nIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (B : MarkedCore.MDecomposition α)
    (hLab : MarkedCore.NLabHypothesis α 0 nIsCanonical)
    (hcanon : nIsCanonical (DM α 0 : Type) (chiNOnDM α 0).toMonoidHom) :
    Nonempty (ContinuousMulEquiv (DM α 0 : Type) (DN α 0 : Type)) :=
  nonempty_equiv_DM_DN_of_nLabHypothesis α 0 hα2 nIsCanonical (MarkedCore.demushkinQ_DM B) hLab
    hcanon

/-! ## §4 The separation `imChiM α ≠ imChiN α`

What `NLabHypothesis` drops is canonicity, and canonicity is exactly what the images see: the
*canonical* `M` image `imChiM α = ⟨−1, u⟩` contains `−1`, while `imChiN α = ⟨v⟩` does not.  The
proof is a finite-level one.  Reduce mod `2^{α+1}`.  There `v ≡ −1 + 2^α` is an involution
(`nUnit_res_sq`, from the exact level `α+1` of `v²`) and is *not* `−1` (`nUnit_res_ne_neg_one`,
from `v·(1+2^α) = −1`), so the units reducing into `{1, v}` form a closed subgroup containing
`v` and missing `−1`; `imChiN α`, the smallest closed subgroup containing `v`, is inside it.

Reducing mod `2^α` would *not* work: `v ≡ −1 (mod 2^α)`.  Level `α+1` is the first one that
sees the difference. -/

section Separation

/-- Reduction of a power of `2` mod `2^k`, as a natural-number cast. -/
private theorem toZModPow_two_pow (k n : ℕ) :
    PadicInt.toZModPow (p := 2) k ((2 : ℤ_[2]) ^ n) = ((2 ^ n : ℕ) : ZMod (2 ^ k)) := by
  rw [show (2 : ℤ_[2]) = ((2 : ℕ) : ℤ_[2]) by norm_num, ← Nat.cast_pow, map_natCast]

/-- **The pair subgroup.**  When a residue `r` mod `2^k` is an involution, the `2`-adic units
reducing to `1` or to `r` form a subgroup of `ℤ₂ˣ` — the finite-level shadow of a procyclic
group whose generator has residue `r`. -/
def modPairSubgroup (k : ℕ) (r : ZMod (2 ^ k)) (hr : r * r = 1) : Subgroup ℤ_[2]ˣ where
  carrier := {u : ℤ_[2]ˣ | PadicInt.toZModPow (p := 2) k (u : ℤ_[2]) = 1 ∨
    PadicInt.toZModPow (p := 2) k (u : ℤ_[2]) = r}
  one_mem' := Or.inl (by rw [Units.val_one, map_one])
  mul_mem' := by
    intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact Or.inl (by rw [Units.val_mul, map_mul, ha, hb, one_mul])
    · exact Or.inr (by rw [Units.val_mul, map_mul, ha, hb, one_mul])
    · exact Or.inr (by rw [Units.val_mul, map_mul, ha, hb, mul_one])
    · exact Or.inl (by rw [Units.val_mul, map_mul, ha, hb, hr])
  inv_mem' := by
    intro a ha
    have hmul : PadicInt.toZModPow (p := 2) k ((a : ℤ_[2]ˣ) : ℤ_[2]) *
        PadicInt.toZModPow (p := 2) k ((a⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
    rcases ha with ha | ha
    · rw [ha, one_mul] at hmul
      exact Or.inl hmul
    · rw [ha] at hmul
      refine Or.inr ?_
      have := congrArg (fun z => r * z) hmul
      simpa [← mul_assoc, hr] using this

@[simp] theorem mem_modPairSubgroup {k : ℕ} {r : ZMod (2 ^ k)} (hr : r * r = 1) (u : ℤ_[2]ˣ) :
    u ∈ modPairSubgroup k r hr ↔ PadicInt.toZModPow (p := 2) k (u : ℤ_[2]) = 1 ∨
      PadicInt.toZModPow (p := 2) k (u : ℤ_[2]) = r := Iff.rfl

/-- The pair subgroup is closed: it is the preimage of a two-element set under the locally
constant map `toZModPow k` (`isOpen_preimage_toZModPow`, `GQ2/ZtwoPowering.lean:143`). -/
theorem isClosed_modPairSubgroup (k : ℕ) (r : ZMod (2 ^ k)) (hr : r * r = 1) :
    IsClosed ((modPairSubgroup k r hr : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ) := by
  have hpre : ((modPairSubgroup k r hr : Subgroup ℤ_[2]ˣ) : Set ℤ_[2]ˣ)
      = (fun u : ℤ_[2]ˣ => (u : ℤ_[2])) ⁻¹'
        (PadicInt.toZModPow (p := 2) k ⁻¹' ({1, r} : Set (ZMod (2 ^ k)))) := by
    ext u
    simp only [SetLike.mem_coe, mem_modPairSubgroup, Set.mem_preimage, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  rw [hpre]
  refine IsClosed.preimage Units.continuous_val ?_
  rw [← isOpen_compl_iff, ← Set.preimage_compl]
  exact isOpen_preimage_toZModPow k _

/-- **`v² ≡ 1 (mod 2^{α+1})`**: the exact level of `v²` is `α + 1` (`nUnit_sq_sub_one`), so the
residue of `v` mod `2^{α+1}` is an involution. -/
theorem nUnit_res_sq (α : ℕ) (hα2 : 2 ≤ α) :
    PadicInt.toZModPow (p := 2) (α + 1) ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) *
      PadicInt.toZModPow (p := 2) (α + 1) ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
  obtain ⟨b, hb⟩ := nUnit_sq_sub_one hα2
  have hval : ((nUnit α ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) = ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 :=
    Units.val_pow_eq_pow_val _ _
  have hzero : PadicInt.toZModPow (p := 2) (α + 1) ((2 : ℤ_[2]) ^ (α + 1) * (b : ℤ_[2])) = 0 := by
    rw [map_mul, toZModPow_two_pow, ZMod.natCast_self, zero_mul]
  have hcong := congrArg (PadicInt.toZModPow (p := 2) (α + 1)) hb
  rw [map_sub, map_one, hval, map_pow, hzero, sub_eq_zero] at hcong
  rw [← pow_two]
  exact hcong

/-- **`v ≢ −1 (mod 2^{α+1})`**: from `v·(1+2^α) = −1`, the congruence `v ≡ −1` would force
`2^α ≡ 0 (mod 2^{α+1})`. -/
theorem nUnit_res_ne_neg_one (α : ℕ) (hα2 : 2 ≤ α) :
    PadicInt.toZModPow (p := 2) (α + 1) ((nUnit α : ℤ_[2]ˣ) : ℤ_[2])
      ≠ (-1 : ZMod (2 ^ (α + 1))) := by
  intro hres
  have hmul := congrArg (PadicInt.toZModPow (p := 2) (α + 1)) (nUnit_mul (α := α) (by omega))
  rw [map_mul, map_add, map_neg, map_one, hres, toZModPow_two_pow] at hmul
  have hz : ((2 ^ α : ℕ) : ZMod (2 ^ (α + 1))) = 0 := by linear_combination -hmul
  rw [CharP.cast_eq_zero_iff (ZMod (2 ^ (α + 1))) (2 ^ (α + 1)) (2 ^ α)] at hz
  have hle : 2 ^ (α + 1) ≤ 2 ^ α := Nat.le_of_dvd (Nat.two_pow_pos α) hz
  have hlt : 2 ^ α < 2 ^ (α + 1) := by
    have hpos := Nat.two_pow_pos α
    rw [pow_succ]
    omega
  omega

/-- **`−1` is not in the procyclic `N` image.**  `imChiN α` is the smallest closed subgroup
containing `v`, hence sits inside the pair subgroup at level `α + 1`, which misses `−1`. -/
theorem neg_one_notMem_imChiN {α : ℕ} (hα2 : 2 ≤ α) : (-1 : ℤ_[2]ˣ) ∉ imChiN α := by
  intro hmem
  have hr : PadicInt.toZModPow (p := 2) (α + 1) ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) *
      PadicInt.toZModPow (p := 2) (α + 1) ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) = 1 :=
    nUnit_res_sq α hα2
  have hsub : imChiN α ≤ modPairSubgroup (α + 1) _ hr := by
    refine Subgroup.topologicalClosure_minimal _ ?_ (isClosed_modPairSubgroup _ _ hr)
    rw [Subgroup.closure_le]
    rintro _ rfl
    exact (mem_modPairSubgroup hr _).mpr (Or.inr rfl)
  have hneg : PadicInt.toZModPow (p := 2) (α + 1) (((-1 : ℤ_[2]ˣ) : ℤ_[2]))
      = (-1 : ZMod (2 ^ (α + 1))) := by
    rw [Units.val_neg, Units.val_one, map_neg, map_one]
  rcases (mem_modPairSubgroup hr _).mp (hsub hmem) with h1 | h1
  · rw [hneg] at h1
    have h2 : ((2 : ℕ) : ZMod (2 ^ (α + 1))) = 0 := by push_cast; linear_combination -h1
    rw [CharP.cast_eq_zero_iff (ZMod (2 ^ (α + 1))) (2 ^ (α + 1)) 2] at h2
    have hle2 : 2 ^ (α + 1) ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have h8 : 2 ^ 3 ≤ 2 ^ (α + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8
    omega
  · rw [hneg] at h1
    exact nUnit_res_ne_neg_one α hα2 h1.symm

/-- **The `M`/`N` orientation-image separator** (memo §3.2(i), V2), proved: `−1 ∈ im χ_M` but
`−1 ∉ im χ_N`.  This is the invariant `NLabHypothesis` would have to key on for the two rows to
stay apart, and it is precisely what `chiNOnDM` shows the binder does *not* key on: the same
group `D_M` carries characters with both images. -/
theorem imChiM_ne_imChiN {α : ℕ} (hα2 : 2 ≤ α) : imChiM α ≠ imChiN α := fun heq =>
  neg_one_notMem_imChiN hα2 (heq ▸ neg_one_mem_imChiM α)

/-- The non-canonicity of `chiNOnDM`, stated where it bites: two continuous characters of the
*same* group `D_M` with different images, one of them the canonical `M` image. -/
theorem range_chiNOnDM_ne_range_chiM (α h : ℕ) (hα2 : 2 ≤ α) :
    MonoidHom.range (chiNOnDM α h).toMonoidHom ≠ MonoidHom.range (chiM α h).toMonoidHom := by
  rw [range_chiNOnDM, range_chiM]
  exact fun heq => imChiM_ne_imChiN hα2 heq.symm

end Separation

/-! ## §5 The `N`-side sanity pin

The same package on the row the binder is *about*.  Here the `q`-invariant is available at every
handle count (`demushkinQ_DN_nFrame`) once a frame is supplied, and the character is the
canonical `χ_N` itself, so the conclusion is the harmless one. -/

/-- `NLabHypothesis` applied to its own row: every hypothesis is met by `D_N` itself, the
canonicity guard included — on this row the character is the canonical `χ_N`, so `hcanon` is
whatever the consumer's own descent characterisation says about it. -/
theorem nonempty_equiv_DN_self_of_nLabHypothesis (α h : ℕ) (hα2 : 2 ≤ α)
    (nIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (F : MarkedCore.NFrame α h) (hLab : MarkedCore.NLabHypothesis α h nIsCanonical)
    (hcanon : nIsCanonical (DN α h : Type) (chiN α h).toMonoidHom) :
    Nonempty (ContinuousMulEquiv (DN α h : Type) (DN α h : Type)) :=
  hLab (DN α h : Type) (isDemushkin_DN α h hα2)
    (demushkinRank_DN α h (le_trans one_le_two hα2)) (MarkedCore.demushkinQ_DN_nFrame F)
    ⟨(chiN α h).toMonoidHom, (chiN α h).continuous_toFun, hcanon, range_chiN α h⟩

/-! ## §6 Axiom hygiene -/

#print axioms chiNOnDM
#print axioms chiNOnDM_dmA
#print axioms chiNOnDM_dmB
#print axioms chiNOnDM_dmC
#print axioms chiNOnDM_dmD
#print axioms chiNOnDM_handleU
#print axioms chiNOnDM_handleV
#print axioms range_chiNOnDM
#print axioms nonempty_equiv_DM_DN_of_nLabHypothesis
#print axioms noCanonicityGuard
#print axioms nonempty_equiv_DM_DN_of_unguarded_nLabHypothesis
#print axioms nonempty_equiv_DM_DN_zero_of_nLabHypothesis
#print axioms modPairSubgroup
#print axioms mem_modPairSubgroup
#print axioms isClosed_modPairSubgroup
#print axioms nUnit_res_sq
#print axioms nUnit_res_ne_neg_one
#print axioms neg_one_notMem_imChiN
#print axioms imChiM_ne_imChiN
#print axioms range_chiNOnDM_ne_range_chiM
#print axioms nonempty_equiv_DN_self_of_nLabHypothesis

end

end GQ2.Dyadic.EvenNLab
