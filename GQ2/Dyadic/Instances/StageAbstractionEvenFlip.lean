/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenEndpoint
import GQ2.Dyadic.MarkedCore.N

/-!
# W55-SLOT3: the paired move is false, the corrected move is true, and the even flip supply
collapses to one slot
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.EvenRowSupply

/-! ## §1 The two-central power-commutator identity -/

section Tower

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Squares sink one layer. -/
private theorem evenFlip_sq_mem {j m : ℕ} {q : levelQuot G m} (hq : q ∈ lambdaImage G j m) :
    q ^ 2 ∈ lambdaImage G (j + 1) m := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨x ^ 2, sq_mem_twoCentralSeries_succ G hx, map_pow _ _ _⟩

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `2`-power powers of a `λ_t`-class sink `r` further layers. -/
private theorem evenFlip_pow_mem {t m : ℕ} {q : levelQuot G m} (hq : q ∈ lambdaImage G t m)
    (r : ℕ) : q ^ 2 ^ r ∈ lambdaImage G (t + r) m := by
  induction r with
  | zero => simpa using hq
  | succ r ih =>
    have hsq : q ^ 2 ^ (r + 1) = (q ^ 2 ^ r) ^ 2 := by rw [← pow_mul, ← pow_succ]
    rw [hsq, show t + (r + 1) = t + r + 1 from rfl]
    exact evenFlip_sq_mem ih

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The exact expansion of a commutator against a square, in any group. -/
private theorem evenFlip_commP_sq {H : Type*} [Group H] (x y : H) :
    commP (x ^ 2) y = commP x y * commP (commP x y) x * commP x y := by
  simp only [commP, pow_two]
  group

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A vanishing `commP` is a commutation. -/
private theorem evenFlip_commute_of_commP {H : Type*} [Group H] {p q : H}
    (h : commP p q = 1) : Commute p q := by
  have hh : p * q = q * p := by
    calc p * q = q * p * (p⁻¹ * q⁻¹ * p * q) := by group
      _ = q * p := by rw [show p⁻¹ * q⁻¹ * p * q = commP p q from rfl, h, mul_one]
  exact hh

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A class of depth at least the level is trivial. -/
private theorem evenFlip_eq_one_of_deep {j m : ℕ} (hm : m ≤ j) {p : levelQuot G m}
    (hp : p ∈ lambdaImage G j m) : p = 1 := by
  have hbot : lambdaImage G j m ≤ lambdaImage G m m := lambdaImage_le_of_le hm
  rw [lambdaImage_self] at hbot
  exact Subgroup.mem_bot.mp (hbot hp)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Two classes of depth `j` commute in `Q_m` as soon as `m ≤ 2 * j`. -/
private theorem evenFlip_commute_deep {j m : ℕ} (hm : m ≤ j + j) {p q : levelQuot G m}
    (hp : p ∈ lambdaImage G j m) (hq : q ∈ lambdaImage G j m) : Commute p q :=
  evenFlip_commute_of_commP (evenFlip_eq_one_of_deep hm (commP_mem_lambdaImage_add hp hq))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Monoid homomorphisms intertwine the repo commutator convention. -/
private theorem evenFlip_map_commP {A B : Type*} [Group A] [Group B] (f : A →* B) (x y : A) :
    f (commP x y) = commP (f x) (f y) := by
  simp only [commP, map_mul, map_inv]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The two-central power-commutator identity.**  In `Q_{i+4}`, for every `a` and `b`, with
`c = [a, b]`:

  `[a ^ 2^(i+1), b] · c ^ 2^(i+1) · [c ^ 2^i, a] = 1`.

This is the whole arithmetic of the `2`-power commutator in the lower two-central tower: the
`2^(i+1)`-st power of `a` brackets against `b` exactly as `c ^ 2^(i+1)` does, up to the single
correction `[c ^ 2^i, a]`.  Proved by induction on `i`, each step running in one level higher
of the tower, with the induction hypothesis pulled back along `levelProj` and the two error
terms killed by the depth count `(i+3) + (i+2) ≥ i+5`. -/
theorem evenFlip_commP_pow_two (i : ℕ) : ∀ a b : levelQuot G (i + 4),
    commP (a ^ 2 ^ (i + 1)) b * commP a b ^ 2 ^ (i + 1) * commP (commP a b ^ 2 ^ i) a = 1 := by
  induction i with
  | zero =>
    intro a b
    have htop : ∀ q : levelQuot G 4, q ∈ lambdaImage G 1 4 := by
      intro q; rw [lambdaImage_one_eq_top]; trivial
    have hcmem : commP a b ∈ lambdaImage G 2 4 :=
      commP_mem_lambdaImage_add (htop a) (htop b)
    have hs : commP (commP a b) a ∈ zLayer G 3 :=
      commP_mem_lambdaImage_add hcmem (htop a)
    have ht : commP a b ^ 2 ∈ zLayer G 3 := evenFlip_sq_mem hcmem
    have hcen : ∀ z ∈ zLayer G 3, ∀ w : levelQuot G 4, w * z = z * w := fun z hz w ↦
      Subgroup.mem_center_iff.mp (zLayer_le_center G 3 hz) w
    simp only [Nat.zero_add, pow_zero, pow_one]
    rw [evenFlip_commP_sq a b]
    have hstep : commP a b * commP (commP a b) a * commP a b * commP a b ^ 2 *
        commP (commP a b) a = (commP a b ^ 2 * commP (commP a b) a) ^ 2 := by
      have hsc := hcen _ hs (commP a b)
      calc commP a b * commP (commP a b) a * commP a b * commP a b ^ 2 *
            commP (commP a b) a
          = commP a b * (commP (commP a b) a * commP a b) * commP a b ^ 2 *
            commP (commP a b) a := by group
        _ = commP a b * (commP a b * commP (commP a b) a) * commP a b ^ 2 *
            commP (commP a b) a := by rw [← hsc]
        _ = (commP a b * commP a b) * commP (commP a b) a * commP a b ^ 2 *
            commP (commP a b) a := by group
        _ = (commP a b ^ 2 * commP (commP a b) a) ^ 2 := by
            rw [← pow_two (commP a b), pow_two (commP a b ^ 2 * commP (commP a b) a)]
            group
    rw [hstep]
    exact zLayer_sq G (Subgroup.mul_mem _ ht hs)
  | succ i ih =>
    intro a b
    have htop : ∀ q : levelQuot G (i + 1 + 4), q ∈ lambdaImage G 1 (i + 1 + 4) := by
      intro q; rw [lambdaImage_one_eq_top]; trivial
    -- the induction hypothesis, pulled back one level
    have hE : commP (a ^ 2 ^ (i + 1)) b * commP a b ^ 2 ^ (i + 1) *
        commP (commP a b ^ 2 ^ i) a ∈ zLayer G (i + 4) := by
      rw [zLayer_eq_ker_levelProj, MonoidHom.mem_ker]
      simp only [map_mul, map_pow, evenFlip_map_commP]
      exact ih (levelProj G (i + 4) a) (levelProj G (i + 4) b)
    set c := commP a b with hcdef
    set x := a ^ 2 ^ (i + 1) with hxdef
    set z := c ^ 2 ^ i with hzdef
    set u := commP x b with hudef
    set s := commP z a with hsdef
    set t := c ^ 2 ^ (i + 1) with htdef
    -- depths
    have hcmem : c ∈ lambdaImage G 2 (i + 1 + 4) :=
      commP_mem_lambdaImage_add (htop a) (htop b)
    have hxmem : x ∈ lambdaImage G (i + 2) (i + 1 + 4) := by
      have hm := evenFlip_pow_mem (htop a) (i + 1)
      rw [show 1 + (i + 1) = i + 2 by omega] at hm
      exact hm
    have hzmem : z ∈ lambdaImage G (i + 2) (i + 1 + 4) := by
      have hm := evenFlip_pow_mem hcmem i
      rw [show 2 + i = i + 2 by omega] at hm
      exact hm
    have humem : u ∈ lambdaImage G (i + 3) (i + 1 + 4) := by
      have hm := commP_mem_lambdaImage_add hxmem (htop b)
      rw [show i + 2 + 1 = i + 3 by omega] at hm
      exact hm
    have hsmem : s ∈ lambdaImage G (i + 3) (i + 1 + 4) := by
      have hm := commP_mem_lambdaImage_add hzmem (htop a)
      rw [show i + 2 + 1 = i + 3 by omega] at hm
      exact hm
    have htmem : t ∈ lambdaImage G (i + 3) (i + 1 + 4) := by
      have hm := evenFlip_pow_mem hcmem (i + 1)
      rw [show 2 + (i + 1) = i + 3 by omega] at hm
      exact hm
    -- the two error terms die
    have hux : commP u x = 1 :=
      evenFlip_eq_one_of_deep (by omega) (commP_mem_lambdaImage_add humem hxmem)
    have hsz : commP s z = 1 :=
      evenFlip_eq_one_of_deep (by omega) (commP_mem_lambdaImage_add hsmem hzmem)
    -- the three rewrites
    have hgoal1 : commP (a ^ 2 ^ (i + 1 + 1)) b = u ^ 2 := by
      have hxx : a ^ 2 ^ (i + 1 + 1) = x ^ 2 := by
        rw [hxdef, ← pow_mul, ← pow_succ]
      rw [hxx, evenFlip_commP_sq x b, ← hudef, hux, mul_one, ← pow_two]
    have hgoal2 : c ^ 2 ^ (i + 1 + 1) = t ^ 2 := by rw [htdef, ← pow_mul, ← pow_succ]
    have hgoal3 : commP (c ^ 2 ^ (i + 1)) a = s ^ 2 := by
      have hzz : c ^ 2 ^ (i + 1) = z ^ 2 := by rw [hzdef, ← pow_mul, ← pow_succ]
      rw [hzz, evenFlip_commP_sq z a, ← hsdef, hsz, mul_one, ← pow_two]
    rw [hgoal1, hgoal2, hgoal3]
    -- and the collapse: the three squares recombine into the square of the pulled-back class
    have hut : Commute u t := evenFlip_commute_deep (by omega) humem htmem
    have hus : Commute u s := evenFlip_commute_deep (by omega) humem hsmem
    have hts : Commute t s := evenFlip_commute_deep (by omega) htmem hsmem
    have hcut : Commute (u * t) s := hus.mul_left hts
    have hcollapse : (u * t * s) ^ 2 = u ^ 2 * t ^ 2 * s ^ 2 := by
      rw [hcut.mul_pow, hut.mul_pow]
    rw [← hcollapse]
    exact zLayer_sq G hE

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The identity at the depth the flip engines run at.**  For `k ≥ 3` and any two classes of
`Q_{k+1}`, with `n = 2^(k-2)` the flip exponent and `m = 2^(k-3)` its half. -/
theorem evenFlip_commP_pow_of_three_le {k : ℕ} (hk : 3 ≤ k) (a b : levelQuot G (k + 1)) :
    commP (a ^ 2 ^ (k - 2)) b * commP a b ^ 2 ^ (k - 2) *
      commP (commP a b ^ 2 ^ (k - 3)) a = 1 := by
  obtain ⟨i, rfl⟩ : ∃ i, k = i + 3 := ⟨k - 3, by omega⟩
  have h2 : i + 3 - 2 = i + 1 := by omega
  have h3 : i + 3 - 3 = i := by omega
  rw [h2, h3]
  exact evenFlip_commP_pow_two i a b

/-! ### §1.2 Depth bookkeeping at the flip exponent -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The flip exponent `2^(k-2)` sinks any class to depth `k-1`. -/
theorem evenFlip_pow_flip_mem {k : ℕ} (hk : 3 ≤ k) (q : levelQuot G (k + 1)) :
    q ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) := by
  have hm := pow_two_pow_mem_lambdaImage q (k - 2)
  rwa [show 1 + (k - 2) = k - 1 by omega] at hm

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The half exponent `2^(k-3)` sinks any *commutator* to depth `k-1`: a commutator already
has depth `2`, and `2 + (k - 3) = k - 1`. -/
theorem evenFlip_commP_pow_half_mem {k : ℕ} (hk : 3 ≤ k) (a b : levelQuot G (k + 1)) :
    commP a b ^ 2 ^ (k - 3) ∈ lambdaImage G (k - 1) (k + 1) := by
  have htop : ∀ q : levelQuot G (k + 1), q ∈ lambdaImage G 1 (k + 1) := by
    intro q; rw [lambdaImage_one_eq_top]; trivial
  have hm := evenFlip_pow_mem (commP_mem_lambdaImage_add (htop a) (htop b)) (k - 3)
  rwa [show 2 + (k - 3) = k - 1 by omega] at hm

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The flip exponent applied to a commutator lands in the central layer. -/
theorem evenFlip_commP_pow_flip_mem {k : ℕ} (hk : 3 ≤ k) (a b : levelQuot G (k + 1)) :
    commP a b ^ 2 ^ (k - 2) ∈ zLayer G k := by
  have htop : ∀ q : levelQuot G (k + 1), q ∈ lambdaImage G 1 (k + 1) := by
    intro q; rw [lambdaImage_one_eq_top]; trivial
  have hm := evenFlip_pow_mem (commP_mem_lambdaImage_add (htop a) (htop b)) (k - 2)
  rwa [show 2 + (k - 2) = k by omega] at hm

/-! ### §1.3 Bilinearity of the row map on the top layer

Every row of the literal even shift word is a `commP` against a fixed base letter, evaluated
at a depth-`(k-1)` class; the value is central, so the row map is a homomorphism in the
correction. -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The row map is additive in the correction: `commP` against a fixed letter is multiplicative
on depth-`(k-1)` classes. -/
theorem evenFlip_commP_mul_left {k : ℕ} (hk : 3 ≤ k) {p q y : levelQuot G (k + 1)}
    (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (p * q) y = commP p y * commP q y := by
  have hcen := zLayer_le_center G k (commP_mem_zLayer k hk hp (g := y))
  have hzc : q⁻¹ * commP p y = commP p y * q⁻¹ :=
    (Subgroup.mem_center_iff.mp hcen q⁻¹)
  have hid : commP (p * q) y = q⁻¹ * commP p y * q * commP q y := by
    simp only [commP]; group
  rw [hid]
  calc q⁻¹ * commP p y * q * commP q y = commP p y * q⁻¹ * q * commP q y := by rw [hzc]
    _ = commP p y * commP q y := by group

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Inverting a depth-`(k-1)` class inverts its row. -/
theorem evenFlip_commP_inv_left {k : ℕ} (hk : 3 ≤ k) {p y : levelQuot G (k + 1)}
    (hp : p ∈ lambdaImage G (k - 1) (k + 1)) :
    commP p⁻¹ y = (commP p y)⁻¹ := by
  have hmul := evenFlip_commP_mul_left hk (p := p) (q := p⁻¹) (y := y) hp
  rw [mul_inv_cancel] at hmul
  have hone : commP (1 : levelQuot G (k + 1)) y = 1 := by simp only [commP]; group
  rw [hone] at hmul
  exact eq_inv_of_mul_eq_one_right hmul.symm

end Tower

/-! ## §2 The wave-54 paired move, and its repair -/

section PairedMove

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Central layer classes are involutions. -/
private theorem evenFlip_zsq {k : ℕ} {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) :
    z * z = 1 := by
  rw [← pow_two]; exact zLayer_sq G hz

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Central layer classes commute with everything. -/
private theorem evenFlip_zcomm {k : ℕ} {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k)
    (w : levelQuot G (k + 1)) : z * w = w * z :=
  (Subgroup.mem_center_iff.mp (zLayer_le_center G k hz) w).symm

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Central layer classes are their own inverses. -/
private theorem evenFlip_zinv {k : ℕ} {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) :
    z⁻¹ = z :=
  inv_eq_of_mul_eq_one_left (evenFlip_zsq hz)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Two three-term relations among involutions, with one central letter shared, force the
product of the two leading letters. -/
private theorem evenFlip_two_relations {H : Type*} [Group H] {A B C S T : H}
    (hCc : ∀ w : H, C * w = w * C) (hC2 : C * C = 1) (hS2 : S * S = 1) (hT2 : T * T = 1)
    (h1 : A * C * S = 1) (h2 : B * C * T = 1) : A * B = S * T := by
  have hA : A = S * C := by
    calc A = A * C * S * (S * C) := by
          rw [show A * C * S * (S * C) = A * C * (S * S) * C by group, hS2,
            show A * C * 1 * C = A * (C * C) by group, hC2, mul_one]
      _ = S * C := by rw [h1, one_mul]
  have hB : B = T * C := by
    calc B = B * C * T * (T * C) := by
          rw [show B * C * T * (T * C) = B * C * (T * T) * C by group, hT2,
            show B * C * 1 * C = B * (C * C) by group, hC2, mul_one]
      _ = T * C := by rw [h2, one_mul]
  calc A * B = S * (C * T) * C := by rw [hA, hB]; group
    _ = S * (T * C) * C := by rw [hCc T]
    _ = S * T * (C * C) := by group
    _ = S * T := by rw [hC2, mul_one]

variable {k : ℕ}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The exact value of the wave-54 paired move.**  For any two classes `a`, `b` of `Q_{k+1}`,
with `c = [a, b]`, `n = 2^(k-2)` and `m = 2^(k-3)`:

  `[a^n, b] · [b^n, a] = [c^m, a] · [c^m, b]`.

Both sides lie in the central involutive layer `Z_k`.  This is the honest content of the
wave-54 reduction `evenEndpoint_flipSlotThree_M_of_pairedMove`, whose hypothesis `hpair` asks
the left side to vanish: the right side is what it actually equals, and it does not vanish in
general (§2.1). -/
theorem evenFlip_pairedMove_eq (hk : 3 ≤ k) (a b : levelQuot G (k + 1)) :
    commP (a ^ 2 ^ (k - 2)) b * commP (b ^ 2 ^ (k - 2)) a =
      commP (commP a b ^ 2 ^ (k - 3)) a * commP (commP a b ^ 2 ^ (k - 3)) b := by
  have hcm : commP a b ^ 2 ^ (k - 3) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_commP_pow_half_mem hk a b
  have hCmem : commP a b ^ 2 ^ (k - 2) ∈ zLayer G k := evenFlip_commP_pow_flip_mem hk a b
  have hSmem : commP (commP a b ^ 2 ^ (k - 3)) a ∈ zLayer G k := commP_mem_zLayer k hk hcm a
  have hTmem : commP (commP a b ^ 2 ^ (k - 3)) b ∈ zLayer G k := commP_mem_zLayer k hk hcm b
  have hab := evenFlip_commP_pow_of_three_le hk a b
  have hba := evenFlip_commP_pow_of_three_le hk b a
  have hinv : commP b a = (commP a b)⁻¹ := by simp only [commP]; group
  rw [hinv, inv_pow, inv_pow, evenFlip_commP_inv_left hk hcm, evenFlip_zinv hCmem,
    evenFlip_zinv hTmem] at hba
  exact evenFlip_two_relations (evenFlip_zcomm hCmem) (evenFlip_zsq hCmem)
    (evenFlip_zsq hSmem) (evenFlip_zsq hTmem) hab hba

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **What the wave-54 hypothesis really asks.**  `hpair` of
`evenEndpoint_flip_three_of_pairedMove` is *equivalent* to the vanishing of
`[c^m, a] · [c^m, b]`, that is of `[[a,b], a·b]` up to the half power: an honest condition on
the pair, not an identity. -/
theorem evenFlip_pairedMove_iff (hk : 3 ≤ k) (a b : levelQuot G (k + 1)) :
    commP (a ^ 2 ^ (k - 2)) b * commP (b ^ 2 ^ (k - 2)) a = 1 ↔
      commP (commP a b ^ 2 ^ (k - 3)) a * commP (commP a b ^ 2 ^ (k - 3)) b = 1 := by
  rw [evenFlip_pairedMove_eq hk a b]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The corrected paired move.**  Placing `a^n · c^m` at one cross slot and `b^n · c^m` at
the other, with `c = [a, b]`, kills the pair of rows outright, for every `a` and `b` and with
no hypothesis at all.  This is the wave-54 move with the wave-54 obstruction added back at
both slots: each of `[c^m, a]` and `[c^m, b]` now occurs twice in the central involutive
layer, so the whole product dies. -/
theorem evenFlip_pairedMove_corrected (hk : 3 ≤ k) (a b : levelQuot G (k + 1)) :
    commP (a ^ 2 ^ (k - 2) * commP a b ^ 2 ^ (k - 3)) b *
      commP (b ^ 2 ^ (k - 2) * commP a b ^ 2 ^ (k - 3)) a = 1 := by
  have hcm : commP a b ^ 2 ^ (k - 3) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_commP_pow_half_mem hk a b
  have hamem : a ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) := evenFlip_pow_flip_mem hk a
  have hbmem : b ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) := evenFlip_pow_flip_mem hk b
  have hSmem : commP (commP a b ^ 2 ^ (k - 3)) a ∈ zLayer G k := commP_mem_zLayer k hk hcm a
  have hTmem : commP (commP a b ^ 2 ^ (k - 3)) b ∈ zLayer G k := commP_mem_zLayer k hk hcm b
  rw [evenFlip_commP_mul_left hk hamem, evenFlip_commP_mul_left hk hbmem]
  set A := commP (a ^ 2 ^ (k - 2)) b with hAdef
  set B := commP (b ^ 2 ^ (k - 2)) a with hBdef
  set S := commP (commP a b ^ 2 ^ (k - 3)) a with hSdef
  set T := commP (commP a b ^ 2 ^ (k - 3)) b with hTdef
  have hAB : A * B = S * T := evenFlip_pairedMove_eq hk a b
  calc A * T * (B * S) = A * B * (T * S) := by
        rw [show A * T * (B * S) = A * (T * B) * S by group,
          evenFlip_zcomm hTmem B, show A * (B * T) * S = A * B * (T * S) by group]
    _ = S * T * (T * S) := by rw [hAB]
    _ = S * (T * T) * S := by group
    _ = S * S := by rw [evenFlip_zsq hTmem, mul_one]
    _ = 1 := evenFlip_zsq hSmem

end PairedMove

/-! ## §3 The two flip engines -/

section Engines

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Central layer classes commute with everything, in `Commute` form. -/
private theorem evenFlip_zcommute {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k)
    (w : levelQuot G (k + 1)) : Commute z w :=
  (Subgroup.mem_center_iff.mp (zLayer_le_center G k hz) w).symm

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The flip power of a canonical lift is the residue of the flip power (the endpoint lane's
`hlift`, restated once). -/
private theorem evenFlip_lift_pow (hk : 3 ≤ k) (x : G) :
    canonLift G k (levelMk G k x) ^ 2 ^ (k - 2) = levelMk G (k + 1) (x ^ 2 ^ (k - 2)) := by
  have h1 : canonLift G k (levelMk G k x) ^ 2 = levelMk G (k + 1) x ^ 2 :=
    (sq_levelMk_eq_sq_canonLift G k x).symm
  have hsplit : (2 : ℕ) * 2 ^ (k - 3) = 2 ^ (k - 2) := by
    rw [show k - 2 = k - 3 + 1 by omega, pow_succ']
  calc canonLift G k (levelMk G k x) ^ 2 ^ (k - 2)
      = (canonLift G k (levelMk G k x) ^ 2) ^ 2 ^ (k - 3) := by rw [← pow_mul, hsplit]
    _ = (levelMk G (k + 1) x ^ 2) ^ 2 ^ (k - 3) := by rw [h1]
    _ = levelMk G (k + 1) (x ^ 2 ^ (k - 2)) := by rw [← pow_mul, hsplit, ← map_pow]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A `commP` of canonical lifts is the residue of the `commP`: the two `Z_k`-discrepancies are
central, and `commP` kills central factors on both sides. -/
private theorem evenFlip_lift_commP (x y : G) :
    commP (canonLift G k (levelMk G k x)) (canonLift G k (levelMk G k y)) =
      levelMk G (k + 1) (commP x y) := by
  have hzx := levelMk_mul_canonLift_inv_mem_zLayer G k x
  have hzy := levelMk_mul_canonLift_inv_mem_zLayer G k y
  have hx : levelMk G (k + 1) x =
      levelMk G (k + 1) x * (canonLift G k (levelMk G k x))⁻¹ *
        canonLift G k (levelMk G k x) := by group
  have hy : levelMk G (k + 1) y =
      levelMk G (k + 1) y * (canonLift G k (levelMk G k y))⁻¹ *
        canonLift G k (levelMk G k y) := by group
  rw [evenFlip_map_commP, hx, hy, commP_central_left (evenFlip_zcommute hzx),
    commP_central_right (evenFlip_zcommute hzy)]

/-- **Engine A: the partner move.**  Suppose the row of slot `i₀` is the pure bracket against
the letter `iw`, and the row of some *other* slot `i₁` is the pure bracket against the letter
`ig`.  Then the correction placing `base ig ^ 2^(k-2) · e ^ 2^(k-3)` at `i₀` and
`base iw ^ 2^(k-2) · e ^ 2^(k-3)` at `i₁`, with `e = [base ig, base iw]`, has literally trivial
shift word (§2's corrected paired move), carries the character digit of `v ig` at `i₀` and the
character digit of `v iw` at `i₁`, and is trivial everywhere else.  So a sharp `v ig` and a
digit-trivial `v iw` give the flip at `i₀`. -/
theorem evenFlip_flip_of_partner {α : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hk : 3 ≤ k) (T : Tuple W v G chi k)
    {i₀ i₁ ig iw : Fin (MarkedCore.coreRank h)} (hne : i₀ ≠ i₁)
    (hrow₀ : ∀ p : lambdaImage G (k - 1) (k + 1),
      ((evenRawDepthShiftHom (fun i ↦ canonLift G k (T.generators i)) hk)
          (evenRawDepthCoordinateCorrection i₀ p)).1 =
        commP p.1 (canonLift G k (T.generators iw)))
    (hrow₁ : ∀ p : lambdaImage G (k - 1) (k + 1),
      ((evenRawDepthShiftHom (fun i ↦ canonLift G k (T.generators i)) hk)
          (evenRawDepthCoordinateCorrection i₁ p)).1 =
        commP p.1 (canonLift G k (T.generators ig)))
    (hsharp : ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((v ig ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (htriv : (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((v iw ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  obtain ⟨xg, hxgchi, hxgrep⟩ := T.rows ig
  obtain ⟨xw, hxwchi, hxwrep⟩ := T.rows iw
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  set e := commP (base ig) (base iw) with hedef
  have hgmem : base ig ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_pow_flip_mem hk _
  have hwmem : base iw ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_pow_flip_mem hk _
  have hemem : e ^ 2 ^ (k - 3) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_commP_pow_half_mem hk _ _
  set p₀ : lambdaImage G (k - 1) (k + 1) :=
    ⟨base ig ^ 2 ^ (k - 2) * e ^ 2 ^ (k - 3), Subgroup.mul_mem _ hgmem hemem⟩ with hp₀
  set p₁ : lambdaImage G (k - 1) (k + 1) :=
    ⟨base iw ^ 2 ^ (k - 2) * e ^ 2 ^ (k - 3), Subgroup.mul_mem _ hwmem hemem⟩ with hp₁
  set F : EvenRawDepthCorrection G h k :=
    evenRawDepthCoordinateCorrection i₀ p₀ * evenRawDepthCoordinateCorrection i₁ p₁ with hF
  -- the group elements realising the three placements
  have hliftg : base ig ^ 2 ^ (k - 2) = levelMk G (k + 1) (xg ^ 2 ^ (k - 2)) := by
    rw [show base ig = canonLift G k (levelMk G k xg) from by
      rw [show base ig = canonLift G k (T.generators ig) from rfl, hxgrep]]
    exact evenFlip_lift_pow hk xg
  have hliftw : base iw ^ 2 ^ (k - 2) = levelMk G (k + 1) (xw ^ 2 ^ (k - 2)) := by
    rw [show base iw = canonLift G k (levelMk G k xw) from by
      rw [show base iw = canonLift G k (T.generators iw) from rfl, hxwrep]]
    exact evenFlip_lift_pow hk xw
  have hlifte : e ^ 2 ^ (k - 3) = levelMk G (k + 1) (commP xg xw ^ 2 ^ (k - 3)) := by
    rw [hedef, show base ig = canonLift G k (levelMk G k xg) from by
      rw [show base ig = canonLift G k (T.generators ig) from rfl, hxgrep],
      show base iw = canonLift G k (levelMk G k xw) from by
      rw [show base iw = canonLift G k (T.generators iw) from rfl, hxwrep],
      evenFlip_lift_commP, ← map_pow]
  have hchic : chi (commP xg xw) = 1 := by
    simp only [commP, map_mul, map_inv]
    rw [mul_comm ((chi xg)⁻¹) ((chi xw)⁻¹)]
    group
  have hchie : ((chi (commP xg xw ^ 2 ^ (k - 3)) : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [map_pow, hchic, one_pow, Units.val_one]
  have hcorr : ∀ j : Fin (MarkedCore.coreRank h), F.correction j =
      (if j = i₀ then p₀.1 else 1) * (if j = i₁ then p₁.1 else 1) := by
    intro j
    rw [hF, EvenRawDepthCorrection.mul_correction, evenRawDepthCoordinateCorrection_apply,
      evenRawDepthCoordinateCorrection_apply]
  refine ⟨F, ?_, ?_, ?_⟩
  · -- the row is the corrected paired move
    have hmul : ((evenRawDepthShiftHom base hk) F).1 =
        ((evenRawDepthShiftHom base hk) (evenRawDepthCoordinateCorrection i₀ p₀)).1 *
          ((evenRawDepthShiftHom base hk) (evenRawDepthCoordinateCorrection i₁ p₁)).1 := by
      rw [hF, map_mul]
      rfl
    show ((evenRawDepthShiftHom base hk) F).1 = 1
    rw [hmul, hrow₀ p₀, hrow₁ p₁]
    exact evenFlip_pairedMove_corrected hk (base ig) (base iw)
  · -- the sharp slot
    refine ⟨xg ^ 2 ^ (k - 2) * commP xg xw ^ 2 ^ (k - 3), ?_, ?_⟩
    · rw [hcorr i₀, if_pos rfl, if_neg hne, mul_one,
        show p₀.1 = base ig ^ 2 ^ (k - 2) * e ^ 2 ^ (k - 3) from rfl,
        hliftg, hlifte, map_mul]
    · rw [map_mul, Units.val_mul, hchie, mul_one, map_pow, hxgchi]
      exact hsharp
  · -- every other slot
    intro j hj
    by_cases hj₁ : j = i₁
    · subst hj₁
      refine ⟨xw ^ 2 ^ (k - 2) * commP xg xw ^ 2 ^ (k - 3), ?_, ?_⟩
      · rw [hcorr j, if_neg hj, if_pos rfl, one_mul,
          show p₁.1 = base iw ^ 2 ^ (k - 2) * e ^ 2 ^ (k - 3) from rfl,
          hliftw, hlifte, map_mul]
      · rw [map_mul, Units.val_mul, hchie, mul_one, map_pow, hxwchi]
        exact htriv
    · refine ⟨1, ?_, ?_⟩
      · rw [hcorr j, if_neg hj, if_neg hj₁, mul_one, map_one]
      · rw [map_one, Units.val_one]
        simp

/-- The two leading letters are distinct. -/
private theorem evenFlip_idx01 : (0 : Fin (MarkedCore.coreRank h)) ≠ 1 := fun hh ↦ by
  have hv := congrArg Fin.val hh
  rw [MarkedCore.coreVal_zero, MarkedCore.coreVal_one] at hv
  omega

/-- **Engine B: the diagonal move.**  Suppose the row of slot `i₀ ≠ 0` is the pure bracket
against the letter `iw`, the row of slot `0` is the diagonal `p² · [p, base 0] · [p, base 1]`,
and the row of slot `1` is `[p, base 0]`.  Then the correction placing
`base 1 ^ 2^(k-2)` at `i₀` and `e ^ 2^(k-3)` at *both* slots `0` and `1`, with
`e = [base 1, base iw]`, has literally trivial shift word: the two `[e^m, base 0]` cancel in
the involutive layer, and what is left is exactly §1's power-commutator identity at the pair
`(base 1, base iw)`.  So on a row table whose character mass sits at the letter `1` - the
`N` situation, where no bracket partner is sharp - every slot but `0` is constructible. -/
theorem evenFlip_flip_of_diagonal {α : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (hk : 3 ≤ k) (T : Tuple W v G chi k)
    {i₀ iw : Fin (MarkedCore.coreRank h)} (hi₀ : i₀ ≠ 0)
    (hrow₀ : ∀ p : lambdaImage G (k - 1) (k + 1),
      ((evenRawDepthShiftHom (fun i ↦ canonLift G k (T.generators i)) hk)
          (evenRawDepthCoordinateCorrection i₀ p)).1 =
        commP p.1 (canonLift G k (T.generators iw)))
    (hrowZero : ∀ p : lambdaImage G (k - 1) (k + 1),
      ((evenRawDepthShiftHom (fun i ↦ canonLift G k (T.generators i)) hk)
          (evenRawDepthCoordinateCorrection 0 p)).1 =
        p.1 ^ 2 * commP p.1 (canonLift G k (T.generators 0)) *
          commP p.1 (canonLift G k (T.generators 1)))
    (hrowOne : ∀ p : lambdaImage G (k - 1) (k + 1),
      ((evenRawDepthShiftHom (fun i ↦ canonLift G k (T.generators i)) hk)
          (evenRawDepthCoordinateCorrection 1 p)).1 =
        commP p.1 (canonLift G k (T.generators 0)))
    (hsharp : ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((v 1 ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  obtain ⟨xg, hxgchi, hxgrep⟩ := T.rows 1
  obtain ⟨xw, hxwchi, hxwrep⟩ := T.rows iw
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  set e := commP (base 1) (base iw) with hedef
  have hgmem : base 1 ^ 2 ^ (k - 2) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_pow_flip_mem hk _
  have hemem : e ^ 2 ^ (k - 3) ∈ lambdaImage G (k - 1) (k + 1) :=
    evenFlip_commP_pow_half_mem hk _ _
  set pg : lambdaImage G (k - 1) (k + 1) := ⟨base 1 ^ 2 ^ (k - 2), hgmem⟩ with hpg
  set pe : lambdaImage G (k - 1) (k + 1) := ⟨e ^ 2 ^ (k - 3), hemem⟩ with hpe
  set F : EvenRawDepthCorrection G h k :=
    evenRawDepthCoordinateCorrection i₀ pg * evenRawDepthCoordinateCorrection 0 pe *
      evenRawDepthCoordinateCorrection 1 pe with hF
  have hliftg : base 1 ^ 2 ^ (k - 2) = levelMk G (k + 1) (xg ^ 2 ^ (k - 2)) := by
    rw [show base 1 = canonLift G k (levelMk G k xg) from by
      rw [show base 1 = canonLift G k (T.generators 1) from rfl, hxgrep]]
    exact evenFlip_lift_pow hk xg
  have hlifte : e ^ 2 ^ (k - 3) = levelMk G (k + 1) (commP xg xw ^ 2 ^ (k - 3)) := by
    rw [hedef, show base 1 = canonLift G k (levelMk G k xg) from by
      rw [show base 1 = canonLift G k (T.generators 1) from rfl, hxgrep],
      show base iw = canonLift G k (levelMk G k xw) from by
      rw [show base iw = canonLift G k (T.generators iw) from rfl, hxwrep],
      evenFlip_lift_commP, ← map_pow]
  have hchic : chi (commP xg xw) = 1 := by
    simp only [commP, map_mul, map_inv]
    rw [mul_comm ((chi xg)⁻¹) ((chi xw)⁻¹)]
    group
  have hchie : ((chi (commP xg xw ^ 2 ^ (k - 3)) : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [map_pow, hchic, one_pow, Units.val_one]
  have hcorr : ∀ j : Fin (MarkedCore.coreRank h), F.correction j =
      (if j = i₀ then pg.1 else 1) * (if j = (0 : Fin (MarkedCore.coreRank h)) then pe.1 else 1) *
        (if j = (1 : Fin (MarkedCore.coreRank h)) then pe.1 else 1) := by
    intro j
    rw [hF, EvenRawDepthCorrection.mul_correction, EvenRawDepthCorrection.mul_correction,
      evenRawDepthCoordinateCorrection_apply, evenRawDepthCoordinateCorrection_apply,
      evenRawDepthCoordinateCorrection_apply]
  refine ⟨F, ?_, ?_, ?_⟩
  · -- the row is the diagonal move
    have hmul : ((evenRawDepthShiftHom base hk) F).1 =
        ((evenRawDepthShiftHom base hk) (evenRawDepthCoordinateCorrection i₀ pg)).1 *
          ((evenRawDepthShiftHom base hk) (evenRawDepthCoordinateCorrection 0 pe)).1 *
          ((evenRawDepthShiftHom base hk) (evenRawDepthCoordinateCorrection 1 pe)).1 := by
      rw [hF, map_mul, map_mul]
      rfl
    show ((evenRawDepthShiftHom base hk) F).1 = 1
    rw [hmul, hrow₀ pg, hrowZero pe, hrowOne pe]
    -- all four factors are central involutions; the two `[e^m, base 0]` cancel
    have hAmem : commP (base 1 ^ 2 ^ (k - 2)) (base iw) ∈ zLayer G k :=
      commP_mem_zLayer k hk hgmem _
    have hXmem : commP (e ^ 2 ^ (k - 3)) (base 0) ∈ zLayer G k :=
      commP_mem_zLayer k hk hemem _
    have hYmem : commP (e ^ 2 ^ (k - 3)) (base 1) ∈ zLayer G k :=
      commP_mem_zLayer k hk hemem _
    have hEmem : (e ^ 2 ^ (k - 3)) ^ 2 ∈ zLayer G k := sq_mem_zLayer k hk hemem
    have hEsq : (e ^ 2 ^ (k - 3)) ^ 2 = e ^ 2 ^ (k - 2) := by
      rw [← pow_mul, show 2 ^ (k - 3) * 2 = 2 ^ (k - 2) by
        rw [show k - 2 = k - 3 + 1 by omega, pow_succ]]
    have hkey := evenFlip_commP_pow_of_three_le hk (base 1) (base iw)
    rw [← hedef] at hkey
    show commP pg.1 (base iw) * (pe.1 ^ 2 * commP pe.1 (base 0) * commP pe.1 (base 1)) *
      commP pe.1 (base 0) = 1
    show commP (base 1 ^ 2 ^ (k - 2)) (base iw) *
      ((e ^ 2 ^ (k - 3)) ^ 2 * commP (e ^ 2 ^ (k - 3)) (base 0) *
        commP (e ^ 2 ^ (k - 3)) (base 1)) * commP (e ^ 2 ^ (k - 3)) (base 0) = 1
    calc commP (base 1 ^ 2 ^ (k - 2)) (base iw) *
          ((e ^ 2 ^ (k - 3)) ^ 2 * commP (e ^ 2 ^ (k - 3)) (base 0) *
            commP (e ^ 2 ^ (k - 3)) (base 1)) * commP (e ^ 2 ^ (k - 3)) (base 0)
        = commP (base 1 ^ 2 ^ (k - 2)) (base iw) * (e ^ 2 ^ (k - 3)) ^ 2 *
            (commP (e ^ 2 ^ (k - 3)) (base 0) *
              (commP (e ^ 2 ^ (k - 3)) (base 1) * commP (e ^ 2 ^ (k - 3)) (base 0))) := by
          group
      _ = commP (base 1 ^ 2 ^ (k - 2)) (base iw) * (e ^ 2 ^ (k - 3)) ^ 2 *
            (commP (e ^ 2 ^ (k - 3)) (base 0) *
              (commP (e ^ 2 ^ (k - 3)) (base 0) * commP (e ^ 2 ^ (k - 3)) (base 1))) := by
          rw [evenFlip_zcomm hYmem]
      _ = commP (base 1 ^ 2 ^ (k - 2)) (base iw) * (e ^ 2 ^ (k - 3)) ^ 2 *
            commP (e ^ 2 ^ (k - 3)) (base 1) := by
          rw [show commP (e ^ 2 ^ (k - 3)) (base 0) *
              (commP (e ^ 2 ^ (k - 3)) (base 0) * commP (e ^ 2 ^ (k - 3)) (base 1)) =
              commP (e ^ 2 ^ (k - 3)) (base 0) * commP (e ^ 2 ^ (k - 3)) (base 0) *
                commP (e ^ 2 ^ (k - 3)) (base 1) by group, evenFlip_zsq hXmem, one_mul]
      _ = 1 := by rw [hEsq]; exact hkey
  · -- the sharp slot
    by_cases hi1 : i₀ = 1
    · refine ⟨xg ^ 2 ^ (k - 2) * commP xg xw ^ 2 ^ (k - 3), ?_, ?_⟩
      · rw [hcorr i₀, if_pos rfl, if_neg hi₀, if_pos hi1, mul_one,
          show pg.1 = base 1 ^ 2 ^ (k - 2) from rfl, show pe.1 = e ^ 2 ^ (k - 3) from rfl,
          hliftg, hlifte, map_mul]
      · rw [map_mul, Units.val_mul, hchie, mul_one, map_pow, hxgchi]
        exact hsharp
    · refine ⟨xg ^ 2 ^ (k - 2), ?_, ?_⟩
      · rw [hcorr i₀, if_pos rfl, if_neg hi₀, if_neg hi1, mul_one, mul_one,
          show pg.1 = base 1 ^ 2 ^ (k - 2) from rfl, hliftg]
      · rw [map_pow, hxgchi]
        exact hsharp
  · -- every other slot
    intro j hj
    by_cases hj0 : j = (0 : Fin (MarkedCore.coreRank h))
    · subst hj0
      refine ⟨commP xg xw ^ 2 ^ (k - 3), ?_, ?_⟩
      · rw [hcorr 0, if_neg hj, if_pos rfl, if_neg evenFlip_idx01, one_mul, mul_one,
          show pe.1 = e ^ 2 ^ (k - 3) from rfl, hlifte]
      · rw [hchie]
        simp
    · by_cases hj1 : j = (1 : Fin (MarkedCore.coreRank h))
      · subst hj1
        refine ⟨commP xg xw ^ 2 ^ (k - 3), ?_, ?_⟩
        · rw [hcorr 1, if_neg hj, if_neg hj0, if_pos rfl, one_mul, one_mul,
            show pe.1 = e ^ 2 ^ (k - 3) from rfl, hlifte]
        · rw [hchie]
          simp
      · refine ⟨1, ?_, ?_⟩
        · rw [hcorr j, if_neg hj, if_neg hj0, if_neg hj1, mul_one, mul_one, map_one]
        · rw [map_one, Units.val_one]
          simp

end Engines

/-! ## §4 The two branches: every slot but `0` -/

section Branches

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

open GQ2.Dyadic.MarkedCore (mUnit nUnit)

/-! ### §4.1 Index disequalities and the two digit facts -/

private theorem evenFlip_idx_ne {i i' : Fin (MarkedCore.coreRank h)}
    (hi : (i : ℕ) ≠ (i' : ℕ)) : i ≠ i' := fun hh ↦ hi (congrArg Fin.val hh)

private theorem evenFlip_handleU_ne {j : Fin h} {i : Fin (MarkedCore.coreRank h)}
    (hi : (i : ℕ) < 4) : MarkedCore.handleIdxU j ≠ i := by
  intro hh
  have hv := congrArg Fin.val hh
  rw [MarkedCore.handleIdxU_val] at hv
  omega

private theorem evenFlip_handleV_ne {j : Fin h} {i : Fin (MarkedCore.coreRank h)}
    (hi : (i : ℕ) < 4) : MarkedCore.handleIdxV j ≠ i := by
  intro hh
  have hv := congrArg Fin.val hh
  rw [MarkedCore.handleIdxV_val] at hv
  omega

/-- The `M` table is sharp at index `3`: `mUnit α` has exact level `α`, so its `2^(k-2)`-th
power has exact level `k + α - 2` and escapes `k + (α - 1)` digits. -/
theorem evenFlip_sharp_M {α : ℕ} (hα : 2 ≤ α) (hk : 3 ≤ k) :
    ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣
      ((vM (h := h) α 3 ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  rw [vM_three]
  have hsh := (evenDigit_pow_sharp (mUnit α) (mUnit α) hα
    (MarkedCore.mUnit_sub_one (by omega)) (k - 2)).2
  rwa [show k + (α - 1) = k - 2 + α + 1 by omega]

/-- The `N` table is sharp at index `1`, one squaring later: `nUnit α` has odd part `-1`, and
`(nUnit α)²` has exact level `α + 1`, so the `2^(k-2)`-th power of `nUnit α` again has exact
level `k + α - 2`. -/
theorem evenFlip_sharp_N {α : ℕ} (hα : 2 ≤ α) (hk : 3 ≤ k) :
    ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣
      ((vN (h := h) α 1 ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  rw [vN_one]
  obtain ⟨a, ha⟩ := evenDigit_nUnit_sq_eq hα
  have hsh := (evenDigit_pow_sharp (nUnit α ^ 2) a (by omega) ha (k - 3)).2
  rw [show (nUnit α ^ 2) ^ 2 ^ (k - 3) = nUnit α ^ 2 ^ (k - 2) by
    rw [← pow_mul, show 2 * 2 ^ (k - 3) = 2 ^ (k - 2) by
      rw [show k - 2 = k - 3 + 1 by omega, pow_succ']]] at hsh
  rwa [show k + (α - 1) = k - 3 + (α + 1) + 1 by omega]

/-- A kernel row contributes no digit at all. -/
theorem evenFlip_triv_one {α : ℕ} :
    (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ (((1 : ℤ_[2]ˣ) ^ 2 ^ (k - 2) : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  simp

/-! ### §4.2 The `M` branch: slot `2` by the partner power, everything but `0` by the
partner move -/

/-- **The `M`-branch flip at every slot but `0`.**  Slot `2` is the wave-53 theorem; every
other nonzero slot is the partner move of §3 with `ig = 3` (the only sharp `M` letter) and
`i₁ = 2` (the slot whose row brackets against letter `3`). -/
theorem evenFlip_flipOffZero_M {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α} (hk : 3 ≤ k)
    (T : Tuple (mStageWord α h hα₁) (vM α) G chi k)
    (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 0) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  have hrow₁ := evenRawDepthShiftHom_two_apply base hk
  obtain rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ := MarkedCore.nCoreIdx_cases i₀
  · exact absurd rfl hi₀
  · exact evenFlip_flip_of_partner hk T
      (evenFlip_idx_ne (by rw [MarkedCore.coreVal_one, MarkedCore.coreVal_two]; omega))
      (evenRawDepthShiftHom_one_apply base hk) hrow₁ (evenFlip_sharp_M hα hk)
      (by rw [vM_zero]; exact evenFlip_triv_one)
  · exact evenDigit_flipSlotTwo_M hα hk T
  · exact evenFlip_flip_of_partner hk T
      (evenFlip_idx_ne (by rw [MarkedCore.coreVal_three, MarkedCore.coreVal_two]; omega))
      (evenRawDepthShiftHom_three_apply base hk) hrow₁ (evenFlip_sharp_M hα hk)
      (by rw [vM_two]; exact evenFlip_triv_one)
  · exact evenFlip_flip_of_partner hk T
      (evenFlip_handleU_ne (by rw [MarkedCore.coreVal_two]; omega))
      (evenRawDepthShiftHom_handleU_apply base hk j) hrow₁ (evenFlip_sharp_M hα hk)
      (by rw [vM_handleV]; exact evenFlip_triv_one)
  · exact evenFlip_flip_of_partner hk T
      (evenFlip_handleV_ne (by rw [MarkedCore.coreVal_two]; omega))
      (evenRawDepthShiftHom_handleV_apply base hk j) hrow₁ (evenFlip_sharp_M hα hk)
      (by rw [vM_handleU]; exact evenFlip_triv_one)

/-! ### §4.3 The `N` branch: everything but `0` by the diagonal move -/

/-- **The `N`-branch flip at every slot but `0`.**  Wave 53 found no `N` slot constructible by
partner powers, and that verdict was right: the `N` character mass sits at the letter `1`,
which is nobody's bracket partner.  The diagonal move of §3 reaches it anyway - slot `0`'s row
carries `[p, base 1]` alongside the diagonal square and `[p, base 0]`, and slot `1`'s row
cancels the second - so every nonzero `N` slot is constructible after all. -/
theorem evenFlip_flipOffZero_N {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α} (hk : 3 ≤ k)
    (T : Tuple (nStageWord α h hα₁) (vN α) G chi k)
    (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 0) :
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) := by
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  have hz := evenRawDepthShiftHom_zero_apply base hk
  have ho := evenRawDepthShiftHom_one_apply base hk
  obtain rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩ := MarkedCore.nCoreIdx_cases i₀
  · exact absurd rfl hi₀
  · exact evenFlip_flip_of_diagonal hk T hi₀ ho hz ho (evenFlip_sharp_N hα hk)
  · exact evenFlip_flip_of_diagonal hk T hi₀
      (evenRawDepthShiftHom_two_apply base hk) hz ho (evenFlip_sharp_N hα hk)
  · exact evenFlip_flip_of_diagonal hk T hi₀
      (evenRawDepthShiftHom_three_apply base hk) hz ho (evenFlip_sharp_N hα hk)
  · exact evenFlip_flip_of_diagonal hk T hi₀
      (evenRawDepthShiftHom_handleU_apply base hk j) hz ho (evenFlip_sharp_N hα hk)
  · exact evenFlip_flip_of_diagonal hk T hi₀
      (evenRawDepthShiftHom_handleV_apply base hk j) hz ho (evenFlip_sharp_N hα hk)

end Branches

/-! ## §5 The reduced flip supplies -/

section Supply

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}

/-- **The digit flip supply at slot `0` only.**  `EvenDigitFlipSupply` with every demand
deleted except the one at the diagonal coordinate `0`.  On both even row tables the deleted
demands are the theorems of §4, so this asks exactly as much (§5's two equivalences) while
being the single honest residue. -/
def EvenDigitFlipSupplySlotZero (α : ℕ) {h : ℕ} (W : StageWord (MarkedCore.coreRank h))
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple W v G chi k,
    ∃ F : EvenRawDepthCorrection G h k,
      evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) F.correction = 1 ∧
      (∃ g : G, F.correction 0 = levelMk G (k + 1) g ∧
        ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
      (∀ j : Fin (MarkedCore.coreRank h), j ≠ 0 →
        ∃ g : G, F.correction j = levelMk G (k + 1) g ∧
          (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The full supply implies the reduced one, trivially. -/
theorem evenFlip_slotZero_of_flip {α : ℕ} {W : StageWord (MarkedCore.coreRank h)}
    {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ} (H : EvenDigitFlipSupply α W v G chi) :
    EvenDigitFlipSupplySlotZero α W v G chi :=
  fun k hk T ↦ H k hk T 0

/-- **The reduced `M` supply gives the full one.**  Every deleted demand is a theorem of §4. -/
theorem evenFlip_mFlip_of_slotZero {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α}
    (H : EvenDigitFlipSupplySlotZero α (mStageWord α h hα₁) (vM α) G chi) :
    EvenDigitFlipSupply α (mStageWord α h hα₁) (vM α) G chi := by
  intro k hk T i₀
  by_cases hi : i₀ = 0
  · subst hi
    exact H k hk T
  · exact evenFlip_flipOffZero_M hα hk T i₀ hi

/-- **The reduced `N` supply gives the full one.** -/
theorem evenFlip_nFlip_of_slotZero {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α}
    (H : EvenDigitFlipSupplySlotZero α (nStageWord α h hα₁) (vN α) G chi) :
    EvenDigitFlipSupply α (nStageWord α h hα₁) (vN α) G chi := by
  intro k hk T i₀
  by_cases hi : i₀ = 0
  · subst hi
    exact H k hk T
  · exact evenFlip_flipOffZero_N hα hk T i₀ hi

/-- **The two `M` flip statements are equivalent**, for every `α ≥ 2`. -/
theorem evenFlip_mFlip_iff_slotZero {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α} :
    EvenDigitFlipSupply α (mStageWord α h hα₁) (vM α) G chi ↔
      EvenDigitFlipSupplySlotZero α (mStageWord α h hα₁) (vM α) G chi :=
  ⟨evenFlip_slotZero_of_flip, evenFlip_mFlip_of_slotZero hα⟩

/-- **The two `N` flip statements are equivalent**, for every `α ≥ 2`. -/
theorem evenFlip_nFlip_iff_slotZero {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α} :
    EvenDigitFlipSupply α (nStageWord α h hα₁) (vN α) G chi ↔
      EvenDigitFlipSupplySlotZero α (nStageWord α h hα₁) (vN α) G chi :=
  ⟨evenFlip_slotZero_of_flip, evenFlip_nFlip_of_slotZero hα⟩

/-- The reduced `M` supply also gives the wave-54 `off slot 2` form the composed `M` endpoint
carries. -/
theorem evenFlip_mOffTwo_of_slotZero {α : ℕ} (hα : 2 ≤ α) {hα₁ : 1 ≤ α}
    (H : EvenDigitFlipSupplySlotZero α (mStageWord α h hα₁) (vM α) G chi) :
    GQ2.Dyadic.EvenEndpoint.EvenDigitFlipSupplyOffTwo α (mStageWord α h hα₁) (vM α) G chi :=
  GQ2.Dyadic.EvenEndpoint.evenEndpoint_offTwo_of_flip (evenFlip_mFlip_of_slotZero hα H)

end Supply

/-! ## §6 The even endpoints, with the flip input reduced to one slot -/

section Endpoints

open ContCoh
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply
open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenFrameDeep
open GQ2.Dyadic.EvenEndpoint

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenFlipScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenFlipContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The slot-`0` flip supply at one field, `N` branch**, at every branch depth `α ≥ 2`. -/
def EvenFlipNSlotZero (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha),
    EvenDigitFlipSupplySlotZero alpha (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

/-- **The slot-`0` flip supply at one field, `M` branch**, at every branch depth `α ≥ 2`. -/
def EvenFlipMSlotZero (h : ℕ) (K : IntermediateField ℚ_[2] ℚ̄₂)
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (alpha : ℕ) (halpha : 2 ≤ alpha),
    EvenDigitFlipSupplySlotZero alpha (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-54 `N` flip input is implied by the slot-`0` one. -/
theorem evenFlip_nFlip_of_nSlotZero {h : ℕ} (H : EvenFlipNSlotZero h K) :
    EvenEndpointNFlip h K :=
  fun alpha halpha ↦ evenFlip_nFlip_of_slotZero halpha (H alpha halpha)

omit [FiniteDimensional ℚ_[2] K] in
/-- The wave-54 `M` flip input (off slot `2`) is implied by the slot-`0` one. -/
theorem evenFlip_mFlipOffTwo_of_mSlotZero {h : ℕ} (H : EvenFlipMSlotZero h K) :
    EvenEndpointMFlipOffTwo h K :=
  fun alpha halpha ↦ evenFlip_mOffTwo_of_slotZero halpha (H alpha halpha)

/-- **The composed `N` endpoint at one field and one branch depth, at one flip slot.**  The
wave-54 statement with the flip supply reduced to its diagonal coordinate. -/
theorem evenFlip_orientedEquivN_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha))
        (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplySlotZero alpha
      (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivN_atDepth halpha hrange hev Hfam
    (evenFlip_nFlip_of_slotZero halpha Hflip)

/-- **The composed `M` endpoint at one field and one branch depth, at one flip slot.** -/
theorem evenFlip_orientedEquivM_atDepth {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hiso : frattiniFrameCup (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange)
      (evenDeepClass alpha (Nat.le_of_succ_le halpha) hrange) = 0)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha))
        (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplySlotZero alpha
      (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivM_atDepth halpha hrange hev hiso Hfam
    (evenFlip_mOffTwo_of_slotZero halpha Hflip)

/-- **The composed even `N` endpoint, per field, at one flip slot.**  Carried: the coordinate
derivation family with its relator kill, and one digit at one coordinate per stage. -/
theorem evenFlip_orientedEquivN {R : LocalReciprocity} (B : MarkedRecip R K)
    (deltaI : ℚ̄₂) (hdeltaI : deltaI ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K deltaI)
    (hneg : (-1 : ℤ_[2]ˣ) ∉ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : EvenEndpointNFamily h K) (Hflip : EvenFlipNSlotZero h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiN alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivN B deltaI hdeltaI hram hneg h hev Hfam
    (evenFlip_nFlip_of_nSlotZero Hflip)

/-- **The composed even `M` endpoint, per field, at one flip slot.** -/
theorem evenFlip_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hiso : EvenDeepMIsotropicSupply K)
    (Hfam : EvenEndpointMFamily h K) (Hflip : EvenFlipMSlotZero h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivM B hneg h hev Hiso Hfam
    (evenFlip_mFlipOffTwo_of_mSlotZero Hflip)

/-- **The `N` endpoint on the `α = 2` stratum, at one flip slot.** -/
theorem evenFlip_orientedEquivN_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 2 h one_le_two) (vN 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplySlotZero 2 (nStageWord 2 h one_le_two) (vN 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivN_two hrange hev Hfam
    (evenFlip_nFlip_of_slotZero (le_refl 2) Hflip)

/-- **The `M` endpoint on the `α = 2` stratum, at one flip slot.**  Two inputs, and one digit
at one coordinate per stage is the whole of the second. -/
theorem evenFlip_orientedEquivM_two {h : ℕ}
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord 2 h one_le_two) (vM 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F)
    (Hflip : EvenDigitFlipSupplySlotZero 2 (mStageWord 2 h one_le_two) (vM 2)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K))) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 h) (chiCycKTwo (K := K))) :=
  evenEndpoint_orientedEquivM_two hrange hev Hfam
    (evenFlip_mOffTwo_of_slotZero (le_refl 2) Hflip)

end Endpoints

end

end GQ2.Dyadic.StageGeneric
