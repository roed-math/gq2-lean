import GQ2.SectionSeven
import GQ2.FrattiniCriterion

/-!
# Frattini nongeneration for `frattiniLike`  (ticket P-16d, the (136) surjectivity step)

The finite-2-group **nongeneration property** of `Φ(K) = K²[K,K]`
(`SectionSeven.frattiniLike`): `H ⊔ Φ(K) = K` forces `H = K`.  Every maximal subgroup of the
finite 2-group `K` is normal of index 2, so its quotient is `ℤ/2` — abelian of exponent 2 —
and therefore contains all squares and commutators; a proper `H` lies under some maximal
subgroup, which then also contains `H ⊔ Φ(K)`.

Consequence (`eq_top_of_map_frattini_quotient_top`): in the §8 recursion, an `R`-lift whose
image maps onto `Y/R = Y/Φ(K)` is automatically **surjective** — the paper's Frattini
argument in the proof of Prop 8.9 ("if its image `J` maps onto `Y/R`, then `(J ∩ K)R = K`;
because `R = Φ(K)`, the Frattini argument forces `J ∩ K = K`, and hence `J = Y`").

All std-3; no axioms.
-/

namespace GQ2

open SectionSeven Pointwise

variable {Y : Type} [Group Y] [Finite Y]

/-- Squares land in any index-2 subgroup (the quotient has order 2). -/
private theorem sq_mem_of_index_two {Q : Type*} [Group Q] [Finite Q] {M : Subgroup Q}
    [M.Normal] (hM : M.index = 2) (k : Q) : k * k ∈ M := by
  have hcard : Nat.card (Q ⧸ M) = 2 := by
    rw [← hM]
    exact (Subgroup.index_eq_card M).symm
  have hpow : (QuotientGroup.mk k : Q ⧸ M) ^ 2 = 1 := by
    rw [← hcard]
    exact pow_card_eq_one'
  have hmk : (QuotientGroup.mk (k * k) : Q ⧸ M) = 1 := by
    rw [QuotientGroup.mk_mul, ← pow_two]
    exact hpow
  exact (QuotientGroup.eq_one_iff _).mp hmk

/-- Commutators land in any index-2 subgroup (the quotient has prime order, hence is
cyclic and abelian). -/
private theorem comm_mem_of_index_two {Q : Type*} [Group Q] [Finite Q] {M : Subgroup Q}
    [M.Normal] (hM : M.index = 2) (k l : Q) : k * l * k⁻¹ * l⁻¹ ∈ M := by
  have hcard : Nat.card (Q ⧸ M) = 2 := by
    rw [← hM]
    exact (Subgroup.index_eq_card M).symm
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsCyclic (Q ⧸ M) := isCyclic_of_prime_card hcard
  letI : CommGroup (Q ⧸ M) := IsCyclic.commGroup
  have hmk : (QuotientGroup.mk (k * l * k⁻¹ * l⁻¹) : Q ⧸ M) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, QuotientGroup.mk_inv]
    rw [mul_comm (QuotientGroup.mk k : Q ⧸ M) (QuotientGroup.mk l)]
    group
  exact (QuotientGroup.eq_one_iff _).mp hmk

/-- **Frattini nongeneration** for the finite 2-group `K`: a subgroup `H ≤ K` with
`H ⊔ Φ(K) = K` is all of `K`.  (`Φ(K) = K²[K,K] = frattiniLike K`.) -/
theorem frattiniLike_nongen {K H : Subgroup Y} (h2K : IsPGroup 2 ↥K) (hHK : H ≤ K)
    (hsup : H ⊔ frattiniLike K = K) : H = K := by
  classical
  -- pass to the subtype `Q = ↥K`
  set Φ' : Subgroup ↥K := Subgroup.closure
    ({x : ↥K | ∃ k : ↥K, x = k * k} ∪ {x : ↥K | ∃ k l : ↥K, x = k * l * k⁻¹ * l⁻¹}) with hΦ'
  have hmap : (H.subgroupOf K ⊔ Φ').map K.subtype = K := by
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, ← frattiniLike_eq_map,
      inf_eq_left.mpr hHK]
    exact hsup
  have htop : H.subgroupOf K ⊔ Φ' = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  -- a proper `H` would sit under a maximal subgroup that also contains `Φ'`
  rcases eq_top_or_exists_le_coatom (H.subgroupOf K) with heq | ⟨M, hM, hHM⟩
  · -- `H.subgroupOf K = ⊤` means `K ≤ H`
    have : K ≤ H := by
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ H.subgroupOf K := by rw [heq]; trivial
      exact this
    exact le_antisymm hHK this
  · exfalso
    haveI hMn : M.Normal := coatom_normal_of_pGroup h2K hM
    have hMi : M.index = 2 := coatom_index_of_pGroup h2K hM
    have hΦM : Φ' ≤ M := by
      rw [hΦ']
      refine (Subgroup.closure_le _).mpr ?_
      rintro x (⟨k, rfl⟩ | ⟨k, l, rfl⟩)
      · exact sq_mem_of_index_two hMi k
      · exact comm_mem_of_index_two hMi k l
    have : (⊤ : Subgroup ↥K) ≤ M := by
      rw [← htop]
      exact sup_le hHM hΦM
    exact hM.1 (le_antisymm le_top this)

/-- **The §8 R-lift surjectivity** (paper, proof of Prop 8.9): if `J ≤ Y` maps onto
`Y/R` for `R = Φ(K)` a normal subgroup with `R ≤ K` and `K` a 2-group inside the marked
kernel, then `J = ⊤`.  Route: `J ⊔ R = ⊤` (image onto the quotient, `R` normal), the
Dedekind step `K = (J ⊓ K) ⊔ R` (elementwise, `R ≤ K` and `R` normal), nongeneration
forces `J ⊓ K = K`, so `R ≤ K ≤ J` and `J = J ⊔ R = ⊤`. -/
theorem eq_top_of_map_frattini_quotient_top {B : Type} [Group B]
    (piB : Y →* B) {K : Subgroup Y} (h2K : IsPGroup 2 ↥K)
    (hker : piB.ker = frattiniLike K) (hRK : frattiniLike K ≤ K)
    [hRn : (frattiniLike K).Normal]
    {J : Subgroup Y} (hJtop : J.map piB = ⊤) (hBtop : piB.range = ⊤) : J = ⊤ := by
  classical
  -- `J ⊔ Φ(K) = ⊤`: every `y` has `piB`-image hit by some `j ∈ J`
  have hJR : J ⊔ frattiniLike K = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : piB y ∈ J.map piB := by rw [hJtop]; trivial
    obtain ⟨j, hjJ, hj⟩ := Subgroup.mem_map.mp hy
    have hker' : j⁻¹ * y ∈ frattiniLike K := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hj]
      group
    have hy' : y = j * (j⁻¹ * y) := by group
    rw [hy']
    exact Subgroup.mul_mem_sup hjJ hker'
  -- Dedekind step: `K = (J ⊓ K) ⊔ Φ(K)`
  have hKdec : (J ⊓ K) ⊔ frattiniLike K = K := by
    apply le_antisymm
    · exact sup_le (le_trans inf_le_right le_rfl) hRK
    · intro k hk
      -- `k ∈ ⊤ = J·Φ(K)` (`Φ(K)` normal): write `k = j·r`, then `j = k·r⁻¹ ∈ K`
      have hk' : k ∈ (J : Set Y) * (frattiniLike K : Set Y) := by
        rw [← Subgroup.mul_normal J (frattiniLike K), hJR, Subgroup.coe_top]
        trivial
      obtain ⟨j, hjJ, r, hrR, rfl⟩ := hk'
      have hjK : j ∈ K := by
        have hrK : r ∈ K := hRK hrR
        have hj' : j = (j * r) * r⁻¹ := by group
        rw [hj']
        exact mul_mem hk (inv_mem hrK)
      exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨hjJ, hjK⟩) hrR
  -- nongeneration: `J ⊓ K = K`, hence `K ≤ J`
  have hJK : J ⊓ K = K := frattiniLike_nongen h2K inf_le_right hKdec
  have hKJ : K ≤ J := by
    rw [← hJK]
    exact inf_le_left
  -- conclude
  have hJfix : J ⊔ frattiniLike K = J := by
    rw [sup_eq_left]
    exact le_trans hRK hKJ
  rw [← hJfix, hJR]

end GQ2
