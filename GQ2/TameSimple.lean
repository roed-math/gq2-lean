import GQ2.FoxHeisenberg

/-!
# P-13d: tameness of the split-case simple factors

For a nontrivial simple `𝔽₂[C]`-module `V` at a marking whose tame/wild inertia (`τ, x₀, x₁`) acts
trivially and which **generates** `C`, the `C`-action factors through the cyclic `⟨σ̄⟩`, so it is
abelian.  Two consequences, which `prop_5_15` (P-13f) feeds to `lemma_5_13_split`:

* **`sigma2_smul_trivial`** (`hU`) — the 2-primary part `σ₂ = σ^{ω₂}` acts trivially.  Because the
  action is abelian, `σ₂` is central, so its fixed space `V^{σ₂}` is a `C`-submodule; `⟨σ₂⟩` is a
  2-group, so (`p`-group fixed points, char 2) `V^{σ₂} ≠ 0`; simplicity forces `V^{σ₂} = V`.
* **`fixedPoints_sigma_eq_zero`** (`hVS`) — `V^S = 0` when `σ` acts nontrivially: `V^σ` is a
  `C`-submodule (σ central), so `⊥` or `⊤`; nontriviality kills `⊤`.

The central-fixed-point mechanism is `central_pow2_smul_trivial`, the analogue of `lemma_5_12` with
centrality in place of normality.  No finite-field / image-group construction is needed.
-/

namespace GQ2.FoxH

open scoped Classical

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- The set of `c : C` whose action commutes with a fixed automorphism `g •` is a subgroup. -/
def actionCommutant (g : C) : Subgroup C where
  carrier := {c | ∀ v : V, g • (c • v) = c • (g • v)}
  one_mem' v := by rw [one_smul, one_smul]
  mul_mem' {a b} ha hb v := by
    rw [mul_smul, ha, hb, ← mul_smul]
  inv_mem' {a} ha v := by
    have h := ha (a⁻¹ • v)
    rw [smul_inv_smul] at h
    rw [h, inv_smul_smul]

/-- Dually: the set of `h : C` commuting (in the action) with the whole `C`-action is a subgroup.
Used to promote centrality of `g` to centrality of every `zpower` of `g`. -/
def actionCentre : Subgroup C where
  carrier := {h | ∀ (c : C) (v : V), h • (c • v) = c • (h • v)}
  one_mem' c v := by rw [one_smul, one_smul]
  mul_mem' {a b} ha hb c v := by rw [mul_smul, mul_smul, hb, ha]
  inv_mem' {a} ha c v := by
    have h := ha c (a⁻¹ • v)
    rw [smul_inv_smul] at h
    rw [← h, inv_smul_smul]

variable [Finite V]

/-- **The central fixed-point lemma** (analogue of `lemma_5_12` with centrality for normality):
a 2-power-order element `g` whose action commutes with the whole `C`-action acts trivially on a
simple char-2 module.  Its fixed space is `C`-stable (centrality) and nonzero (`p`-group fixed
points, char 2), so simplicity makes it everything. -/
theorem central_pow2_smul_trivial (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (g : C) (hpow : IsPGroup 2 (Subgroup.zpowers g))
    (hcentral : ∀ (c : C) (v : V), g • (c • v) = c • (g • v)) :
    ∀ v : V, g • v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial V := hsimple.1
  -- every zpower of `g` is central too
  have hcomm : ∀ h ∈ Subgroup.zpowers g, ∀ (c : C) (v : V), h • (c • v) = c • (h • v) := by
    have hle : Subgroup.zpowers g ≤ actionCentre (C := C) (V := V) :=
      Subgroup.zpowers_le.mpr (show g ∈ actionCentre (C := C) (V := V) from hcentral)
    exact fun h hh => hle hh
  -- the fixed space of `⟨g⟩`
  let W : AddSubgroup V :=
    { carrier := {v | ∀ h ∈ Subgroup.zpowers g, h • v = v}
      zero_mem' := fun h _ => smul_zero h
      add_mem' := fun {a b} ha hb h hh => by rw [smul_add, ha h hh, hb h hh]
      neg_mem' := fun {a} ha h hh => by rw [smul_neg, ha h hh] }
  have hmemW : ∀ {v : V}, v ∈ W ↔ ∀ h ∈ Subgroup.zpowers g, h • v = v := Iff.rfl
  -- `C`-stable by centrality
  have hstable : ∀ (c : C) (w : V), w ∈ W → c • w ∈ W := by
    intro c w hw h hh
    rw [hcomm h hh c w, hw h hh]
  -- fixed points of `↥⟨g⟩` coincide with `W`
  have hset : (MulAction.fixedPoints ↥(Subgroup.zpowers g) V : Set V) = (W : Set V) := by
    ext v
    refine ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  -- `|V|` even
  have h2 : 2 ∣ Nat.card V := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hord : addOrderOf v = 2 := addOrderOf_eq_prime (by rw [two_nsmul]; exact hV₂ v) hv
    exact hord ▸ addOrderOf_dvd_natCard v
  -- so `W ≠ ⊥`
  have hWne : W ≠ ⊥ := by
    intro hbot
    have hmod := hpow.card_modEq_card_fixedPoints (p := 2) V
    have hsub : Subsingleton ↥(MulAction.fixedPoints ↥(Subgroup.zpowers g) V) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have haW : a ∈ W := by rw [← SetLike.mem_coe, ← hset]; exact ha
      have hbW : b ∈ W := by rw [← SetLike.mem_coe, ← hset]; exact hb
      rw [hbot, AddSubgroup.mem_bot] at haW hbW
      exact Subtype.ext (haW.trans hbW.symm)
    have h0fp : (0 : V) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers g) V := by
      have : (0 : V) ∈ (W : Set V) := W.zero_mem
      rwa [← hset] at this
    have hfp1 : Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers g) V) = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨0, h0fp⟩⟩⟩
    rw [hfp1] at hmod
    have h0 : Nat.card V ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr h2
    exact absurd (h0.symm.trans hmod) (by decide)
  -- simplicity ⟹ `W = ⊤` ⟹ `g` acts trivially
  rcases hsimple.2 W hstable with h | h
  · exact absurd h hWne
  · intro v
    exact (h ▸ AddSubgroup.mem_top v : v ∈ W) g (Subgroup.mem_zpowers g)

/-- `orderOf (powOmega2 x) ∣ 2 ^ v₂(orderOf x)`: the 2-primary projection has 2-power order.
The odd part `m = n / 2^a` of `n = orderOf x` divides `ω₂` (`oddPart_dvd_omega2Exp`), so
`n = 2^a·m ∣ ω₂·2^a`, whence `(x^{ω₂})^{2^a} = 1`. -/
theorem orderOf_powOmega2_dvd_two_pow {G : Type*} [Group G] [Finite G] (x : G) :
    orderOf (powOmega2 x) ∣ 2 ^ (orderOf x).factorization 2 := by
  apply orderOf_dvd_of_pow_eq_one
  have hm : (orderOf x / 2 ^ (orderOf x).factorization 2) ∣ omega2Exp (orderOf x) :=
    oddPart_dvd_omega2Exp (orderOf x)
  have hsplit : 2 ^ (orderOf x).factorization 2 * (orderOf x / 2 ^ (orderOf x).factorization 2)
      = orderOf x := Nat.ordProj_mul_ordCompl_eq_self (orderOf x) 2
  have key : orderOf x ∣ omega2Exp (orderOf x) * 2 ^ (orderOf x).factorization 2 :=
    calc orderOf x
        = 2 ^ (orderOf x).factorization 2 * (orderOf x / 2 ^ (orderOf x).factorization 2) :=
          hsplit.symm
      _ ∣ 2 ^ (orderOf x).factorization 2 * omega2Exp (orderOf x) := mul_dvd_mul_left _ hm
      _ = omega2Exp (orderOf x) * 2 ^ (orderOf x).factorization 2 := mul_comm _ _
  rw [powOmega2, ← pow_mul]
  exact (orderOf_dvd_iff_pow_eq_one).mp key

/-- `⟨powOmega2 x⟩` is a 2-group — needed to feed `central_pow2_smul_trivial` with `g = σ₂`. -/
theorem isPGroup_zpowers_powOmega2 {G : Type*} [Group G] [Finite G] (x : G) :
    IsPGroup 2 (Subgroup.zpowers (powOmega2 x)) := by
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_powOmega2_dvd_two_pow x)
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])

/-- With `τ, x₀, x₁` acting trivially and the marking generating `C`, any `g` whose action commutes
with `σ`'s is central for the whole `C`-action.  The commutant `{c | g·c = c·g on V}` is a subgroup
containing the four generators (three act trivially, `σ` by hypothesis), hence is all of `C`. -/
theorem central_of_commutes_sigma (t : Marking C) (hgen : t.Generates)
    (htau : ∀ v : V, t.τ • v = v) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (g : C) (hgσ : ∀ v : V, g • (t.σ • v) = t.σ • (g • v)) :
    ∀ (c : C) (v : V), g • (c • v) = c • (g • v) := by
  have hle : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤ actionCommutant (V := V) g := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hgσ
    · intro v; simp only [htau]
    · intro v; simp only [hx0]
    · intro v; simp only [hx1]
  rw [hgen] at hle
  exact fun c v => hle (Subgroup.mem_top c) v

/-- **P-13d output `hU`**: on a nontrivial simple char-2 module at a *generating* split-tame marking
(`τ, x₀, x₁` trivial), the 2-primary part `σ₂` acts trivially.  `σ₂` is central (`σ₂` is a power of
`σ`, and the module is generated) and of 2-power order, so `central_pow2_smul_trivial` applies. -/
theorem sigma2_smul_trivial (t : Marking C) (hgen : t.Generates)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) :
    ∀ v : V, t.sigma2 • v = v := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  refine central_pow2_smul_trivial hV₂ hsimple t.sigma2 (isPGroup_zpowers_powOmega2 t.σ) ?_
  refine central_of_commutes_sigma t hgen htau hx0 hx1 t.sigma2 (fun v => ?_)
  have hcomm : Commute t.sigma2 t.σ := (Commute.refl t.σ).pow_left _
  rw [smul_smul, smul_smul, hcomm.eq]

/-- **P-13d output `hVS`**: on a nontrivial simple char-2 module at a *generating* split-tame marking
where `σ` acts nontrivially, `V^S = 0` (the `1 + S⁻¹`-invertibility feeding `lemma_5_13_split`).
`V^σ` is a `C`-submodule (`σ` central), so `⊥` or `⊤`; the nontriviality `hσ` kills `⊤`. -/
theorem fixedPoints_sigma_eq_zero (t : Marking C) (hgen : t.Generates)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) (hσ : ∃ v : V, t.σ • v ≠ v) :
    ∀ v : V, t.σ • v = v → v = 0 := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  have hcentralσ : ∀ (c : C) (v : V), t.σ • (c • v) = c • (t.σ • v) :=
    central_of_commutes_sigma t hgen htau hx0 hx1 t.σ (fun _ => rfl)
  let W : AddSubgroup V :=
    { carrier := {v | t.σ • v = v}
      zero_mem' := smul_zero t.σ
      add_mem' := fun {a b} ha hb => by
        show t.σ • (a + b) = a + b
        rw [smul_add, ha, hb]
      neg_mem' := fun {a} ha => by
        show t.σ • (-a) = -a
        rw [smul_neg, ha] }
  have hstable : ∀ (c : C) (w : V), w ∈ W → c • w ∈ W := by
    intro c w hw
    show t.σ • (c • w) = c • w
    rw [hcentralσ, hw]
  rcases hsimple.2 W hstable with h | h
  · intro v hv
    have hvW : v ∈ W := hv
    rw [h, AddSubgroup.mem_bot] at hvW
    exact hvW
  · exfalso
    obtain ⟨v, hv⟩ := hσ
    exact hv (h.ge (AddSubgroup.mem_top v))

end GQ2.FoxH
