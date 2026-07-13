import GQ2.SectionSeven.Basic

/-!
# Lemma 7.2 (Frattini–centralizer collapse) and Lemma 7.3 (decorations vanish)

Split off from `GQ2.SectionSeven`, building on `GQ2.SectionSeven.Basic`.  This file provides:

* **Lemma 7.2** (`lemma_7_2`): for a tame head, the Frattini–centralizer collapse;
* **Lemma 7.3** (`lemma_7_3`): every homomorphism from `Y` to an elementary target that is
  trivial on the block's decorations vanishes.

See `GQ2.SectionSeven` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionSeven

open QuadraticFp2

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

variable {L : Subgroup Y}

/-! ## Lemma 7.2 (Frattini–centralizer collapse) and Lemma 7.3 (decorations vanish) -/

/-- **Lemma 7.2**: for a tame head (the target's head map factors through `GQ2.Ttame`),
`R = Φ(K)` is central elementary abelian in `K`, and `K⁴ = 1`.  [P-14 statement; proof P-15
(odd Hall lift + three-subgroup lemma + the `G`-equivariant fourth-power map).] -/
theorem lemma_7_2 {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom Ttame H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L) :
    (∀ r ∈ B.frattiniK, ∀ k ∈ B.K, r * k = k * r) ∧ (∀ r ∈ B.frattiniK, r * r = 1) ∧
      ∀ k ∈ B.K, k ^ 4 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := B.hK
  have := B.hS
  have := B.hP
  have hRN : (B.frattiniK).Normal := frattiniLike_normal B.K B.hK
  -- `IsPGroup 2 P` and `IsPGroup 2 S`
  have hP2 : IsPGroup 2 B.P := B.h2L.to_le B.hPL
  have hS2 : IsPGroup 2 B.S := B.h2L.to_le (B.hSP.le.trans B.hPL)
  -- an odd-order element moving `V = P/S`
  obtain ⟨y, hyodd, pw, hpwP, hpwS⟩ :=
    GQ2.exists_odd_moving_general B.S B.P B.hS B.hP B.hSP hP2 B.chief B.nontrivial_action
  set Ñ := Subgroup.zpowers y with hÑ
  have hÑcard : Nat.card Ñ = orderOf y := Nat.card_zpowers y
  -- `#Ñ` (odd) is coprime to `#S` (a power of 2)
  have hcop : Nat.Coprime (Nat.card Ñ) (Nat.card B.S) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hS2
    rw [hÑcard, hm]
    exact (Nat.coprime_two_right.mpr hyodd).pow_right m
  -- `⁅Ñ, S⁆ = ⊥`
  obtain ⟨n, c, hc0, hcn, hmono, _hnorm, hccomm⟩ := B.scalar_below
  have hÑS : ⁅Ñ, B.S⁆ = ⊥ := by
    have := GQ2.comm_bot_of_scalarChain n Ñ c hc0 hmono hccomm (by rw [hcn]; exact hcop)
    rwa [hcn] at this
  -- `R ≤ S`, hence `⁅Ñ, R⁆ = ⊥`
  have hRS : B.frattiniK ≤ B.S := (lemma_7_1_head B).trans inf_le_right
  have hÑR : ⁅Ñ, B.frattiniK⁆ = ⊥ := le_bot_iff.mp (hÑS ▸ Subgroup.commutator_mono le_rfl hRS)
  have hÑcentR : Ñ ≤ Subgroup.centralizer (B.frattiniK : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hÑR
  -- `D = K ⊓ C_Y(R)` is `Y`-normal
  set D := B.K ⊓ Subgroup.centralizer (B.frattiniK : Set Y) with hD
  have : D.Normal := by
    refine ⟨fun d hd g => Subgroup.mem_inf.mpr
      ⟨B.hK.conj_mem d (Subgroup.mem_inf.mp hd).1 g, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hdc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2
    have hgr : g⁻¹ * r * g ∈ B.frattiniK := by simpa using hRN.conj_mem r hr g⁻¹
    have hcomm := hdc (g⁻¹ * r * g) hgr
    calc r * (g * d * g⁻¹) = g * ((g⁻¹ * r * g) * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * d * g⁻¹) * r := by group
  -- three-subgroup lemma: `⁅⁅K, Ñ⁆, R⁆ = ⊥`
  have hRK : ⁅B.frattiniK, B.K⁆ ≤ B.frattiniK := Subgroup.commutator_le_left B.frattiniK B.K
  have h3 : ⁅⁅B.K, Ñ⁆, B.frattiniK⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [hÑR, Subgroup.commutator_bot_left]
    · exact le_bot_iff.mp (hÑR ▸
        (Subgroup.commutator_mono hRK le_rfl).trans
          (le_of_eq (Subgroup.commutator_comm B.frattiniK Ñ)))
  -- `⁅K, Ñ⁆ ≤ D`
  have hKÑD : ⁅B.K, Ñ⁆ ≤ D :=
    le_inf (Subgroup.commutator_le_left B.K Ñ)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  -- the `Y`-normal closure `K₁ = ⟪⁅K,Ñ⁆⟫` sits inside `D` and inside `K`
  set K₁ := Subgroup.normalClosure ((⁅B.K, Ñ⁆ : Subgroup Y) : Set Y) with hK₁
  have hCK₁ : ⁅B.K, Ñ⁆ ≤ K₁ := Subgroup.le_normalClosure
  have hK₁D : K₁ ≤ D := Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr hKÑD)
  have hK₁K : K₁ ≤ B.K := Subgroup.normalClosure_le_normal
    (SetLike.coe_subset_coe.mpr (Subgroup.commutator_le_left B.K Ñ))
  have hK₁N : K₁.Normal := Subgroup.normalClosure_normal
  -- `K₁ ⊔ S = P` (the chief dichotomy: `= S` contradicts nontriviality)
  have hK₁gen : K₁ ⊔ B.S = B.P := by
    have hle : K₁ ⊔ B.S ≤ B.P := sup_le (hK₁K.trans B.hKP) B.hSP.le
    have hSle : B.S ≤ K₁ ⊔ B.S := le_sup_right
    rcases B.chief _ (Subgroup.sup_normal K₁ B.S) hSle hle with hEqS | hEqP
    · exfalso
      -- `K₁ ⊔ S = S ⟹ ⁅K,Ñ⁆ ≤ S`, so every `[y, p]` (`p ∈ P`) lands in `S`
      have hKÑS : ⁅B.K, Ñ⁆ ≤ B.S := hCK₁.trans (le_sup_left.trans hEqS.le)
      apply hpwS
      -- `pw = k * s`
      have hmem : pw ∈ (B.K : Set Y) * (B.S : Set Y) := by
        rw [← Subgroup.mul_normal, B.gen]; exact hpwP
      obtain ⟨k, hk, s, hs, rfl⟩ := hmem
      -- `[y, k] ∈ ⁅Ñ, K⁆ = ⁅K, Ñ⁆ ≤ S`
      have hyk : y * k * y⁻¹ * k⁻¹ ∈ B.S := by
        have : y * k * y⁻¹ * k⁻¹ ∈ ⁅Ñ, B.K⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) hk
        rw [Subgroup.commutator_comm] at this
        exact hKÑS this
      -- `[y, s] ∈ ⁅Ñ, S⁆ = ⊥`
      have hys : y * s * y⁻¹ * s⁻¹ = 1 := by
        have : y * s * y⁻¹ * s⁻¹ ∈ ⁅Ñ, B.S⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) hs
        rwa [hÑS, Subgroup.mem_bot] at this
      have hexp : y * (k * s) * y⁻¹ * (k * s)⁻¹
          = (y * k * y⁻¹ * k⁻¹) * (k * (y * s * y⁻¹ * s⁻¹) * k⁻¹) := by group
      rw [hexp, hys]
      simpa using hyk
    · exact hEqP
  -- minimality forces `K₁ = K`, hence `K ≤ D ≤ C_Y(R)`: conclusion (a)
  have hK₁eq : K₁ = B.K := B.minimal K₁ hK₁N hK₁K hK₁gen
  have hKcentR : B.K ≤ Subgroup.centralizer (B.frattiniK : Set Y) := by
    rw [← hK₁eq]; exact hK₁D.trans inf_le_right
  have hRcentral : ∀ r ∈ B.frattiniK, ∀ k ∈ B.K, r * k = k * r := fun r hr k hk =>
    (Subgroup.mem_centralizer_iff.mp (hKcentR hk) r hr)
  -- squares and commutators of `K` land in `R = Φ(K)`
  have hksq : ∀ k, k ∈ B.K → k * k ∈ B.frattiniK := fun k hk =>
    Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)
  have hcommR : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → k * l * k⁻¹ * l⁻¹ ∈ B.frattiniK := fun k hk l hl =>
    Subgroup.subset_closure (Or.inr ⟨k, hk, l, hl, rfl⟩)
  -- `group` will not expand `x ^ (4 : ℕ)`; unfold it explicitly wherever it meets a product
  have hp4 : ∀ x : Y, x ^ 4 = x * x * x * x := fun x => by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  -- `[k,l]² = 1`
  have hcomm2 : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → (k * l * k⁻¹ * l⁻¹) * (k * l * k⁻¹ * l⁻¹) = 1 := by
    intro k hk l hl
    have hkkl : (k * k) * l * (k * k)⁻¹ * l⁻¹ = 1 := by
      have hc := hRcentral (k * k) (hksq k hk) l hl
      rw [hc]; group
    have hexp : (k * k) * l * (k * k)⁻¹ * l⁻¹
        = k * (k * l * k⁻¹ * l⁻¹) * k⁻¹ * (k * l * k⁻¹ * l⁻¹) := by group
    have hkc : k * (k * l * k⁻¹ * l⁻¹) * k⁻¹ = k * l * k⁻¹ * l⁻¹ := by
      have hc := hRcentral (k * l * k⁻¹ * l⁻¹) (hcommR k hk l hl) k hk
      rw [show k * (k * l * k⁻¹ * l⁻¹) = (k * l * k⁻¹ * l⁻¹) * k from hc.symm]
      group
    rw [hexp, hkc] at hkkl
    exact hkkl
  -- `(k*l)^4 = k^4 * l^4` (class-2 algebra with `[k,l]^2 = 1`)
  have hf_hom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → (k * l) ^ 4 = k ^ 4 * l ^ 4 := by
    intro k hk l hl
    have hclk : l * k * l⁻¹ * k⁻¹ ∈ B.frattiniK := hcommR l hl k hk
    have hc' : k * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * k :=
      (hRcentral (l * k * l⁻¹ * k⁻¹) hclk k hk).symm
    have hsq : (k * l) ^ 2 = (l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l) := by
      calc (k * l) ^ 2
          = k * (l * k * l⁻¹ * k⁻¹) * (k * l * l) := by rw [pow_two]; group
        _ = (l * k * l⁻¹ * k⁻¹) * k * (k * l * l) := by rw [hc']
        _ = (l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l) := by group
    have hlk2 : (l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹) = 1 := hcomm2 l hl k hk
    -- three central factors commute pairwise
    have s1 : (l * l) * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * (l * l) :=
      hRcentral (l * l) (hksq l hl) _ (frattiniLike_le B.K hclk)
    have s2 : (k * k) * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * (k * k) :=
      hRcentral (k * k) (hksq k hk) _ (frattiniLike_le B.K hclk)
    have s3 : (l * l) * (k * k) = (k * k) * (l * l) :=
      hRcentral (l * l) (hksq l hl) _ (mul_mem hk hk)
    have h4 : (k * l) ^ 4 = ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l))
        * ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l)) := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two]
    rw [h4]
    calc ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l)) * ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l))
        = (l * k * l⁻¹ * k⁻¹) * (k * k) * ((l * l) * (l * k * l⁻¹ * k⁻¹)) * (k * k) * (l * l) := by
          group
      _ = (l * k * l⁻¹ * k⁻¹) * (k * k) * ((l * k * l⁻¹ * k⁻¹) * (l * l)) * (k * k) * (l * l) := by
          rw [s1]
      _ = (l * k * l⁻¹ * k⁻¹) * ((k * k) * (l * k * l⁻¹ * k⁻¹)) * (l * l) * (k * k) * (l * l) := by
          group
      _ = (l * k * l⁻¹ * k⁻¹) * ((l * k * l⁻¹ * k⁻¹) * (k * k)) * (l * l) * (k * k) * (l * l) := by
          rw [s2]
      _ = (l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹) * (k * k) * ((l * l) * (k * k)) * (l * l) := by
          group
      _ = (l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹) * (k * k) * ((k * k) * (l * l)) * (l * l) := by
          rw [s3]
      _ = ((l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹)) * ((k * k) * (k * k)) *
            ((l * l) * (l * l)) := by
          group
      _ = 1 * ((k * k) * (k * k)) * ((l * l) * (l * l)) := by rw [hlk2]
      _ = k ^ 4 * l ^ 4 := by rw [one_mul, hp4 k, hp4 l]; group
  -- `f k = k^4 ∈ R`
  have hf_mem : ∀ k, k ∈ B.K → k ^ 4 ∈ B.frattiniK := by
    intro k hk
    rw [show k ^ 4 = (k * k) * (k * k) by rw [hp4 k]; group]
    exact mul_mem (hksq k hk) (hksq k hk)
  -- the `Y`-normal subgroup `Kf = {k ∈ K | k^4 = 1}` contains `⁅K,Ñ⁆`, hence all of `K`
  have hf_ker : ∀ k, k ∈ B.K → k ^ 4 = 1 := by
    let Kf : Subgroup Y :=
      { carrier := {k | k ∈ B.K ∧ k ^ 4 = 1}
        one_mem' := ⟨one_mem _, one_pow 4⟩
        mul_mem' := by
          rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
          exact ⟨mul_mem haK hbK, by rw [hf_hom a haK b hbK, ha, hb, one_mul]⟩
        inv_mem' := by
          rintro a ⟨haK, ha⟩
          exact ⟨inv_mem haK, by rw [show a⁻¹ ^ 4 = (a ^ 4)⁻¹ by group, ha, inv_one]⟩ }
    have : Kf.Normal := by
      refine ⟨fun a ha g => ⟨B.hK.conj_mem a ha.1 g, ?_⟩⟩
      rw [show (g * a * g⁻¹) ^ 4 = g * a ^ 4 * g⁻¹ by rw [hp4 (g * a * g⁻¹), hp4 a]; group,
        ha.2]; group
    have hKÑKf : ⁅B.K, Ñ⁆ ≤ Kf := by
      rw [Subgroup.commutator_le]
      intro k hk n hn
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        simpa [mul_assoc] using mul_mem hk (B.hK.conj_mem k⁻¹ (inv_mem hk) n)
      · rw [commutatorElement_def]
        have hkn : k * n * k⁻¹ * n⁻¹ = k * (n * k⁻¹ * n⁻¹) := by group
        have hnkK : n * k⁻¹ * n⁻¹ ∈ B.K := B.hK.conj_mem k⁻¹ (inv_mem hk) n
        rw [hkn, hf_hom k hk _ hnkK,
          show (n * k⁻¹ * n⁻¹) ^ 4 = n * (k ^ 4)⁻¹ * n⁻¹ by
            rw [hp4 (n * k⁻¹ * n⁻¹), hp4 k]; group]
        have hn' : n ∈ Subgroup.centralizer (B.frattiniK : Set Y) := hÑcentR hn
        have hcomm := Subgroup.mem_centralizer_iff.mp hn' (k ^ 4) (hf_mem k hk)
        have hncent : n * (k ^ 4)⁻¹ * n⁻¹ = (k ^ 4)⁻¹ := by
          calc n * (k ^ 4)⁻¹ * n⁻¹ = (n * k ^ 4 * n⁻¹)⁻¹ := by group
            _ = (k ^ 4 * n * n⁻¹)⁻¹ := by rw [← hcomm]
            _ = (k ^ 4)⁻¹ := by group
        rw [hncent]; group
    have hKKf : B.K ≤ Kf := by
      rw [← hK₁eq]; exact Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr hKÑKf)
    exact fun k hk => (hKKf hk).2
  refine ⟨hRcentral, ?_, hf_ker⟩
  -- `r^2 = 1`: `R = Φ(K)` is generated by squares (`k^4=1`) and commutators (`[k,l]^2=1`),
  -- and `R` is abelian (central in `K ⊇ R`), so the involution property closes under products.
  intro r hr
  have key : ∀ x ∈ frattiniLike B.K, x * x = 1 := by
    intro x hx
    refine Subgroup.closure_induction (p := fun g _ => g * g = 1) ?_ ?_ ?_ ?_ hx
    · rintro g (⟨k, hk, rfl⟩ | ⟨k, hk, l, hl, rfl⟩)
      · rw [show (k * k) * (k * k) = k ^ 4 by rw [hp4 k]; group]; exact hf_ker k hk
      · exact hcomm2 k hk l hl
    · exact one_mul 1
    · intro a b ha_mem hb_mem ha hb
      have hbK : b ∈ B.K := frattiniLike_le B.K hb_mem
      have hab : a * b = b * a := hRcentral a ha_mem b hbK
      calc (a * b) * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = (a * a) * (b * b) := by group
        _ = 1 := by rw [ha, hb, mul_one]
    · intro a _ ha
      rw [show a⁻¹ * a⁻¹ = (a * a)⁻¹ by group, ha, inv_one]
  exact key r hr

omit [Finite Y] in
/-- **Lemma 7.3 (decorations vanish on the block)**: every homomorphism from `Y` to an
elementary abelian 2-group kills `K` (via Lemma 7.1's dual clause).  The frame decorations
`θ_Y` of `GQ2.MarkedTarget` are such homomorphisms.  [P-14 statement; proof P-15: a nonzero
value `f k₀ ≠ 1` yields — through the `𝔽₂`-module structure on `Additive E` and a separating
dual functional — a `C₂`-character of `Y` nontrivial on `K` and killing `R`, whose kernel meets
`K` in a `Y`-normal index-2 subgroup above `R`, contradicting `lemma_7_1_dual`.
Finiteness-free.] -/
theorem lemma_7_3 (B : MinimalBlock L)
    {E : Type} [CommGroup E] (hE : ∀ e : E, e ^ 2 = 1) (f : Y →* E) :
    B.K ≤ f.ker := by
  by_contra hnot
  rw [SetLike.le_def] at hnot
  simp only [not_forall] at hnot
  obtain ⟨k₀, hk₀K, hk₀⟩ := hnot
  rw [MonoidHom.mem_ker] at hk₀
  -- `Additive E` is an `𝔽₂`-vector space
  letI : Module (ZMod 2) (Additive E) := AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hE x.toMul)
  -- a functional separating `f k₀` from `0`
  have hw : Additive.ofMul (f k₀) ≠ (0 : Additive E) := by simpa using hk₀
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ZMod 2) (Additive E),
      φ (Additive.ofMul (f k₀)) ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hw ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp hall)
  -- the induced `C₂`-character of `Y`
  set g : Y →* Multiplicative (ZMod 2) :=
    (AddMonoidHom.toMultiplicativeRight φ.toAddMonoidHom).comp f with hg
  have hgk₀ : g k₀ ≠ 1 := by
    rw [hg]
    simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply]
    intro h
    apply hφ
    simpa using congrArg Multiplicative.toAdd h
  -- `R` dies under `g` (squares and commutators die in `C₂`)
  have hRker : frattiniLike B.K ≤ g.ker := by
    refine (Subgroup.closure_le _).mpr ?_
    have hsq : ∀ x : Multiplicative (ZMod 2), x * x = 1 := by decide
    have hab : ∀ a b : Multiplicative (ZMod 2), a * b * a⁻¹ * b⁻¹ = 1 := by decide
    rintro x (⟨k, hk, rfl⟩ | ⟨k, hk, l, hl, rfl⟩)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul]
      exact hsq _
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      exact hab _ _
  -- the kernel meets `K` in a `Y`-normal index-2 subgroup above `R`
  have hXn : (g.ker ⊓ B.K).Normal := ⟨fun n hn y => Subgroup.mem_inf.mpr
    ⟨g.normal_ker.conj_mem _ (Subgroup.mem_inf.mp hn).1 y,
      B.hK.conj_mem _ (Subgroup.mem_inf.mp hn).2 y⟩⟩
  set g' : B.K →* Multiplicative (ZMod 2) := g.comp B.K.subtype with hg'
  have hker' : (g.ker ⊓ B.K).subgroupOf B.K = g'.ker := by
    ext ⟨y, hy⟩
    simp [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, hg']
  have hidx : ((g.ker ⊓ B.K).subgroupOf B.K).index = 2 := by
    rw [hker', Subgroup.index_ker]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hdvd : Nat.card g'.range ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card g'.range
      rwa [h2] at h
    rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
    · exfalso
      have hbot : g'.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hmem : g' ⟨k₀, hk₀K⟩ ∈ g'.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hgk₀ hmem
    · exact h1
  exact lemma_7_1_dual B ⟨g.ker ⊓ B.K, hXn,
    le_inf hRker (frattiniLike_le B.K), inf_le_right, hidx⟩


end SectionSeven

end GQ2
