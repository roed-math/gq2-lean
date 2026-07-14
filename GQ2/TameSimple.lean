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
  one_mem' v := by simp
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
  one_mem' c v := by simp
  mul_mem' {a b} ha hb c v := by rw [mul_smul, mul_smul, hb, ha]
  inv_mem' {a} ha c v := by
    have h := ha c (a⁻¹ • v)
    rw [smul_inv_smul] at h
    rw [← h, inv_smul_smul]

variable [Finite V]

omit [Finite C] in
/-- **Nonvanishing of 2-group fixed points, subgroup-packaged**: on a nontrivial finite module of
exponent 2, an additive subgroup `W` whose carrier is the fixed-point set of a 2-power-order
`⟨g⟩` is nonzero — `p`-group fixed points mod `p = 2`, with `#V` even.  The shared `hWne` engine
of `central_pow2_smul_trivial` and `pow2_smul_trivial_of_stable`. -/
private theorem fixedPoints_addSubgroup_ne_bot [Nontrivial V] (hV₂ : ∀ v : V, v + v = 0)
    (g : C) (hpow : IsPGroup 2 (Subgroup.zpowers g)) (W : AddSubgroup V)
    (hset : (MulAction.fixedPoints ↥(Subgroup.zpowers g) V : Set V) = (W : Set V)) :
    W ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- `|V|` even
  have h2 : 2 ∣ Nat.card V := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hord : addOrderOf v = 2 := addOrderOf_eq_prime (by rw [two_nsmul]; exact hV₂ v) hv
    exact hord ▸ addOrderOf_dvd_natCard v
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

omit [Finite C] in
/-- **The central fixed-point lemma** (analogue of `lemma_5_12` with centrality for normality):
a 2-power-order element `g` whose action commutes with the whole `C`-action acts trivially on a
simple char-2 module.  Its fixed space is `C`-stable (centrality) and nonzero (`p`-group fixed
points, char 2), so simplicity makes it everything. -/
theorem central_pow2_smul_trivial (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (g : C) (hpow : IsPGroup 2 (Subgroup.zpowers g))
    (hcentral : ∀ (c : C) (v : V), g • (c • v) = c • (g • v)) :
    ∀ v : V, g • v = v := by
  haveI : Nontrivial V := hsimple.1
  -- every zpower of `g` is central too
  have hcomm : ∀ h ∈ Subgroup.zpowers g, ∀ (c : C) (v : V), h • (c • v) = c • (h • v) :=
    fun _ hh => Subgroup.zpowers_le.mpr
      (show g ∈ actionCentre (C := C) (V := V) from hcentral) hh
  -- the fixed space of `⟨g⟩`
  let W : AddSubgroup V :=
    { carrier := {v | ∀ h ∈ Subgroup.zpowers g, h • v = v}
      zero_mem' := fun h _ => smul_zero h
      add_mem' := fun {a b} ha hb h hh => by rw [smul_add, ha h hh, hb h hh]
      neg_mem' := fun {a} ha h hh => by rw [smul_neg, ha h hh] }
  -- `C`-stable by centrality
  have hstable : ∀ (c : C) (w : V), w ∈ W → c • w ∈ W := by
    intro c w hw h hh
    rw [hcomm h hh c w, hw h hh]
  -- fixed points of `↥⟨g⟩` coincide with `W`
  have hset : (MulAction.fixedPoints ↥(Subgroup.zpowers g) V : Set V) = (W : Set V) := by
    ext v
    refine ⟨fun h g hg => h ⟨g, hg⟩, fun h g => h g.1 g.2⟩
  -- `W ≠ ⊥`: 2-group fixed points on an even-cardinality module
  have hWne : W ≠ ⊥ := fixedPoints_addSubgroup_ne_bot hV₂ g hpow W hset
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

omit [Finite C] [Finite V] in
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

omit [Finite C] in
/-- **The stable fixed-point lemma** (the `central_pow2_smul_trivial` mechanism with `C`-stability
of the fixed space assumed instead of derived from centrality): a 2-power-order `g` whose fixed
space is `C`-stable acts trivially on a simple char-2 module.  This is what the *ramified* tame
providers need — there `powOmega2 τ` is not central (`σ` conjugates it to its square), but its
fixed space is still `C`-stable via the tame relation. -/
theorem pow2_smul_trivial_of_stable (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V)
    (g : C) (hpow : IsPGroup 2 (Subgroup.zpowers g))
    (hstable : ∀ (c : C) (v : V), g • v = v → g • (c • v) = c • v) :
    ∀ v : V, g • v = v := by
  haveI : Nontrivial V := hsimple.1
  -- the fixed space of `g` (fixed by `g` ⟺ fixed by all of `⟨g⟩`, via the stabilizer subgroup)
  let W : AddSubgroup V :=
    { carrier := {v | g • v = v}
      zero_mem' := smul_zero g
      add_mem' := fun {a b} ha hb => by show g • (a + b) = a + b; rw [smul_add, ha, hb]
      neg_mem' := fun {a} ha => by show g • (-a) = -a; rw [smul_neg, ha] }
  -- fixed points of `↥⟨g⟩` coincide with `W`
  have hset : (MulAction.fixedPoints ↥(Subgroup.zpowers g) V : Set V) = (W : Set V) := by
    ext v
    refine ⟨fun h => h ⟨g, Subgroup.mem_zpowers g⟩, fun h ⟨x, hx⟩ => ?_⟩
    have hle : Subgroup.zpowers g ≤ MulAction.stabilizer C v :=
      Subgroup.zpowers_le.mpr (by rwa [MulAction.mem_stabilizer_iff])
    exact hle hx
  -- `W ≠ ⊥`: 2-group fixed points on an even-cardinality module
  have hWne : W ≠ ⊥ := fixedPoints_addSubgroup_ne_bot hV₂ g hpow W hset
  rcases hsimple.2 W hstable with h | h
  · exact absurd h hWne
  · intro v
    exact (h ▸ AddSubgroup.mem_top v : v ∈ W)

/-- The tame relation conjugates the 2-primary part of `τ` to its square:
`σ⁻¹ · τ^{ω₂} · σ = (τ^{ω₂})²` — `powOmega2` naturality under `MulAut.conj σ⁻¹` plus
`powOmega2 (τ²) = (powOmega2 τ)²` (exponent independence `powOmega2_pow_eq`). -/
theorem conj_powOmega2_tau (t : Marking C) (ht : t.TameRel) :
    t.σ⁻¹ * powOmega2 t.τ * t.σ = (powOmega2 t.τ) ^ 2 := by
  have htame : t.σ⁻¹ * t.τ * t.σ = t.τ ^ 2 := by
    have h := ht; rw [Marking.TameRel, conjP] at h; exact h
  have hconj : t.σ⁻¹ * powOmega2 t.τ * t.σ = powOmega2 (t.σ⁻¹ * t.τ * t.σ) := by
    simpa [MulAut.conj_apply, mul_assoc] using powOmega2_map (MulAut.conj t.σ⁻¹).toMonoidHom t.τ
  have hne : orderOf t.τ ≠ 0 := (orderOf_pos t.τ).ne'
  have hdvd : orderOf (t.τ ^ 2) ∣ orderOf t.τ :=
    orderOf_dvd_of_pow_eq_one (by rw [← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow])
  have hpow2 : powOmega2 (t.τ ^ 2) = (powOmega2 t.τ) ^ 2 := by
    rw [← powOmega2_pow_eq (t.τ ^ 2) hdvd hne, ← pow_mul, mul_comm 2, pow_mul]
    rfl
  rw [hconj, htame, hpow2]

/-- **P-13d ramified output `hTodd`**: on a simple char-2 module at a generating admissible-style
marking, the 2-primary part `τ^{ω₂}` of the tame generator acts trivially — i.e. `τ` acts with odd
order.  Its fixed space is `C`-stable: `σ` preserves it via `conj_powOmega2_tau` (a `τ^{ω₂}`-fixed
vector is fixed by `(τ^{ω₂})²`), `τ` commutes with its own power, and `x₀, x₁` act trivially
(`wild_acts_trivially`); `⟨τ^{ω₂}⟩` is a 2-group, so `pow2_smul_trivial_of_stable` closes.  Unlike
the split `hU = sigma2_smul_trivial`, no hypothesis on how `τ` acts is needed. -/
theorem tau_powOmega2_smul_trivial (t : Marking C) (ht : t.TameRel) (hgen : t.Generates)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) (hcore : t.Pro2Core) :
    ∀ v : V, powOmega2 t.τ • v = v := by
  obtain ⟨hx0, hx1⟩ := wild_acts_trivially t hV₂ hsimple hcore
  refine pow2_smul_trivial_of_stable hV₂ hsimple (powOmega2 t.τ)
    (isPGroup_zpowers_powOmega2 t.τ) ?_
  -- the stabilizer of the fixed set is a subgroup containing the four generators
  have hσ : ∀ v : V, powOmega2 t.τ • v = v → powOmega2 t.τ • (t.σ • v) = t.σ • v := by
    intro v hv
    have hkey : powOmega2 t.τ * t.σ = t.σ * ((powOmega2 t.τ) ^ 2) := by
      rw [← conj_powOmega2_tau t ht]; group
    calc powOmega2 t.τ • (t.σ • v) = (powOmega2 t.τ * t.σ) • v := (mul_smul _ _ _).symm
      _ = (t.σ * ((powOmega2 t.τ) ^ 2)) • v := by rw [hkey]
      _ = t.σ • ((powOmega2 t.τ) ^ 2 • v) := mul_smul _ _ _
      _ = t.σ • v := by rw [pow_two, mul_smul, hv, hv]
  have hτ : ∀ v : V, powOmega2 t.τ • v = v → powOmega2 t.τ • (t.τ • v) = t.τ • v := by
    intro v hv
    have hcomm : powOmega2 t.τ * t.τ = t.τ * powOmega2 t.τ := by
      rw [powOmega2]
      exact ((Commute.refl t.τ).pow_left _).eq
    rw [← mul_smul, hcomm, mul_smul, hv]
  let S : Subgroup C :=
    { carrier := {c | ∀ v : V, powOmega2 t.τ • v = v → powOmega2 t.τ • (c • v) = c • v}
      one_mem' := fun v hv => by rwa [one_smul]
      mul_mem' := fun {a b} ha hb v hv => by rw [mul_smul]; exact ha _ (hb v hv)
      inv_mem' := fun {a} ha v hv => by
        -- `a` maps the finite fixed set into itself, hence bijectively
        let W : AddSubgroup V :=
          { carrier := {w | powOmega2 t.τ • w = w}
            zero_mem' := smul_zero _
            add_mem' := fun {x y} hx hy => by
              show powOmega2 t.τ • (x + y) = x + y; rw [smul_add, hx, hy]
            neg_mem' := fun {x} hx => by
              show powOmega2 t.τ • (-x) = -x; rw [smul_neg, hx] }
        have hφinj : Function.Injective (fun u : W => (⟨a • u.1, ha u.1 u.2⟩ : W)) := by
          intro x y hxy
          exact Subtype.ext (MulAction.injective a (congrArg Subtype.val hxy))
        obtain ⟨⟨u, hu⟩, hux⟩ := (Finite.injective_iff_surjective.mp hφinj) ⟨v, hv⟩
        have huv : a • u = v := congrArg Subtype.val hux
        rw [show a⁻¹ • v = u from by rw [← huv, inv_smul_smul]]
        exact hu }
  have hgenS : Subgroup.closure {t.σ, t.τ, t.x₀, t.x₁} ≤ S := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact hσ
    · exact hτ
    · intro v hv; rw [hx0 v]; exact hv
    · intro v hv; rw [hx1 v]; exact hv
  rw [hgen] at hgenS
  exact fun c => hgenS (Subgroup.mem_top c)

omit [Finite V] in
/-- **The ramified pairing operator `1 + U + U⁻¹` is injective** for `U = σ₂` on a char-2 module —
with *no* hypothesis on how `σ₂` acts.  `U` has 2-power order (`orderOf_powOmega2_dvd_two_pow`),
so in char 2 the operator is unipotent: writing `E_j(w) = U^{2^j}w + w = (U+1)^{2^j}w`, the
`U`-scaled kernel equation gives `E_1(v) = Uv`, squaring inductively gives
`E_{j+1}(v) = U^{2^j}v`, and at `2^j = ` the order both sides collapse to `0 = v`.  This is the
nondegeneracy engine for the ramified pairing `λ((1+U+U⁻¹)c)` of `lemma_5_13_pairing_ramified`. -/
theorem sigma2_pairing_operator_injective (t : Marking C) (hV₂ : ∀ v : V, v + v = 0) :
    Function.Injective (fun v : V => v + t.sigma2 • v + t.sigma2⁻¹ • v) := by
  have hneg : ∀ w : V, -w = w := fun w => neg_eq_of_add_eq_zero_left (hV₂ w)
  set U := t.sigma2 with hUdef
  set k := (orderOf t.σ).factorization 2 with hkdef
  have h2k : U ^ 2 ^ k = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_powOmega2_dvd_two_pow t.σ)
  -- kernel triviality
  have hker : ∀ v : V, v + U • v + U⁻¹ • v = 0 → v = 0 := by
    intro v hv
    -- the `U`-scaled kernel equation: `U²v + v = Uv`
    have hUv : U ^ 2 • v + v = U • v := by
      have h := congrArg (fun w : V => U • w) hv
      simp only [smul_add, smul_zero] at h
      rw [smul_inv_smul, ← mul_smul, ← pow_two] at h
      have h2 : U • v + (U ^ 2 • v + v) = 0 := by rw [← h]; abel
      have h3 := neg_eq_of_add_eq_zero_right h2
      rw [hneg] at h3
      exact h3.symm
    -- squaring: `E_j (E_j w) = E_{j+1} w` for `E_j w = U^{2^j}w + w`
    have hdouble : ∀ (j : ℕ) (w : V),
        U ^ 2 ^ j • (U ^ 2 ^ j • w + w) + (U ^ 2 ^ j • w + w) = U ^ 2 ^ (j + 1) • w + w := by
      intro j w
      rw [smul_add, ← mul_smul, ← pow_add, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) from by ring]
      rw [show U ^ 2 ^ (j + 1) • w + U ^ 2 ^ j • w + (U ^ 2 ^ j • w + w)
          = U ^ 2 ^ (j + 1) • w + w + (U ^ 2 ^ j • w + U ^ 2 ^ j • w) from by abel, hV₂, add_zero]
    -- inductively: `E_{j+1}(v) = U^{2^j} v`
    have hQ : ∀ j : ℕ, U ^ 2 ^ (j + 1) • v + v = U ^ 2 ^ j • v := by
      intro j
      induction j with
      | zero => simpa [pow_one] using hUv
      | succ j ih =>
        have hd := hdouble (j + 1) v
        rw [ih] at hd
        rw [← hd, show U ^ 2 ^ (j + 1) • U ^ 2 ^ j • v + U ^ 2 ^ j • v
            = U ^ 2 ^ j • (U ^ 2 ^ (j + 1) • v + v) from by
              rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add,
                add_comm (2 ^ (j + 1)) (2 ^ j)],
          ih, ← mul_smul, ← pow_add, show 2 ^ j + 2 ^ j = 2 ^ (j + 1) from by ring]
    -- specialize at the order: both sides collapse
    have hfin := hQ k
    rw [show 2 ^ (k + 1) = 2 ^ k * 2 from by ring, pow_mul, h2k, one_pow, one_smul,
      hV₂ v] at hfin
    exact hfin.symm
  -- injectivity from kernel triviality (the operator is additive)
  intro a b hab
  simp only at hab
  have hd : (a - b) + U • (a - b) + U⁻¹ • (a - b) = 0 := by
    rw [smul_sub, smul_sub, show a - b + (U • a - U • b) + (U⁻¹ • a - U⁻¹ • b)
        = a + U • a + U⁻¹ • a - (b + U • b + U⁻¹ • b) from by abel, hab, sub_self]
  exact sub_eq_zero.mp (hker _ hd)

omit [Finite C] in
/-- **P-13d output `hVS`**: on a nontrivial simple char-2 module at a *generating* split-tame
marking
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
  · exact fun v hv => AddSubgroup.mem_bot.mp (h ▸ (hv : v ∈ W))
  · obtain ⟨v, hv⟩ := hσ
    exact absurd (h.ge (AddSubgroup.mem_top v)) hv

end GQ2.FoxH
