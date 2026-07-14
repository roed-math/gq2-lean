import GQ2.GaussSigns
import GQ2.TameSimple

/-!
# Ramified Arf value (Lemma 6.8 (87)):  `arf q = s`  via the `⟨T⟩` route  (ticket P-15b)

The ramified Arf value is computed **without** the Hermitian model, involution, or norm-one group:
tame inertia `⟨T⟩` itself acts diagonally on `V ≅ W^{⊕s}` (the isotypic decomposition), freely on
`V ∖ 0` (`T` fixes only `0` in the simple faithful `W`), preserving `q`.  Feeding
`GaussSigns.arf_eq_of_free` with `U = ⟨T⟩` and `n = ord(T)` — using `ord(T) ∣ 2^{2m'} − 1`
(`T` a unit of the field `𝔽₂[T] ≅ 𝔽_{2^f}`) and `ord(T) ∤ 2^{m'} − 1`
(`irreducible_operator_pow_ne_one`) —
pins `arf q = s`.

Reuses P-13d (`GQ2/TameSimple.lean`): `IsSimpleModTwo`.

No `sorry`.
-/

open Polynomial Module

namespace GQ2.GaussSigns

open QuadraticFp2

/-! ### The field-order lemma: an irreducible operator is a unit of `𝔽₂[T] ≅ 𝔽_{2^f}` -/

section FieldOrder

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

/-- **An irreducible `𝔽₂`-operator on a `2m`-dimensional space has `T^{2^{2m} − 1} = 1`**: `T` is a
nonzero element of the field `𝔽₂[T] ≅ AdjoinRoot(minpoly T) ≅ 𝔽_{2^{2m}}`, so `T^{#field − 1} = 1`.
Hence `ord(T) ∣ 2^{2m} − 1`. -/
theorem irreducible_operator_pow_card_sub_one (m : ℕ)
    (hdim : Module.finrank (ZMod 2) W = 2 * m) (T : Module.End (ZMod 2) W)
    (hV : Nontrivial W)
    (hirr : ∀ U : Submodule (ZMod 2) W, U ≠ ⊥ → U ≠ ⊤ → ∃ w ∈ U, T w ∉ U) :
    T ^ (2 ^ (2 * m) - 1) = 1 := by
  have hirred : Irreducible (minpoly (ZMod 2) T) :=
    minpoly_irreducible_of_noInvariant T hV hirr
  haveI : Fact (Irreducible (minpoly (ZMod 2) T)) := ⟨hirred⟩
  set f := minpoly (ZMod 2) T with hf
  have hne : f ≠ 0 := hirred.ne_zero
  have hdeg : f.natDegree = 2 * m := by
    rw [hf, ← hdim]; exact (finrank_eq_natDegree_minpoly T hV hirr).symm
  have hm1 : 1 ≤ m := by
    have hpos : 0 < Module.finrank (ZMod 2) W := Module.finrank_pos
    omega
  haveI : Module.Finite (ZMod 2) (AdjoinRoot f) :=
    Module.Finite.of_basis (AdjoinRoot.powerBasis hne).basis
  haveI : Finite (AdjoinRoot f) := Module.finite_of_finite (ZMod 2)
  letI : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  -- `K := AdjoinRoot f ≅ 𝔽_{2^{2m}}`
  have hfr : Module.finrank (ZMod 2) (AdjoinRoot f) = 2 * m := by
    rw [(AdjoinRoot.powerBasis hne).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hcard : Fintype.card (AdjoinRoot f) = 2 ^ (2 * m) := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hfr]
  -- the root is a nonzero element of the field, so `root^{#K − 1} = 1`
  have hroot_ne : (AdjoinRoot.root f) ≠ 0 := by
    rw [← AdjoinRoot.mk_X, Ne, AdjoinRoot.mk_eq_zero]
    intro hdvd
    have := Polynomial.natDegree_le_of_dvd hdvd (Polynomial.X_ne_zero)
    rw [natDegree_X] at this
    omega
  have hroot_pow : (AdjoinRoot.root f) ^ (2 ^ (2 * m) - 1) = 1 := by
    rw [← hcard]; exact FiniteField.pow_card_sub_one_eq_one _ hroot_ne
  -- `f ∣ X^{2^{2m}−1} − 1`, so `aeval T (X^{2^{2m}−1} − 1) = 0`, i.e. `T^{2^{2m}−1} = 1`
  have hdvd : f ∣ (X ^ (2 ^ (2 * m) - 1) - 1 : (ZMod 2)[X]) := by
    apply AdjoinRoot.mk_eq_zero.mp
    rw [map_sub, map_one, map_pow, AdjoinRoot.mk_X, hroot_pow, sub_self]
  obtain ⟨g, hg⟩ := hdvd
  have haev : Polynomial.aeval T (X ^ (2 ^ (2 * m) - 1) - 1 : (ZMod 2)[X]) = 0 := by
    rw [hg, map_mul, show Polynomial.aeval T f = 0 from minpoly.aeval (ZMod 2) T, zero_mul]
  rw [map_sub, map_pow, aeval_X, map_one] at haev
  exact sub_eq_zero.mp haev

end FieldOrder

/-! ### Lemma 6.8 (87): `arf q = s` via the `⟨T⟩` route -/

section ArfRamified

variable {V : Type*} [AddCommGroup V] [Finite V] {W : Type*} [AddCommGroup W]
  {G : Type*} [Group G] [Finite G] [DistribMulAction G V] [DistribMulAction G W]

omit [Finite V] in
/-- **Isotypic card count**: from `V ≅ W^{⊕s}` and `#W = 2^{2m'}` one gets `#V = 2^{2·m'·s}`. -/
private theorem isotypic_card_eq (m' s : ℕ) (hWcard : Nat.card W = 2 ^ (2 * m'))
    (e : V ≃+ (Fin s → W)) :
    Nat.card V = 2 ^ (2 * (m' * s)) := by
  rw [Nat.card_congr e.toEquiv, Nat.card_pi, Finset.prod_const, hWcard, Finset.card_univ,
    Fintype.card_fin, ← pow_mul]
  congr 1; ring

omit [Finite V] [Finite G] in
/-- **Faithfulness transports to the component**: if `G` acts faithfully on `V ≅ W^{⊕s}`
(equivariantly via `e`), then it acts faithfully on the summand `W`. -/
private theorem faithful_on_component {s : ℕ} (e : V ≃+ (Fin s → W))
    (he : ∀ (g : G) (v : V) (j : Fin s), e (g • v) j = g • e v j)
    (hVfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1) :
    ∀ g : G, (∀ w : W, g • w = w) → g = 1 := by
  intro g hg
  refine hVfaith g (fun v => ?_)
  apply e.injective
  ext j
  rw [he g v j, hg]

/-- **Order lower bound**: an order dividing `2^{2a} − 1` but not `2^a − 1` (`a ≥ 1`) exceeds `2`
(it is odd — else `2 ∣ 2^{2a} − 1` — and it is not `1`). -/
private theorem two_lt_orderOf {n a : ℕ} (ha : 1 ≤ a) (hsub : n ∣ 2 ^ (2 * a) - 1)
    (hnot : ¬ n ∣ 2 ^ a - 1) : 2 < n := by
  have hne1 : n ≠ 1 := fun h1 => hnot (by rw [h1]; exact one_dvd _)
  have hodd : Odd n := by
    rcases Nat.even_or_odd n with h | h
    · exfalso
      have h2d : (2 : ℕ) ∣ 2 ^ (2 * a) - 1 := dvd_trans h.two_dvd hsub
      have hev : (2 : ℕ) ∣ 2 ^ (2 * a) := dvd_pow_self 2 (by omega)
      have h1le : 1 ≤ 2 ^ (2 * a) := Nat.one_le_two_pow
      omega
    · exact h
  rcases hodd with ⟨j, hj⟩; omega

omit [Finite V] [Finite G] in
/-- **Freeness on `V ∖ 0`**: if `g` fixes a nonzero `v`, some `W`-component `e v j₀ ≠ 0` is fixed;
its `G`-stable fixed subgroup `Fg` cannot be `⊥`, so by simplicity `Fg = ⊤`, i.e. `g` fixes all of
`W`, whence `g = 1` by faithfulness. -/
private theorem free_on_nonzero {s : ℕ} (T : G) (e : V ≃+ (Fin s → W))
    (he : ∀ (g : G) (v : V) (j : Fin s), e (g • v) j = g • e v j)
    (hWsimple : GQ2.FoxH.IsSimpleModTwo G W)
    (hnatpow : ∀ g : G, ∃ k : ℕ, T ^ k = g)
    (hWfaith : ∀ g : G, (∀ w : W, g • w = w) → g = 1) :
    ∀ (g : G) (v : V), v ≠ 0 → g • v = v → g = 1 := by
  intro g v hv hgv
  have hcomp : ∀ j, g • e v j = e v j := fun j => by rw [← he g v, hgv]
  obtain ⟨j₀, hj₀⟩ : ∃ j, e v j ≠ 0 := by
    by_contra hc
    simp only [not_exists, not_not] at hc
    exact hv (e.injective (by ext j; rw [hc j]; simp))
  -- `fix(g)` on `W` is a `G`-stable subgroup containing `e v j₀ ≠ 0`, hence `⊤`
  let Fg : AddSubgroup W :=
    { carrier := {w | g • w = w}
      add_mem' := fun {x y} hx hy => by simp only [Set.mem_setOf_eq] at *; rw [smul_add, hx, hy]
      zero_mem' := smul_zero g
      neg_mem' := fun {x} hx => by simp only [Set.mem_setOf_eq] at *; rw [smul_neg, hx] }
  have hFgstab : ∀ (h : G), ∀ w ∈ Fg, h • w ∈ Fg := by
    intro h w hw
    show g • (h • w) = h • w
    obtain ⟨k, rfl⟩ := hnatpow h
    obtain ⟨l, rfl⟩ := hnatpow g
    rw [← mul_smul, ← pow_add, Nat.add_comm, pow_add, mul_smul]
    exact congrArg (T ^ k • ·) hw
  rcases hWsimple.2 Fg hFgstab with hb | ht
  · exact absurd (hb ▸ (hcomp j₀ : g • e v j₀ = e v j₀) : e v j₀ ∈ (⊥ : AddSubgroup W))
      (by rw [AddSubgroup.mem_bot]; exact hj₀)
  · exact hWfaith g (fun w => (ht ▸ AddSubgroup.mem_top w : w ∈ Fg))

/-- **Lemma 6.8 (87)** in engine form: for a finite cyclic `G = ⟨T⟩` acting faithfully on `V`,
simply on the exponent-2 module `W` (`#W = 2^{2m'}`), with `V ≅ W^{⊕s}` `G`-equivariantly (via
`e`, `he`) and a nonsingular `G`-invariant `q`, the Arf invariant is `arf q = s`.

`G` acts diagonally on `V ≅ W^{⊕s}`, freely on `V ∖ 0` (`T` fixes only `0` in the simple faithful
`W`), preserving `q`; `#G = ord(T)` divides `2^{2m'} − 1` (`T` a unit of `𝔽₂[T]`) but not
`2^{m'} − 1` (`T` irreducible on `W`), so `GaussSigns.arf_eq_of_free` gives `arf q = s`. -/
theorem arf_eq_s_ramified (T : G) (hTgen : ∀ g : G, g ∈ Subgroup.zpowers T)
    (hVfaith : ∀ g : G, (∀ v : V, g • v = v) → g = 1)
    (hWsimple : GQ2.FoxH.IsSimpleModTwo G W)
    (_ : ∀ v : V, v + v = 0) (hW2 : ∀ w : W, w + w = 0)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hqinv : ∀ (g : G) (v : V), q (g • v) = q v)
    (m' s : ℕ) (hm' : 1 ≤ m') (hs1 : 1 ≤ s) (hWcard : Nat.card W = 2 ^ (2 * m'))
    (e : V ≃+ (Fin s → W))
    (he : ∀ (g : G) (v : V) (j : Fin s), e (g • v) j = g • e v j) :
    arf q = (s : ZMod 2) := by
  classical
  -- `#V = 2^{2·m'·s}`
  have hVcard : Nat.card V = 2 ^ (2 * (m' * s)) := isotypic_card_eq m' s hWcard e
  haveI : Nontrivial W := hWsimple.1
  -- `W` is finite and an `𝔽₂`-module of dimension `2m'`
  haveI : Finite W := by
    haveI : Finite (Fin s → W) := Finite.of_equiv V e.toEquiv
    exact Finite.of_injective (fun w (_ : Fin s) => w)
      (fun a b hab => congrFun hab ⟨0, by omega⟩)
  letI : Module (ZMod 2) W :=
    AddCommGroup.zmodModule (n := 2) (fun w => by rw [two_nsmul]; exact hW2 w)
  haveI : Module.Finite (ZMod 2) W := (Module.finite_iff_finite (R := ZMod 2)).mpr inferInstance
  have hfrW : Module.finrank (ZMod 2) W = 2 * m' := by
    letI : Fintype W := Fintype.ofFinite W
    have h1 : Fintype.card W = 2 ^ Module.finrank (ZMod 2) W := by
      rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card]
    have hc := hWcard; rw [Nat.card_eq_fintype_card, h1] at hc
    exact Nat.pow_right_injective (le_refl 2) hc
  -- the operator `T_W = (T • ·)` on `W`
  let TW : Module.End (ZMod 2) W :=
    { toFun := fun w => T • w
      map_add' := fun x y => smul_add T x y
      map_smul' := fun c w => map_nsmul (DistribSMul.toAddMonoidHom W T) c.val w }
  have hTWapp : ∀ w, TW w = T • w := fun _ => rfl
  -- nat-power form of `zpowers` membership (finite order)
  have hfin : IsOfFinOrder T :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨orderOf T, orderOf_pos T, pow_orderOf_eq_one T⟩
  have hnatpow : ∀ g : G, ∃ k : ℕ, T ^ k = g := fun g =>
    (Submonoid.mem_powers_iff g T).mp (hfin.mem_powers_iff_mem_zpowers.mpr (hTgen g))
  -- faithfulness of `G` on `W` (transported from `V` via `e`)
  have hWfaith : ∀ g : G, (∀ w : W, g • w = w) → g = 1 := faithful_on_component e he hVfaith
  -- `TW ^ k = 1 ↔ T ^ k = 1` (via faithfulness)
  have hTWpowapp : ∀ (k : ℕ) (w : W), (TW ^ k) w = T ^ k • w := by
    intro k
    induction k with
    | zero => intro w; simp
    | succ k ih => intro w; rw [pow_succ, Module.End.mul_apply, hTWapp, ih, pow_succ, mul_smul]
  have hTWpow : ∀ k : ℕ, TW ^ k = 1 ↔ T ^ k = 1 := by
    intro k
    constructor
    · intro h
      apply hWfaith
      intro w
      simpa [hTWpowapp] using DFunLike.congr_fun h w
    · intro h
      ext w
      rw [Module.End.one_apply, hTWpowapp, h, one_smul]
  -- `T_W` is irreducible (no proper invariant subspace): invariant ⟹ `G`-stable ⟹ `⊥`/`⊤`
  have hirrW : ∀ U : Submodule (ZMod 2) W, U ≠ ⊥ → U ≠ ⊤ → ∃ w ∈ U, TW w ∉ U := by
    intro U hUb hUt
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hpow : ∀ (k : ℕ) (w : W), w ∈ U → T ^ k • w ∈ U := by
      intro k
      induction k with
      | zero => intro w hw; simpa using hw
      | succ k ih =>
        intro w hw
        rw [pow_succ, mul_smul]
        exact ih (T • w) (hcon w hw)
    have hstab : ∀ (g : G), ∀ w ∈ U.toAddSubgroup, g • w ∈ U.toAddSubgroup := by
      intro g w hw
      obtain ⟨k, rfl⟩ := hnatpow g
      exact hpow k w hw
    rcases hWsimple.2 U.toAddSubgroup hstab with hb | ht
    · exact hUb (Submodule.toAddSubgroup_injective (hb.trans Submodule.bot_toAddSubgroup.symm))
    · exact hUt (Submodule.toAddSubgroup_injective (ht.trans Submodule.top_toAddSubgroup.symm))
  -- `ord(T) = #G` and the two divisibility facts
  have hcardG : Nat.card G = orderOf T := by
    rw [← Nat.card_zpowers T]
    exact Nat.card_congr (Equiv.subtypeUnivEquiv hTgen).symm
  have hordsub : orderOf T ∣ 2 ^ (2 * m') - 1 :=
    orderOf_dvd_of_pow_eq_one ((hTWpow _).mp
      (irreducible_operator_pow_card_sub_one m' hfrW TW inferInstance hirrW))
  have hordnot : ¬ orderOf T ∣ 2 ^ m' - 1 := by
    intro hd
    have hTk : T ^ (2 ^ m' - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hd
    rw [← hTWpow] at hTk
    exact irreducible_operator_pow_ne_one m' hm' hfrW TW hirrW hTk
  have hordgt : 2 < orderOf T := two_lt_orderOf hm' hordsub hordnot
  -- assemble via the general Arf-parity engine, `U := G`
  refine arf_eq_of_free q hq hns m' s hm' hs1 hVcard (U := G) ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hcardG]; exact hordsub
  · rw [hcardG]; exact hordnot
  · rw [hcardG]; exact hordgt
  · intro g; exact smul_zero g
  · exact hqinv
  · -- free on `V ∖ 0`: `g • v = v`, `v ≠ 0` ⟹ `g` fixes a nonzero `W`-component ⟹ `g` trivial
    -- ⟹ `g = 1`
    exact free_on_nonzero T e he hWsimple hnatpow hWfaith

end ArfRamified

end GQ2.GaussSigns

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.8 = ⟦lem-ramifiedhermitian⟧
-/
