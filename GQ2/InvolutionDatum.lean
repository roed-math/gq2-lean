import GQ2.OrbitData

/-!
# P-17e3: the involution-orbit datum is an equivariant factor set  (Lemma 6.2)

`GQ2.invOrbitDatum N gbar` (defined in `GQ2/OrbitData.lean`) is the paper's involution-orbit
cocycle `E_ḡ` (Lemma 6.2, eqs. (67)–(73)): for an involution `ḡ` of `C = G/N`, the factor set
`f_g(x,y) = Σ_{u} x_{u} y_{uḡ}` (summed over the `⟨ḡ⟩`-coset transversal, realized as
`Quotient.out`) together with the **nonzero** orientation corrections
`m^g_c(x) = Σ_u ε_c(u)·x_{π_c(u)} x_{π_c(u)ḡ}`.

This file proves `isEquivariantFactorSet_invOrbitDatum`: the seven `IsEquivariantFactorSet`
identities, the hard ones being (71) `m_quad` and (72) `m_mul`.  Own file (imports only
`OrbitData`); spliced into the §9 layer by the consumer (`kappa0_exists` orbit-sum, P-17e5).

## The transversal bookkeeping (eqs. (67), (74))

Write `O := C ⧸ ⟨ḡ⟩` for the coset space, `u.out : C` the canonical representative.  For `c : C`,
left translation `u ↦ ↑(c⁻¹ · u.out)` is a bijection `piEquiv c : O ≃ O` (the paper's `π_c`), and
`ε_c(u) ∈ 𝔽₂` records whether `c⁻¹·u.out` is already the canonical rep of its coset (`ε = 0`) or
the twisted one `π_c(u)·ḡ` (`ε = 1`).  With `ḡ² = 1` the coset is `{π, πḡ}`, so
`c⁻¹·u.out ∈ {π_c(u), π_c(u)·ḡ}` — the decomposition (67).

No axioms; `Ax = ∅`.
-/

namespace GQ2

open scoped Classical
open QuadraticFp2

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)] (gbar : G ⧸ N)

/-- The `⟨ḡ⟩`-coset space of `C = G/N` — the index set of the involution orbit sum. -/
local notation "O" => (G ⧸ N) ⧸ Subgroup.zpowers gbar

-- The coset space is finite only where finsums are summed; the algebraic lemmas below
-- do not need it, so omit it and re-add `[Finite (G ⧸ N)]` on the three finsum users.
omit [Finite (G ⧸ N)]

/-- Left translation commutes with the `⟨ḡ⟩`-coset projection past a chosen representative:
`↑(a · (↑w).out) = ↑(a · w)` in `O`. -/
theorem mk_mul_out_eq (a w : G ⧸ N) :
    (((a * (w : O).out : G ⧸ N)) : O) = ((a * w : G ⧸ N) : O) := by
  rw [QuotientGroup.eq, show (a * (w : O).out)⁻¹ * (a * w) = ((w : O).out)⁻¹ * w from by group,
    ← QuotientGroup.eq]
  exact Quotient.out_eq _

/-- `π_c` (paper (67)): left translation by `c⁻¹` on the `⟨ḡ⟩`-coset space, `u ↦ ↑(c⁻¹·u.out)`.
A bijection with inverse `u ↦ ↑(c·u.out)`. -/
noncomputable def piEquiv (c : G ⧸ N) : O ≃ O where
  toFun u := (c⁻¹ * u.out : G ⧸ N)
  invFun u := (c * u.out : G ⧸ N)
  left_inv u := by
    show (((c * ((c⁻¹ * u.out : G ⧸ N) : O).out : G ⧸ N)) : O) = u
    rw [mk_mul_out_eq, show c * (c⁻¹ * u.out) = u.out from by group]
    exact Quotient.out_eq _
  right_inv u := by
    show (((c⁻¹ * ((c * u.out : G ⧸ N) : O).out : G ⧸ N)) : O) = u
    rw [mk_mul_out_eq, show c⁻¹ * (c * u.out) = u.out from by group]
    exact Quotient.out_eq _

/-- With `ḡ² = 1` the cyclic subgroup `⟨ḡ⟩` is `{1, ḡ}`. -/
theorem zpowers_sq_dichotomy (hg2 : gbar * gbar = 1) {t : G ⧸ N}
    (ht : t ∈ Subgroup.zpowers gbar) : t = 1 ∨ t = gbar := by
  obtain ⟨n, rfl⟩ := ht
  show gbar ^ n = 1 ∨ gbar ^ n = gbar
  have hsq : gbar ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one]; exact hg2
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left; rw [← two_mul, zpow_mul, hsq, one_zpow]
  · right; rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- **Eq. (67)**: with `ḡ² = 1`, `c⁻¹·u.out` is either the canonical representative `π_c(u)` of its
`⟨ḡ⟩`-coset (`ε = 0`) or the twist `π_c(u)·ḡ` (`ε = 1`). -/
theorem coset_out_decomp (hg2 : gbar * gbar = 1) (c : G ⧸ N) (u : O) :
    c⁻¹ * u.out = ((c⁻¹ * u.out : G ⧸ N) : O).out
      ∨ c⁻¹ * u.out = ((c⁻¹ * u.out : G ⧸ N) : O).out * gbar := by
  have hmem : (((c⁻¹ * u.out : G ⧸ N) : O).out)⁻¹ * (c⁻¹ * u.out) ∈ Subgroup.zpowers gbar := by
    rw [← QuotientGroup.eq]; exact Quotient.out_eq _
  rcases zpowers_sq_dichotomy N gbar hg2 hmem with h | h
  · left; exact (inv_mul_eq_one.mp h).symm
  · right; exact inv_mul_eq_iff_eq_mul.mp h

/-- Unfolding lemma for `invOrbitDatum`'s factor set (definitional). -/
theorem invOrbitDatum_f_apply (x y : RegRep N) :
    (invOrbitDatum N gbar).f x y = ∑ᶠ u : O, x u.out * y (u.out * gbar) := rfl

/-- Unfolding lemma for `invOrbitDatum`'s corrections (definitional). -/
theorem invOrbitDatum_m_apply (c : G ⧸ N) (x : RegRep N) :
    (invOrbitDatum N gbar).m c x = ∑ᶠ u : O,
      (if c⁻¹ * u.out = ((c⁻¹ * u.out : G ⧸ N) : O).out then (0 : ZMod 2) else 1) *
        (x ((c⁻¹ * u.out : G ⧸ N) : O).out * x (((c⁻¹ * u.out : G ⧸ N) : O).out * gbar)) := rfl

/-- The canonical `⟨ḡ⟩`-coset representative of `c⁻¹·u.out` — the paper's `π_c(u)` (an element). -/
noncomputable def piElt (c : G ⧸ N) (u : O) : G ⧸ N := ((c⁻¹ * u.out : G ⧸ N) : O).out

/-- The orientation bit `ε_c(u)` (paper (67)): `0` if `c⁻¹·u.out` is already canonical, else `1`. -/
noncomputable def epsFun (c : G ⧸ N) (u : O) : ZMod 2 :=
  if c⁻¹ * u.out = piElt N gbar c u then 0 else 1

theorem piElt_eq_out (c : G ⧸ N) (u : O) : piElt N gbar c u = (piEquiv N gbar c u).out := rfl

/-- `m` in `piElt`/`epsFun` form (definitional). -/
theorem invOrbitDatum_m_apply' (c : G ⧸ N) (x : RegRep N) :
    (invOrbitDatum N gbar).m c x
      = ∑ᶠ u : O, epsFun N gbar c u * (x (piElt N gbar c u) * x (piElt N gbar c u * gbar)) := rfl

/-- (67) restated in `piElt` form. -/
theorem coset_out_decomp' (hg2 : gbar * gbar = 1) (c : G ⧸ N) (u : O) :
    c⁻¹ * u.out = piElt N gbar c u ∨ c⁻¹ * u.out = piElt N gbar c u * gbar :=
  coset_out_decomp N gbar hg2 c u

/-- **Shift-invariance** of the square term (`ḡ²=1`): `x_a x_{aḡ}` depends only on the coset of `a`,
so it equals `x_{π} x_{πḡ}` for the canonical rep `π = (↑a).out`. -/
theorem square_term_out (hg2 : gbar * gbar = 1) (x : RegRep N) (a : G ⧸ N) :
    x a * x (a * gbar) = x ((a : O).out) * x ((a : O).out * gbar) := by
  have hmem : ((a : O).out)⁻¹ * a ∈ Subgroup.zpowers gbar := by
    rw [← QuotientGroup.eq]; exact Quotient.out_eq _
  set p := (a : O).out with hp
  rcases zpowers_sq_dichotomy N gbar hg2 hmem with h | h
  · rw [inv_mul_eq_one.mp h]
  · rw [inv_mul_eq_iff_eq_mul.mp h, mul_assoc p gbar gbar, hg2, mul_one]
    exact mul_comm (x (p * gbar)) (x p)

/-- **Paper (74)**, coset half: `π_{cd} = π_d ∘ π_c` as maps on the coset space. -/
theorem piEquiv_mul (c d : G ⧸ N) :
    piEquiv N gbar (c * d) = (piEquiv N gbar c).trans (piEquiv N gbar d) := by
  ext u
  show (((c * d)⁻¹ * u.out : G ⧸ N) : O)
    = ((d⁻¹ * (((c⁻¹ * u.out : G ⧸ N) : O)).out : G ⧸ N) : O)
  rw [mk_mul_out_eq, mul_inv_rev, mul_assoc]

/-- **Paper (74)**, representative form: `π_{cd}(u) = π_d(π_c(u))`. -/
theorem piElt_mul (c d : G ⧸ N) (u : O) :
    piElt N gbar (c * d) u = piElt N gbar d (piEquiv N gbar c u) := by
  simp only [piElt_eq_out, piEquiv_mul, Equiv.trans_apply]

/-- **Paper (74)**, orientation half: `ε_{cd}(u) = ε_c(u) + ε_d(π_c(u))` in `𝔽₂` (the g-exponents
add mod 2).  The 4-case bash on `(ε_c, ε_d)`; the mixed cases use `ḡ²=1` and `mul_right_eq_self`. -/
theorem epsFun_mul (hg2 : gbar * gbar = 1) (c d : G ⧸ N) (u : O) :
    epsFun N gbar (c * d) u = epsFun N gbar c u + epsFun N gbar d (piEquiv N gbar c u) := by
  have hPcd : (c * d)⁻¹ * u.out = d⁻¹ * (c⁻¹ * u.out) := by rw [mul_inv_rev, mul_assoc]
  have hpout : (piEquiv N gbar c u).out = piElt N gbar c u := (piElt_eq_out N gbar c u).symm
  have hpcd : piElt N gbar d (piEquiv N gbar c u) = piElt N gbar (c * d) u :=
    (piElt_mul N gbar c d u).symm
  simp only [epsFun, hpout, hpcd]
  by_cases hc : c⁻¹ * u.out = piElt N gbar c u
  · by_cases hd : d⁻¹ * piElt N gbar c u = piElt N gbar (c * d) u
    · rw [if_pos hc, if_pos hd, if_pos (by rwa [hPcd, hc])]; decide
    · rw [if_pos hc, if_neg hd, if_neg (by rwa [hPcd, hc])]; decide
  · have hc2 : c⁻¹ * u.out = piElt N gbar c u * gbar :=
      (coset_out_decomp' N gbar hg2 c u).resolve_left hc
    by_cases hd : d⁻¹ * piElt N gbar c u = piElt N gbar (c * d) u
    · -- ε_c=1, ε_d=0: `Pcd = π_{cd}·ḡ ≠ π_{cd}` (else `ḡ=1` ⟹ `c⁻¹u.out = π_c`, contra `hc`)
      rw [if_neg hc, if_pos hd,
        if_neg (show (c * d)⁻¹ * u.out ≠ piElt N gbar (c * d) u by
          rw [hPcd, hc2, ← mul_assoc d⁻¹ (piElt N gbar c u) gbar, hd]
          exact fun heq => hc (hc2.trans (mul_eq_left.mpr (mul_eq_left.mp heq))))]
      decide
    · -- ε_c=1, ε_d=1: `Pcd = π_{cd}·ḡ² = π_{cd}`
      have hd2 : d⁻¹ * piElt N gbar c u = piElt N gbar (c * d) u * gbar := by
        have h := (coset_out_decomp' N gbar hg2 d (piEquiv N gbar c u)).resolve_left
          (by rwa [hpout, hpcd])
        rwa [hpout, hpcd] at h
      rw [if_neg hc, if_neg hd,
        if_pos (show (c * d)⁻¹ * u.out = piElt N gbar (c * d) u by
          rw [hPcd, hc2, ← mul_assoc d⁻¹ (piElt N gbar c u) gbar, hd2,
            mul_assoc (piElt N gbar (c * d) u) gbar gbar, hg2, mul_one])]
      decide

/-- Left-additivity of the involution factor set. -/
theorem invOrbitDatum_f_add_left [Finite (G ⧸ N)] (x x' y : RegRep N) :
    (invOrbitDatum N gbar).f (x + x') y
      = (invOrbitDatum N gbar).f x y + (invOrbitDatum N gbar).f x' y := by
  simp only [invOrbitDatum_f_apply]
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun u => add_mul _ _ _

/-- Right-additivity of the involution factor set. -/
theorem invOrbitDatum_f_add_right [Finite (G ⧸ N)] (x y y' : RegRep N) :
    (invOrbitDatum N gbar).f x (y + y')
      = (invOrbitDatum N gbar).f x y + (invOrbitDatum N gbar).f x y' := by
  simp only [invOrbitDatum_f_apply]
  rw [← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finsum_congr fun u => mul_add _ _ _

/-- **The involution-orbit datum is an equivariant factor set** (Lemma 6.2, eqs. (71)–(73)) for
its square map `q_g x = Σ_u x_{u} x_{uḡ}`.  Needs the involution hypothesis `ḡ² = 1`. -/
theorem isEquivariantFactorSet_invOrbitDatum [Finite (G ⧸ N)] (hg2 : gbar * gbar = 1) :
    IsEquivariantFactorSet
      (fun x : RegRep N => ∑ᶠ u : O, x u.out * x (u.out * gbar))
      (invOrbitDatum N gbar) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `f_cocycle`: biadditivity ⟹ 2-cocycle
    intro v w x
    rw [invOrbitDatum_f_add_left, invOrbitDatum_f_add_right]; ring
  · -- `f_diag`: `f v v = q v` definitionally
    intro v; rfl
  · -- `f_polar`: from biadditivity + diagonal (char 2)
    intro v w
    have hexp : (invOrbitDatum N gbar).f (v + w) (v + w)
        = (invOrbitDatum N gbar).f v v + (invOrbitDatum N gbar).f v w
          + (invOrbitDatum N gbar).f w v + (invOrbitDatum N gbar).f w w := by
      rw [invOrbitDatum_f_add_left, invOrbitDatum_f_add_right, invOrbitDatum_f_add_right]; ring
    show (invOrbitDatum N gbar).f v w + (invOrbitDatum N gbar).f w v
        = polar (fun x : RegRep N => ∑ᶠ u : O, x u.out * x (u.out * gbar)) v w
    simp only [polar]
    rw [← invOrbitDatum_f_apply (x := v + w) (y := v + w),
      ← invOrbitDatum_f_apply (x := v) (y := v), ← invOrbitDatum_f_apply (x := w) (y := w), hexp]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
  · -- `f_zero_left`
    intro v
    rw [invOrbitDatum_f_apply]
    exact (finsum_congr fun u => zero_mul _).trans finsum_zero
  · -- `f_zero_right`
    intro v
    rw [invOrbitDatum_f_apply]
    exact (finsum_congr fun u => mul_zero _).trans finsum_zero
  · -- (71) `m_quad`: `m_c(v+w) + m_c v + m_c w = f(cv, cw) + f(v, w)`.
    intro c v w
    -- reindex `f(v,w)` by the bijection `π_c`
    have hfvw : (invOrbitDatum N gbar).f v w
        = ∑ᶠ u : O, v (piElt N gbar c u) * w (piElt N gbar c u * gbar) := by
      rw [invOrbitDatum_f_apply]
      exact (finsum_comp_equiv (piEquiv N gbar c)
        (f := fun u' : O => v u'.out * w (u'.out * gbar))).symm
    -- LHS: the three `m`-finsums combine, per-`u` bracket is the polarization
    have hLHS : (invOrbitDatum N gbar).m c (v + w) + (invOrbitDatum N gbar).m c v
          + (invOrbitDatum N gbar).m c w
        = ∑ᶠ u : O, epsFun N gbar c u * (v (piElt N gbar c u) * w (piElt N gbar c u * gbar)
            + w (piElt N gbar c u) * v (piElt N gbar c u * gbar)) := by
      rw [invOrbitDatum_m_apply', invOrbitDatum_m_apply', invOrbitDatum_m_apply',
        ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _),
        ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finsum_congr fun u => ?_
      rw [show (v + w) (piElt N gbar c u) = v (piElt N gbar c u) + w (piElt N gbar c u) from rfl,
        show (v + w) (piElt N gbar c u * gbar)
          = v (piElt N gbar c u * gbar) + w (piElt N gbar c u * gbar) from rfl]
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    -- RHS: split `f(cv,cw)` per-`u`, add `f(v,w)`
    have hRHS : (invOrbitDatum N gbar).f (c • v) (c • w) + (invOrbitDatum N gbar).f v w
        = ∑ᶠ u : O, epsFun N gbar c u * (v (piElt N gbar c u) * w (piElt N gbar c u * gbar)
            + w (piElt N gbar c u) * v (piElt N gbar c u * gbar)) := by
      rw [invOrbitDatum_f_apply (x := c • v) (y := c • w), hfvw,
        ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
      refine finsum_congr fun u => ?_
      by_cases hP : c⁻¹ * u.out = piElt N gbar c u
      · have hε : epsFun N gbar c u = 0 := if_pos hP
        rw [hε, zero_mul]
        show v (c⁻¹ * u.out) * w (c⁻¹ * (u.out * gbar))
          + v (piElt N gbar c u) * w (piElt N gbar c u * gbar) = 0
        rw [hP, ← mul_assoc, hP]
        exact CharTwo.add_self_eq_zero _
      · have hε : epsFun N gbar c u = 1 := if_neg hP
        have hd2 : c⁻¹ * u.out = piElt N gbar c u * gbar :=
          (coset_out_decomp' N gbar hg2 c u).resolve_left hP
        rw [hε, one_mul]
        show v (c⁻¹ * u.out) * w (c⁻¹ * (u.out * gbar))
          + v (piElt N gbar c u) * w (piElt N gbar c u * gbar)
          = v (piElt N gbar c u) * w (piElt N gbar c u * gbar)
            + w (piElt N gbar c u) * v (piElt N gbar c u * gbar)
        rw [hd2, ← mul_assoc, hd2, mul_assoc (piElt N gbar c u) gbar gbar, hg2, mul_one]
        ring
    rw [hLHS, hRHS]
  · -- (72) `m_mul`: `m_{cd} v = m_c (d•v) + m_d v`.
    intro c d v
    -- `m_c(d•v)`: `(d•v)_π = v_{d⁻¹π}`, then `square_term_out` folds `d⁻¹·π_c(u)` to `π_{cd}(u)`
    have hmcdv : (invOrbitDatum N gbar).m c (d • v)
        = ∑ᶠ u : O, epsFun N gbar c u
            * (v (piElt N gbar (c * d) u) * v (piElt N gbar (c * d) u * gbar)) := by
      rw [invOrbitDatum_m_apply']
      refine finsum_congr fun u => ?_
      have hout : ((d⁻¹ * piElt N gbar c u : G ⧸ N) : O).out = piElt N gbar (c * d) u :=
        (piElt_mul N gbar c d u).symm
      show epsFun N gbar c u
        * (v (d⁻¹ * piElt N gbar c u) * v (d⁻¹ * (piElt N gbar c u * gbar))) = _
      rw [← mul_assoc d⁻¹ (piElt N gbar c u) gbar,
        square_term_out N gbar hg2 v (d⁻¹ * piElt N gbar c u), hout]
    -- `m_d(v)`: reindex `u ↦ π_c(u)` (bijection), then `π_d(π_c u) = π_{cd}(u)`
    have hmdv : (invOrbitDatum N gbar).m d v
        = ∑ᶠ u : O, epsFun N gbar d (piEquiv N gbar c u)
            * (v (piElt N gbar (c * d) u) * v (piElt N gbar (c * d) u * gbar)) := by
      rw [invOrbitDatum_m_apply',
        ← finsum_comp_equiv (piEquiv N gbar c)
          (f := fun u => epsFun N gbar d u * (v (piElt N gbar d u) * v (piElt N gbar d u * gbar)))]
      exact finsum_congr fun u => by simp only [piElt_mul]
    -- combine via the (74) cocycle `ε_{cd} = ε_c + ε_d∘π_c`
    rw [hmcdv, hmdv, invOrbitDatum_m_apply',
      ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finsum_congr fun u => by rw [← add_mul, ← epsFun_mul N gbar hg2 c d u]
  · -- `m_one`: every `ε_1(u) = 0` because `1·u.out` is already the canonical rep
    intro v
    rw [invOrbitDatum_m_apply]
    have hz : ∀ u : O,
        (if (1 : G ⧸ N)⁻¹ * u.out = (((1 : G ⧸ N)⁻¹ * u.out : G ⧸ N) : O).out
          then (0 : ZMod 2) else 1) *
          (v (((1 : G ⧸ N)⁻¹ * u.out : G ⧸ N) : O).out
            * v ((((1 : G ⧸ N)⁻¹ * u.out : G ⧸ N) : O).out * gbar)) = 0 := by
      intro u
      simp only [inv_one, one_mul]
      rw [if_pos (congrArg Quotient.out (Quotient.out_eq u)).symm, zero_mul]
    rw [finsum_congr hz, finsum_zero]

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (67) = ⟦eq-piepsilon⟧
  * eq. (71) = ⟦eq-halforbitquadratic⟧
  * eq. (73) = ⟦eq-kappahalforbit⟧
  * Lemma 6.2 = ⟦lem-halforbitcocycle⟧
-/
