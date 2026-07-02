import GQ2.Omega2

/-!
# Appendix A/B: computational cross-checks of the `ω₂`-marking

The paper's Appendices A–B are an explicit, finite computational verification that is *independent*
of the proof (Remark 1.3): the auxiliary words and the relator are evaluated in finite groups, with
the profinite idempotent `ω₂ ∈ ℤ̂` replaced by an ordinary integer representative modulo the group's
exponent (App. B: `ω₂ ≡ 40491355905 (mod 85667662080)`).

This file makes that finite calculus rigorous and machine-checkable:

* `powOmega2_eq_one_of_odd`, `powOmega2_eq_self_of_orderOf_two_pow` — how `ω₂` acts elementwise
  (`≡ 0` on the odd part, `≡ 1` on the `2`-part); the App. A word-ledger building blocks.
* `markOmega2` — the App. B *computable* `ω₂`-power `x ↦ x ^ 40491355905`, proved equal to
  `powOmega2` on any group whose element orders divide `85667662080`.
* concrete admissible markings verified by `decide` (see `AppendixB` examples below).
-/

namespace GQ2

variable {G : Type*} [Group G]

/-! ## How `ω₂` acts elementwise (App. A ledger, Lemma 5.1) -/

/-- **`ω₂ ≡ 0` on the odd part.**  If `x` has odd order, then `x ^ ω₂ = 1`. -/
theorem powOmega2_eq_one_of_odd {x : G} (h : Odd (orderOf x)) : powOmega2 x = 1 := by
  have hfac : (orderOf x).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by rw [← even_iff_two_dvd]; exact (Nat.not_even_iff_odd).2 h)
  rw [powOmega2, ← orderOf_dvd_iff_pow_eq_one]
  have := oddPart_dvd_omega2Exp (orderOf x)
  rwa [hfac, pow_zero, Nat.div_one] at this

/-- **`ω₂ ≡ 1` on the `2`-part.**  If `x` has order a power of `2`, then `x ^ ω₂ = x`. -/
theorem powOmega2_eq_self_of_orderOf_two_pow {x : G} {k : ℕ} (h : orderOf x = 2 ^ k) :
    powOmega2 x = x := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · -- order 1 ⇒ x = 1
    subst hk
    rw [pow_zero, orderOf_eq_one_iff] at h
    rw [h]; simp [powOmega2]
  · have hn : orderOf x ≠ 0 := by rw [h]; positivity
    have hfac : (orderOf x).factorization 2 = k := by
      rw [h, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
    have hmod : omega2Exp (orderOf x) ≡ 1 [MOD 2 ^ k] := by
      have h1 := omega2Exp_modEq_one hn (by rw [hfac]; omega)
      rwa [hfac] at h1
    have hmod' : omega2Exp (orderOf x) ≡ 1 [MOD orderOf x] := h.symm ▸ hmod
    rw [powOmega2]
    calc x ^ omega2Exp (orderOf x) = x ^ 1 := pow_eq_pow_iff_modEq.mpr hmod'
      _ = x := pow_one x

/-! ## The Appendix-B computable `ω₂`-power -/

/-- **App. B representative of `ω₂`.**  The computable `ω₂`-power on finite groups: `x ↦ x^ω₂` with
`ω₂` replaced by its Appendix-B integer serialization `40491355905` (valid whenever the exponent
divides `M = 85667662080`).  Unlike `powOmega2` (which is noncomputable via `orderOf`), this is a
plain group power and so evaluates by `decide`/`#eval`. -/
def markOmega2 (x : G) : G := x ^ 40491355905

/-- `markOmega2` agrees with the genuine `powOmega2` on any element whose order divides the
Appendix-B modulus `M = 85667662080` (in particular on any group of exponent dividing `M`).  This is
`powOmega2_pow_eq` together with the verified `omega2Exp 85667662080 = 40491355905`. -/
theorem markOmega2_eq_powOmega2 {x : G} (h : orderOf x ∣ 85667662080) :
    markOmega2 x = powOmega2 x := by
  rw [markOmega2, ← omega2Exp_appendixB_value]
  exact powOmega2_pow_eq x h (by norm_num)

/-! ## Concrete verified admissible markings -/

namespace Marking

variable {G : Type*} [Group G] (t : Marking G)

/-- If both wild generators are trivial and `τ` has trivial `ω₂`-power (e.g. `τ` of odd order, by
`powOmega2_eq_one_of_odd`), then every auxiliary word collapses to `1` and the wild relation holds
automatically.  This is the tame-frame case of the relator evaluation. -/
theorem wildRel_of_trivial_wild (hx0 : t.x₀ = 1) (hx1 : t.x₁ = 1) (hτ : powOmega2 t.τ = 1) :
    t.WildRel := by
  have hu1 : t.u1 = 1 := by simp only [u1, u, hx1, one_mul, hτ]
  have hu0 : t.u0 = 1 := by simp only [u0, u, hx0, one_mul, hτ]
  have hd0 : t.d0 = 1 := by simp only [d0, hu0, hx0, inv_one, mul_one]
  have hz0 : t.z0 = 1 := by simp only [z0, hx0]; simp [conjP]
  have hc0 : t.c0 = 1 := by simp only [c0, hd0, hz0]; simp [commP]
  have hdg : t.dg = 1 := by simp only [dg, hd0]; simp [conjP]
  have hhc : t.hc = 1 := by simp only [hc, hdg, hd0]; simp [commP]
  have hh0 : t.h0 = 1 := by
    simp only [h0, hx0, hdg, hd0, hhc, one_pow, mul_one]; simp [conjP]
  simp only [WildRel, hh0, hu1, hx1, hc0, inv_one, mul_one]
  simp [conjP]

/-- **A concrete admissible marking** realizing the tame frame `S₃`: the quadruple
`(σ, τ, x₀, x₁) = (sr 0, r 1, 1, 1)` in the dihedral group `S₃ = DihedralGroup 3`.  Here `S₃` is a
genuine tame quotient of `G_{ℚ₂}` (the wild part `O₂(S₃)` is trivial), and this is exactly the
kind of finite check the paper's Appendix B performs. -/
def markS3 : Marking (DihedralGroup 3) := ⟨DihedralGroup.sr 0, DihedralGroup.r 1, 1, 1⟩

/-- The tame relation `τ^σ = τ²` holds in `S₃`, by direct finite computation. -/
theorem markS3_tameRel : markS3.TameRel := by unfold Marking.TameRel conjP; decide

/-- The wild relation `h₀ u₁⁻¹ x₁^σ c₀ = 1` holds in `S₃`: the wild generators are trivial and
`τ = r 1` has odd order `3`, so every auxiliary word collapses to `1`. -/
theorem markS3_wildRel : markS3.WildRel := by
  refine markS3.wildRel_of_trivial_wild rfl rfl (powOmega2_eq_one_of_odd ?_)
  show Odd (orderOf (DihedralGroup.r 1 : DihedralGroup 3))
  rw [DihedralGroup.orderOf_r_one]; decide

end Marking

/-- `markOmega2` on `S₃` reproduces the `ω₂`-action elementwise: the odd-order rotation `r 1` is
killed (`ω₂ ≡ 0` on the odd part).  (The `40491355905`-th power is far too large to evaluate
directly; it is discharged through `powOmega2` via `markOmega2_eq_powOmega2`.) -/
theorem markOmega2_r1 : markOmega2 (DihedralGroup.r 1 : DihedralGroup 3) = 1 := by
  rw [markOmega2_eq_powOmega2 (by rw [DihedralGroup.orderOf_r_one]; decide)]
  exact powOmega2_eq_one_of_odd (by rw [DihedralGroup.orderOf_r_one]; decide)

/-- The order-2 reflection `sr 0` is fixed by `ω₂` (`ω₂ ≡ 1` on the `2`-part). -/
theorem markOmega2_sr0 :
    markOmega2 (DihedralGroup.sr 0 : DihedralGroup 3) = DihedralGroup.sr 0 := by
  rw [markOmega2_eq_powOmega2 (by rw [DihedralGroup.orderOf_sr]; decide)]
  exact powOmega2_eq_self_of_orderOf_two_pow (k := 1) (by rw [DihedralGroup.orderOf_sr, pow_one])

end GQ2


