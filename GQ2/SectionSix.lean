import GQ2.BoundaryFrame
import GQ2.EvensKahn
import GQ2.TateDuality
import GQ2.Omega2
import GQ2.QuadraticFp2
import GQ2.GaussCount
import GQ2.GaussSigns
import GQ2.GaussSignsRamified
import GQ2.HilbertLedger
import GQ2.Prop32
import GQ2.Corestriction
import GQ2.OrbitData
import GQ2.ShapiroLedger
import GQ2.Transgression

/-!
# §6: quadratic determinant obstructions — statements  (ticket P-14)

Statement-first extraction of the paper's §6 (pages 21–37), per the P-14 scope: the **Gauss-sign
pair** 6.8/6.9, the **`D₈`/Evens-norm normalization** 6.13, the **orbit–stabilizer Shapiro
ledger** 6.15, the **Hilbert ledger** 6.16 → 6.17 → **6.18** (the dyadic base determinant
theorem, the section's headline), and the **transgression/shear pair** 6.21/6.22.  Every
`theorem … := by sorry` carries its paper display number; proofs are ticket P-15
(Ax: B5, B6, B7′, B9).  The definitional layer here (factor sets, graph pullbacks, orbit
cocycles, the local functional `ι_F`) is `sorry`-free; classes of not-yet-proved cocycles are
formed with the junk-total `H2ofFun`/`H1ofFun` (`GQ2/Corestriction.lean`).

Design rationale, statement-by-statement display map, and **flagged deviations** (democratic
Arf, canonical transversals, 6.5/6.19 deferred to the P-12/P-16 seam, 6.13's (100) folded into
6.15's (105), 6.21 in consequence form, (83) as the definition shape of `Q⁰_A`):
`docs/section67-extraction.md`.

## The §6 objects, as encoded here

* **Factor-set data** (Lemma 6.1, eqs. (59)–(62)): `FactorSet C V` carries the normalized factor
  set `f` and the equivariant-lift corrections `m_c`; `IsEquivariantFactorSet q dat` is the Prop
  bundle (59)/(60) + square map + polar compatibility.  `kappa0` is the base central cocycle
  (61) on `V ⋊ C`; `graphPullback dat ρ b` is its pullback (62) along a lower map `ρ` and a
  1-cochain `b` — the only form the statements consume.
* **The local functional `ι_F = inv_{ℚ₂}`** (§6 opening): `iotaF D : H²(G_ℚ₂, 𝔽₂) →+ 𝔽₂`
  through the `𝔽₂ ≅ μ₂` coefficient bridge (`muTwoOfF2`) and B6's invariant `D.inv`
  (`GQ2/TateDuality.lean`).  `Q0loc` (eq. (92)) is the base quadratic connecting map, on
  `H¹`-classes via the canonical representative (`Quotient.out`; well-definedness = Lemma 6.4,
  a P-15 obligation).
* **Deep units** (§6.3, eqs. (93)/(94)): `IsDeepUnit N A` says `A = 1 + 2b` with `‖b‖ < 1`,
  `A, b` fixed by `N` — i.e. `A ∈ U_{e+1}(K)` for `K` the fixed field of `N`, phrased through
  the spectral norm on `ℚ̄₂` (Mathlib's `NormedField (AlgebraicClosure ℚ_[p])`), with **no
  ramification-index bookkeeping**: `v_K(A−1) ≥ e+1 ⟺ ‖A−1‖ < ‖2‖`.
* **Ramified/unramified** (for 6.9/6.18): the module's lower map factors through `GQ2.Ttame`
  (`GQ2/BoundaryFrame.lean`), and the dichotomy is whether the inertia generator `tameTau` acts
  trivially on `V`.  `U = S^{ω₂}` is `powOmega2` (`GQ2/Omega2.lean`) of the Frobenius image.

Axioms: **none consumed here** (statement layer); the census stays at 10.
-/

namespace GQ2

open ContCoh QuadraticFp2 Corestriction

open scoped Classical

noncomputable section

/-! ## Instance transports: the trivial `G_ℚ₂`-action on `𝔽₂`

`GQ2/Kummer.lean` registers the trivial action for `GaloisGroup ℚ₂ = ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂`; we
transport it to the `AbsGalQ2`-phrasing (definitionally the same group), following the
`GQ2/MuN.lean` precedent. -/

instance : DistribMulAction AbsGalQ2 (ZMod 2) :=
  inferInstanceAs (DistribMulAction (Kummer.GaloisGroup ℚ_[2]) (ZMod 2))

instance : ContinuousSMul AbsGalQ2 (ZMod 2) :=
  inferInstanceAs (ContinuousSMul (Kummer.GaloisGroup ℚ_[2]) (ZMod 2))

/-- The `G_ℚ₂`-action on `𝔽₂` is trivial (definitionally). -/
lemma absGal_smul_zmodTwo (g : AbsGalQ2) (m : ZMod 2) : g • m = m := rfl

namespace SectionSix

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The local functional `ι_F = inv_{ℚ₂}`  (§6 opening display) -/

/-- `−1` as an element of `μ₂ ⊂ ℚ̄₂ˣ` (additively written). -/
def negOneMuTwo : MuN 2 :=
  Additive.ofMul (⟨-1, by rw [mem_rootsOfUnity]; exact neg_one_sq⟩ : rootsOfUnity 2 ℚ̄₂)

/-- The coefficient bridge `𝔽₂ →+ μ₂`, `1 ↦ −1`. -/
def muTwoOfF2 : ZMod 2 →+ MuN 2 :=
  ZMod.lift 2 ⟨zmultiplesHom (MuN 2) negOneMuTwo, by
    show ((2 : ℕ) : ℤ) • negOneMuTwo = 0
    rw [natCast_zsmul]
    exact nsmul_muN_eq_zero 2 negOneMuTwo⟩

/-- Galois fixes `−1 ∈ μ₂` (it lies in the base field). -/
lemma smul_negOneMuTwo (g : AbsGalQ2) : g • negOneMuTwo = negOneMuTwo := by
  apply Additive.toMul.injective
  apply Subtype.ext
  apply Units.ext
  have hval := val_smul_units (K := ℚ_[2]) (L := ℚ̄₂)
    (show ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂ from g) (-1 : ℚ̄₂ˣ)
  refine hval.trans ?_
  rw [Units.val_neg, Units.val_one]
  show (show ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂ from g) • (-1 : ℚ̄₂) = -1
  rw [AlgEquiv.smul_def, map_neg, map_one]

/-- The bridge is `G_ℚ₂`-equivariant (both actions relevant: trivial on `𝔽₂`, Galois on `μ₂`). -/
lemma muTwoOfF2_equivariant (g : AbsGalQ2) (n : ZMod 2) :
    muTwoOfF2 (g • n) = g • muTwoOfF2 n := by
  rw [absGal_smul_zmodTwo]
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcase n with rfl | rfl
  · rw [map_zero, smul_zero]
  · have h1 : muTwoOfF2 1 = negOneMuTwo := by
      show (1 : ℤ) • negOneMuTwo = negOneMuTwo
      rw [one_zsmul]
    rw [h1, smul_negOneMuTwo]

/-- **The local source functional `ι_F = inv_{ℚ₂} : H²(G_ℚ₂, 𝔽₂) → 𝔽₂`** (§6 opening display),
through the `𝔽₂ ≅ μ₂` bridge and B6's invariant map (`D.inv`, `GQ2/TateDuality.lean`).
Parametrized by a duality bundle `D : TateDuality 2`, so the statement layer stays axiom-free. -/
def iotaF (D : TateDuality 2) : H2 AbsGalQ2 (ZMod 2) →+ ZMod 2 :=
  D.inv.toAddMonoidHom.comp
    (mapCoeff2 muTwoOfF2 continuous_of_discreteTopology muTwoOfF2_equivariant)

/-! ## Factor-set data  (Lemma 6.1, eqs. (59)–(62)) — moved to `GQ2/OrbitData.lean`

`FactorSet`, `IsEquivariantFactorSet`, `kappa0`, `graphPullback`, `FactorSet.comap` now live in
`GQ2/OrbitData.lean` (top-level `namespace GQ2`), reachable here unqualified.  See
`docs/orbit-data-refactor.md`. -/

/-! ## `Q⁰_loc`: the base quadratic connecting map  (§6.3, eq. (92)) -/

section Q0loc

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **`Q⁰_loc`** (eq. (92)): `Q⁰_loc([b]) = inv_{ℚ₂}((b, ρ)^* κ⁰_q)`, on `H¹(G_ℚ₂, V)` via the
canonical cocycle representative.  Independence of the representative (and of the datum, given
`IsEquivariantFactorSet`) is the Lemma 6.4 content — a P-15 obligation, not baked into the
definition.  Junk value `0` when the pullback is not a cocycle (`H2ofFun`). -/
def Q0loc (D : TateDuality 2) (dat : FactorSet C V) (ρ : ContinuousMonoidHom AbsGalQ2 C) :
    H1 AbsGalQ2 V → ZMod 2 :=
  fun x ↦ iotaF D (H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1))

/-- **Well-formedness of the graph pullback** (Lemma 6.1's cocycle assertion, specialized to the
graph (62)): for an equivariant factor-set datum and a continuous 1-cocycle `b` (with the
`G_ℚ₂`-action on `V` acting through `ρ`), the pullback is a continuous 2-cocycle.
Paper: Lemma 6.1, display (62).  [P-14 statement; proof P-15.] -/
theorem graphPullback_mem_Z2 {q : V → ZMod 2} (dat : FactorSet C V)
    (hdat : IsEquivariantFactorSet q dat) (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v) (b : Z1 AbsGalQ2 V) :
    graphPullback dat ρ b.1 ∈ Z2 AbsGalQ2 (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine mem_Z2_iff.mpr ⟨?_, fun g h k ↦ ?_⟩
  · -- continuity: factor through the finite discrete triple `C × V × V`
    have hF : Continuous fun p : AbsGalQ2 × AbsGalQ2 ↦
        ((ρ p.1, b.1 p.1, b.1 p.2) : C × V × V) :=
      (ρ.continuous_toFun.comp continuous_fst).prodMk
        ((hbc.comp continuous_fst).prodMk (hbc.comp continuous_snd))
    exact (continuous_of_discreteTopology
      (f := fun t : C × V × V ↦ dat.f t.2.1 (t.1 • t.2.2) + dat.m t.1 t.2.2)).comp hF
  · -- the cocycle identity: (59) + (60) + the factor-set identity, in char 2
    rw [absGal_smul_zmodTwo]
    show dat.f (b.1 h) (ρ h • b.1 k) + dat.m (ρ h) (b.1 k)
        + (dat.f (b.1 g) (ρ g • b.1 (h * k)) + dat.m (ρ g) (b.1 (h * k)))
        = dat.f (b.1 (g * h)) (ρ (g * h) • b.1 k) + dat.m (ρ (g * h)) (b.1 k)
        + (dat.f (b.1 g) (ρ g • b.1 h) + dat.m (ρ g) (b.1 h))
    have hbk : b.1 (h * k) = b.1 h + ρ h • b.1 k := by rw [hb h k, hρ]
    have hbg : b.1 (g * h) = b.1 g + ρ g • b.1 h := by rw [hb g h, hρ]
    have hρm : ρ (g * h) = ρ g * ρ h := map_mul _ _ _
    rw [hbk, hbg, hρm, smul_add, ← mul_smul]
    have h59 := hdat.m_quad (ρ g) (b.1 h) (ρ h • b.1 k)
    have h60 := hdat.m_mul (ρ g) (ρ h) (b.1 k)
    have hco := hdat.f_cocycle (b.1 g) (ρ g • b.1 h) ((ρ g * ρ h) • b.1 k)
    rw [← mul_smul] at h59
    linear_combination h59 - h60 - hco
      + CharTwo.add_self_eq_zero (dat.f (b.1 h) (ρ h • b.1 k))
      - CharTwo.add_self_eq_zero (dat.m (ρ g) (b.1 h))
      - CharTwo.add_self_eq_zero (dat.m (ρ g) (ρ h • b.1 k))

end Q0loc

/-! ## The Gauss-sign pair: Wall doubling and the candidate base counts
(§6.2: Lemma 6.6, Lemma 6.8, Proposition 6.9)

The candidate base form is taken in its evaluated shape (83): `Q⁰_A = q` when the inertia image
is trivial (`T = 1`), and `Q⁰_A = q_U = qDouble q U` with `U = S^{ω₂}` when `V^T = 0` (ramified).
Deriving (83) from the relator ledger is Prop 6.5 = the P-12 seam (deviation note §6.5). -/

section GaussSign

variable {V : Type*} [AddCommGroup V] [Finite V]

/-- The additive endomorphism `1 + U` of `V` (char 2). -/
def onePlusU (U : V ≃+ V) : V →+ V :=
  AddMonoidHom.mk' (fun v ↦ v + U v) (by
    intro v w
    rw [map_add]
    abel)

/-- **Lemma 6.6 (Wall doubling), eq. (86)**: for a nonsingular `q` and an orthogonal operator
`U` of 2-power order, the doubling `q_U(x) = q(x) + B(x, Ux)` is nonsingular and
`Arf(q_U) = Arf(q) + rank(1 + U) (mod 2)`.  The rank enters as the exponent `k` of
`#im(1 + U) = 2^k`.  [P-14 statement; proof P-15.] -/
theorem lemma_6_6 (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (hns : Nonsingular q) (U : V ≃+ V) (hUq : ∀ v, q (U v) = q v)
    (hU2 : ∃ n : ℕ, (⇑U)^[2 ^ n] = id) :
    Nonsingular (qDouble q ⇑U) ∧
      ∃ k : ℕ, Nat.card (onePlusU U).range = 2 ^ k ∧
        arf (qDouble q ⇑U) = arf q + (k : ZMod 2) := by
  classical
  letI := Fintype.ofFinite V
  -- nonsingularity of `q_U` and the `2`-power rank are proved in `GQ2/GaussCount.lean` (P-15a).
  refine ⟨qDouble_nonsingular q U hq h2 hns hUq hU2, ?_⟩
  obtain ⟨k, hk⟩ := exists_card_range_eq_two_pow h2 (onePlusU U)
  refine ⟨k, hk, arf_qDouble_of_gaussSum_sign q U (gaussSum_ne_zero q hq hns) ?_⟩
  -- **Wall's sign relation** `g(q_U) = (−1)ᵏ g(q)`: proved in `GQ2/GaussCount.lean` (P-15a) —
  -- grouping the double Gauss sum over the fibers of `1 + U` reduces it to the abstract Wall
  -- count of the Wall form `ω(Nx, u) = B(x, u)` on `im (1 + U)`, whose monodromy `U⁻¹` has
  -- 2-power order.
  exact gaussSum_qDouble q U hq h2 hns hUq hU2 (onePlusU U) (fun _ => rfl) hk

variable {Hf : Type} [Group Hf] [TopologicalSpace Hf] [DiscreteTopology Hf] [Finite Hf]
variable [DistribMulAction Hf V]

/-- **Lemma 6.8 (ramified Hermitian model and Frobenius fixed space), eqs. (87)/(88)**:
for a faithful simple ramified tame module `V` (tame image `Hf` marked by
`c : T_tame ↠ Hf`; inertia `T = c(τ) ≠ 1`; `V|_⟨T⟩ ≅ W^{⊕s}` isotypic with
`#W = 2^f`, `f = 2^a·r`, `r` odd, `a ≥ 1`) and an `Hf`-invariant nonsingular `q`:

* (87) `Arf(q) ≡ s (mod 2)`;
* (88) `#V^U = 2^{rs}` and `rank(1 + U) ≡ s (mod 2)`, for `U = S^{ω₂} = powOmega2 (c σ)`;
* consequently `Arf(q_U) = 0` (the ramified candidate base form of (83)).

[P-14 statement; proof P-15.] -/
theorem lemma_6_8 (c : ContinuousMonoidHom Ttame Hf) (hc : Function.Surjective c)
    (hfaith : ∀ h : Hf, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : Hf), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : c tameTau ≠ 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant Hf q)
    (hV2 : ∀ v : V, v + v = 0)
    (s r a : ℕ) (hr : Odd r) (ha : 1 ≤ a) (hs1 : 1 ≤ s)
    (Wt : Type) [AddCommGroup Wt] [DistribMulAction (Subgroup.zpowers (c tameTau)) Wt]
    (hWt2 : ∀ w : Wt, w + w = 0)
    (hWtsimple : GQ2.FoxH.IsSimpleModTwo (Subgroup.zpowers (c tameTau)) Wt)
    (hWcard : Nat.card Wt = 2 ^ (2 ^ a * r))
    (e : V ≃+ (Fin s → Wt))
    (he : ∀ (t : Subgroup.zpowers (c tameTau)) (v : V) (j : Fin s),
      e ((t : Hf) • v) j = t • e v j)
    (hVU : Nat.card {v : V // powOmega2 (c tameSigma) • v = v} = 2 ^ (r * s))
    (hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))).range = 2 ^ k →
        (k : ZMod 2) = (s : ZMod 2)) :
    arf q = (s : ZMod 2) ∧
      Nat.card {v : V // powOmega2 (c tameSigma) • v = v} = 2 ^ (r * s) ∧
      (∃ k : ℕ,
        Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))).range
            = 2 ^ k ∧
          (k : ZMod 2) = (s : ZMod 2)) ∧
      arf (qDouble q (powOmega2 (c tameSigma) • ·)) = 0 := by
  classical
  letI := Fintype.ofFinite V
  set U := DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)) with hU
  have hUq : ∀ v, q (U v) = q v := fun v => hinv (powOmega2 (c tameSigma)) v
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := by
    refine ⟨(orderOf (c tameSigma)).factorization 2, ?_⟩
    have hp1 : powOmega2 (c tameSigma) ^ 2 ^ (orderOf (c tameSigma)).factorization 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (GQ2.FoxH.orderOf_powOmega2_dvd_two_pow (c tameSigma))
    funext v
    show (powOmega2 (c tameSigma) • ·)^[2 ^ (orderOf (c tameSigma)).factorization 2] v = v
    rw [smul_iterate_apply, hp1, one_smul]
  -- (88b): the rank is a 2-power `2^k` with `k ≡ s`
  obtain ⟨k, hk⟩ := exists_card_range_eq_two_pow hV2 (onePlusU U)
  have h88b : (k : ZMod 2) = (s : ZMod 2) := hrank k hk
  -- (87): `arf q = s` via the `⟨T⟩` route (`GaussSignsRamified`), reusing P-13d's simplicity
  have h87 : arf q = (s : ZMod 2) := by
    letI : DistribMulAction (Subgroup.zpowers (c tameTau)) V :=
      DistribMulAction.compHom V (Subgroup.zpowers (c tameTau)).subtype
    have hTmem : c tameTau ∈ Subgroup.zpowers (c tameTau) := Subgroup.mem_zpowers _
    have hTgen : ∀ g : Subgroup.zpowers (c tameTau),
        g ∈ Subgroup.zpowers (⟨c tameTau, hTmem⟩ : Subgroup.zpowers (c tameTau)) := by
      intro g
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by push_cast; exact hn)⟩
    have hVfaith : ∀ g : Subgroup.zpowers (c tameTau), (∀ v : V, g • v = v) → g = 1 := by
      intro g hg
      exact Subtype.ext (hfaith (g : Hf) (fun v => hg v))
    refine GaussSigns.arf_eq_s_ramified ⟨c tameTau, hTmem⟩ hTgen hVfaith hWtsimple hV2 hWt2
      q hq hns (fun g v => hinv (g : Hf) v) (2 ^ (a - 1) * r) s ?_ hs1 ?_ e (fun g v j => he g v j)
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by positivity) (by rcases hr with ⟨j, hj⟩; omega))
    · rw [hWcard]; congr 1
      have h2a : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
        rw [mul_comm, ← pow_succ]; congr 1; omega
      rw [h2a]; ring
  refine ⟨h87, hVU, ⟨k, hk, h88b⟩, ?_⟩
  exact GaussSigns.arf_qDouble_eq_zero q U hq hV2 hns hUq hU2 (onePlusU U) (fun _ => rfl) hk h87 h88b

/-- **Proposition 6.9 (candidate base determinant zero count), eq. (91), unramified case**:
if inertia acts trivially (`c(τ) = 1`, so `Q⁰_A = q` by (83)) and `#V = 2^{2m}`, then
`#(Q⁰_A)⁻¹(0) = 2^{2m−1} − 2^{m−1}` (negative Gauss sign).  [P-14 statement; proof P-15.] -/
theorem prop_6_9_unramified (c : ContinuousMonoidHom Ttame Hf) (hc : Function.Surjective c)
    (hfaith : ∀ h : Hf, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : Hf), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0) (hunram : c tameTau = 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant Hf q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  -- `V` has exponent `2`: its `2`-torsion is an `Hf`-stable subgroup, nonzero (`2 ∣ #V` by
  -- Cauchy), hence all of `V` by simplicity.
  have h2 : ∀ v : V, v + v = 0 := by
    let W2 : AddSubgroup V :=
      { carrier := {v | v + v = 0}
        add_mem' := fun {x y} hx hy => by
          simp only [Set.mem_setOf_eq] at *
          rw [show x + y + (x + y) = x + x + (y + y) by abel, hx, hy, add_zero]
        zero_mem' := by simp
        neg_mem' := fun {x} hx => by
          simp only [Set.mem_setOf_eq] at *
          rw [show -x + -x = -(x + x) by abel, hx, neg_zero] }
    have hstab : ∀ h : Hf, ∀ w ∈ W2, h • w ∈ W2 := by
      intro h w hw
      show h • w + h • w = 0
      rw [← smul_add, (show w + w = 0 from hw), smul_zero]
    rcases hsimple W2 hstab with hbot | htop
    · exfalso
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hdvd : 2 ∣ Fintype.card V := by
        rw [← Nat.card_eq_fintype_card, hcard]; exact dvd_pow_self 2 (by omega)
      obtain ⟨v, hv⟩ := exists_prime_addOrderOf_dvd_card 2 hdvd
      have hvW2 : v ∈ W2 := by
        show v + v = 0
        have h20 : (2 : ℕ) • v = 0 := by rw [← hv]; exact addOrderOf_nsmul_eq_zero v
        rwa [two_nsmul] at h20
      have hvne : v ≠ 0 := by
        intro h0; rw [h0, addOrderOf_zero] at hv; exact absurd hv (by decide)
      rw [hbot] at hvW2
      exact hvne ((AddSubgroup.mem_bot).mp hvW2)
    · intro v; exact (htop ▸ AddSubgroup.mem_top v : v ∈ W2)
  -- `Hf` is cyclic, generated by `c(σ)`: the images of `σ, τ` generate, and `c(τ) = 1`.
  have hgen : ∀ x : Hf, x ∈ Subgroup.zpowers (c tameSigma) := by
    have hcl : Subgroup.closure {c tameSigma, c tameTau} = ⊤ :=
      SectionThree.gen_ttame_quotient c.toMonoidHom c.continuous_toFun hc
    rw [hunram] at hcl
    have hz : Subgroup.closure ({c tameSigma, 1} : Set Hf) = Subgroup.zpowers (c tameSigma) := by
      rw [Subgroup.zpowers_eq_closure]
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact Subgroup.subset_closure (Set.mem_singleton _)
        · exact one_mem _
      · exact Subgroup.closure_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
    rw [hz] at hcl
    intro x; rw [hcl]; trivial
  exact GaussSigns.prop_6_9_unramified_of_cyclic q hq hns m hm hcard h2 (c tameSigma) hgen
    hfaith hsimple (fun h v => hinv h v)

/-- **Proposition 6.9, eq. (91), ramified case**: if inertia acts nontrivially
(`Q⁰_A = q_U`, `U = S^{ω₂}`, by (83)) and `#V = 2^{2m}`, then
`#(Q⁰_A)⁻¹(0) = 2^{2m−1} + 2^{m−1}` (positive Gauss sign).  [P-14 statement; proof P-15.] -/
theorem prop_6_9_ramified (c : ContinuousMonoidHom Ttame Hf) (hc : Function.Surjective c)
    (hfaith : ∀ h : Hf, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : Hf), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : c tameTau ≠ 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant Hf q)
    (hV2 : ∀ v : V, v + v = 0)
    (s r a : ℕ) (hr : Odd r) (ha : 1 ≤ a) (hs1 : 1 ≤ s)
    (Wt : Type) [AddCommGroup Wt] [DistribMulAction (Subgroup.zpowers (c tameTau)) Wt]
    (hWt2 : ∀ w : Wt, w + w = 0)
    (hWtsimple : GQ2.FoxH.IsSimpleModTwo (Subgroup.zpowers (c tameTau)) Wt)
    (hWcard : Nat.card Wt = 2 ^ (2 ^ a * r))
    (e : V ≃+ (Fin s → Wt))
    (he : ∀ (t : Subgroup.zpowers (c tameTau)) (v : V) (j : Fin s),
      e ((t : Hf) • v) j = t • e v j)
    (hVU : Nat.card {v : V // powOmega2 (c tameSigma) • v = v} = 2 ^ (r * s))
    (hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))).range = 2 ^ k →
        (k : ZMod 2) = (s : ZMod 2))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 (c tameSigma) • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  set U := DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)) with hU
  have hUq : ∀ v, q (U v) = q v := fun v => hinv (powOmega2 (c tameSigma)) v
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := by
    refine ⟨(orderOf (c tameSigma)).factorization 2, ?_⟩
    have hp1 : powOmega2 (c tameSigma) ^ 2 ^ (orderOf (c tameSigma)).factorization 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (GQ2.FoxH.orderOf_powOmega2_dvd_two_pow (c tameSigma))
    funext v
    show (powOmega2 (c tameSigma) • ·)^[2 ^ (orderOf (c tameSigma)).factorization 2] v = v
    rw [smul_iterate_apply, hp1, one_smul]
  -- `arf(q_U) = 0` is Lemma 6.8's fourth conjunct
  have h4 : arf (qDouble q (powOmega2 (c tameSigma) • ·)) = 0 :=
    (lemma_6_8 c hc hfaith hsimple hram q hq hns hinv hV2 s r a hr ha hs1 Wt hWt2 hWtsimple
      hWcard e he hVU hrank).2.2.2
  exact GaussSigns.zeroCount_qDouble_of_arf_zero q U hq hV2 hns hUq hU2 h4 m hm hcard

end GaussSign

/-! ## Lemma 6.13: the universal two-point class and the index-two Evens norm

The repo *defines* the index-two Evens norm by the two-point graph cocycle (98)
(`GQ2/EvensKahn.lean`, per the T-18 design), so the paper's eq. (99) is definitional here.
The remaining 6.13 content is the universal model: the explicit `κ_J` on `E ⋊ J`
(eq. (95)), its `D₈` fibre extension, and eq. (96) `[κ_J] = N^{Ev}(e₁^∨)`.
Eq. (100) is folded into 6.15's (105) (deviation note). -/

section TwoPoint

/-- The swap module `E = 𝔽₂e₁ ⊕ 𝔽₂e_s` with `J = C₂` acting by the coordinate swap
(Lemma 6.13).  The acting group is `Multiplicative (ZMod 2)`. -/
abbrev swapE : Type := ZMod 2 × ZMod 2

/-- The swap action function: `c · v = v` for `c = 1` and `v.swap` for the involution. -/
def swapSmul (c : Multiplicative (ZMod 2)) (v : swapE) : swapE :=
  if c.toAdd = 0 then v else v.swap

instance : SMul (Multiplicative (ZMod 2)) swapE := ⟨swapSmul⟩

@[simp] lemma swapSmul_def (c : Multiplicative (ZMod 2)) (v : swapE) :
    c • v = if c.toAdd = 0 then v else v.swap := rfl

/-- The swap action of `J = Multiplicative (ZMod 2)` on `E`. -/
instance : DistribMulAction (Multiplicative (ZMod 2)) swapE where
  smul := (· • ·)
  one_smul v := by
    rw [swapSmul_def, if_pos (by decide : (1 : Multiplicative (ZMod 2)).toAdd = 0)]
  mul_smul c d v := by
    have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    rw [swapSmul_def, swapSmul_def, swapSmul_def]
    rcases hcase c.toAdd with hc | hc <;> rcases hcase d.toAdd with hd | hd <;>
      simp +decide [toAdd_mul, hc, hd, Prod.swap]
  smul_zero c := by
    rw [swapSmul_def]
    split <;> rfl
  smul_add c v w := by
    rw [swapSmul_def, swapSmul_def, swapSmul_def]
    split <;> rfl

/-- The factor-set datum of the universal two-point class (Lemma 6.13):
`f_J(x, y) = x₁·y_s`, `m_1 = 0`, `m_s(y) = y₁·y_s`. -/
def twoPointDatum : FactorSet (Multiplicative (ZMod 2)) swapE where
  f x y := x.1 * y.2
  m c y := if c.toAdd = 0 then 0 else y.1 * y.2

/-- The central extension of a finite elementary abelian group by `𝔽₂` attached to a raw
factor set `f`: the carrier `A × 𝔽₂` with `(v,z)·(w,t) = (v+w, z+t+f(v,w))`.  A `Group`
instance is available exactly when `f` is a normalized 2-cocycle; for the concrete two-point
`f_J` this is decidable (`twoPointExtGroup`). -/
def CentralExt (A : Type*) (_f : A → A → ZMod 2) : Type _ := A × ZMod 2

/-- The twisted multiplication on `CentralExt`. -/
instance {A : Type*} [AddCommGroup A] (f : A → A → ZMod 2) : Mul (CentralExt A f) :=
  ⟨fun p q ↦ (p.1 + q.1, p.2 + q.2 + f p.1 q.1)⟩

/-- The fibre extension of the two-point class: `E_{f_J} = E × 𝔽₂` with the
`f_J`-twisted multiplication. -/
abbrev twoPointExt : Type := CentralExt swapE (twoPointDatum.f)

instance : DecidableEq twoPointExt :=
  inferInstanceAs (DecidableEq (swapE × ZMod 2))

instance : Fintype twoPointExt := inferInstanceAs (Fintype (swapE × ZMod 2))

/-- The group structure on the two-point fibre extension — the axioms are kernel-checked finite
computations over the 8 elements (`decide`; the board's convention allows it, `native_decide`
does not appear). -/
instance twoPointExtGroup : Group twoPointExt where
  mul := (· * ·)
  one := ((0, 0), 0)
  inv p := (-p.1, p.2 + twoPointDatum.f p.1 (-p.1))
  mul_assoc := by decide
  one_mul := by decide
  mul_one := by decide
  inv_mul_cancel := by decide

/-- The exponent table of the powers of `a = ẽ₁ẽ_s` in `twoPointExt`: `a^i` has fibre
coordinates `(i, i)` and central coordinate `1` exactly for `i ∈ {1, 2}`. -/
private def dihedralToTwoPoint : DihedralGroup 4 → twoPointExt
  | .r i => ((((i.val : ZMod 2)), ((i.val : ZMod 2))), (((i.val + 1) / 2 : ℕ) : ZMod 2))
  | .sr i => ((((i.val : ZMod 2)) + 1, ((i.val : ZMod 2))),
      (((i.val + 1) / 2 : ℕ) : ZMod 2) + ((i.val : ZMod 2)))

/-- The exponent-table map as a monoid hom (kernel-checked). -/
private def dihedralHom : DihedralGroup 4 →* twoPointExt where
  toFun := dihedralToTwoPoint
  map_one' := by decide
  map_mul' := by decide

/-- **Lemma 6.13, the `D₈` claim**: the fibre extension of the universal two-point class is the
dihedral group of order 8 — via the explicit exponent-table map `r ↦ ẽ₁ẽ_s`, `sr 0 ↦ ẽ₁`;
all axioms are kernel-checked finite computations.  Paper: Lemma 6.13.  [P-15.] -/
theorem lemma_6_13_dihedral : Nonempty (twoPointExt ≃* DihedralGroup 4) :=
  ⟨(MulEquiv.ofBijective dihedralHom (by decide)).symm⟩

/-- The semidirect product `V ⋊ C` of an additive `C`-module, on the carrier `V × C` with
`(v,c)·(w,d) = (v + c·w, cd)` — the group all §6 base classes live on (Lemma 6.1, display (66)).
A bespoke synonym (rather than Mathlib's `SemidirectProduct`) avoids `Multiplicative` wrappers on
the fibre; the paper's formulas transcribe verbatim. -/
def SemiProd (C V : Type*) [Group C] [AddCommGroup V] [DistribMulAction C V] : Type _ := V × C

namespace SemiProd

variable {C V : Type*} [Group C] [AddCommGroup V] [DistribMulAction C V]

instance : Mul (SemiProd C V) := ⟨fun p q ↦ (p.1 + p.2 • q.1, p.2 * q.2)⟩
instance : One (SemiProd C V) := ⟨((0 : V), (1 : C))⟩
instance : Inv (SemiProd C V) := ⟨fun p ↦ (-(p.2⁻¹ • p.1), p.2⁻¹)⟩

@[simp] lemma mul_def (a b : SemiProd C V) : a * b = (a.1 + a.2 • b.1, a.2 * b.2) := rfl

@[simp] lemma one_def : (1 : SemiProd C V) = ((0 : V), (1 : C)) := rfl

@[simp] lemma inv_def (a : SemiProd C V) : a⁻¹ = (-(a.2⁻¹ • a.1), a.2⁻¹) := rfl

instance : Group (SemiProd C V) :=
  Group.ofLeftAxioms
    (fun p q r ↦ by simp [mul_def, smul_add, mul_smul, add_assoc, mul_assoc])
    (fun p ↦ by simp [mul_def, one_def])
    (fun p ↦ by simp [mul_def, inv_def, one_def])

/-- The fibre subgroup `V × {1} ≤ V ⋊ C`. -/
def fibre : Subgroup (SemiProd C V) where
  carrier := {p | p.2 = 1}
  one_mem' := rfl
  mul_mem' := by
    intro a b (ha : a.2 = 1) (hb : b.2 = 1)
    show a.2 * b.2 = 1
    rw [ha, hb, one_mul]
  inv_mem' := by
    intro a (ha : a.2 = 1)
    show a.2⁻¹ = 1
    rw [ha, inv_one]

instance : TopologicalSpace (SemiProd C V) := ⊥
instance : DiscreteTopology (SemiProd C V) := ⟨rfl⟩

/-- The trivial action of `V ⋊ C` on `𝔽₂` (every action on `ℤ/2` is trivial). -/
instance : DistribMulAction (SemiProd C V) (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul (SemiProd C V) (ZMod 2) := ⟨continuous_snd⟩

end SemiProd

/-- The first-coordinate functional `e₁^∨` on the fibre subgroup of `E ⋊ J`. -/
def fibreCoord (u : (SemiProd.fibre : Subgroup (SemiProd (Multiplicative (ZMod 2)) swapE))) :
    ZMod 2 :=
  ((u : SemiProd (Multiplicative (ZMod 2)) swapE) : swapE × Multiplicative (ZMod 2)).1.1

/-- **Lemma 6.13, eq. (96)**: on `E ⋊ J`, the class of the explicit two-point cocycle `κ_J`
(eq. (95) — `kappa0 twoPointDatum` as a raw function on the `SemiProd` carrier) **is** the
index-two Evens norm of the first coordinate functional `e₁^∨ ∈ H¹(E, 𝔽₂)`.  Since the repo
*defines* the Evens norm by the two-point graph cocycle (98) (`GQ2/EvensKahn.lean`, so the
paper's (99) is definitional), this statement is the normalization anchoring that definition to
the paper's universal model.  Quantified over the side-condition proofs `evensNormH2` takes.
[P-14 statement; proof P-15.] -/
theorem lemma_6_13_evens
    (sJ : SemiProd (Multiplicative (ZMod 2)) swapE)
    (hsJ : sJ = ((0 : swapE), Multiplicative.ofAdd (1 : ZMod 2)))
    (hUi : (SemiProd.fibre : Subgroup (SemiProd (Multiplicative (ZMod 2)) swapE)).index = 2)
    (hUo : IsOpen ((SemiProd.fibre :
        Subgroup (SemiProd (Multiplicative (ZMod 2)) swapE)) :
        Set (SemiProd (Multiplicative (ZMod 2)) swapE)))
    (hs : sJ ∉ (SemiProd.fibre : Subgroup (SemiProd (Multiplicative (ZMod 2)) swapE)))
    (htriv : ∀ (g : SemiProd (Multiplicative (ZMod 2)) swapE) (m : ZMod 2), g • m = m)
    (hα : ∀ u v, fibreCoord (u * v) = fibreCoord u + fibreCoord v)
    (hαc : Continuous fibreCoord) :
    H2ofFun (SemiProd (Multiplicative (ZMod 2)) swapE)
        (fun p ↦ kappa0 twoPointDatum p.1 p.2)
      = evensNormH2 htriv hUo hUi hs fibreCoord hα hαc := by
  subst hsJ
  have hcase : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  have hmemU : ∀ x : SemiProd (Multiplicative (ZMod 2)) swapE,
      x ∈ SemiProd.fibre ↔ x.2 = 1 := fun _ ↦ Iff.rfl
  -- `b₁((v,c)) = v₁` in both membership branches
  have ha1 : ∀ x : SemiProd (Multiplicative (ZMod 2)) swapE,
      evensAux SemiProd.fibre ((0 : swapE), Multiplicative.ofAdd (1 : ZMod 2))
        fibreCoord x = x.1.1 := by
    intro x
    by_cases hx : x ∈ SemiProd.fibre
    · rw [evensAux_of_mem fibreCoord hx]; rfl
    · rw [evensAux_of_notMem hUi hs fibreCoord hx]
      simp [fibreCoord, SemiProd.mul_def]
  -- `b_s((w,d)) = w₂` in both branches
  have hbs : ∀ x : SemiProd (Multiplicative (ZMod 2)) swapE,
      bS SemiProd.fibre ((0 : swapE), Multiplicative.ofAdd (1 : ZMod 2))
        fibreCoord x = x.1.2 := by
    intro x
    simp only [bS]
    rw [ha1]
    simp +decide [SemiProd.mul_def, SemiProd.inv_def, Prod.swap]
  -- the two raw cocycles coincide on the nose
  have hfun : (fun p : SemiProd (Multiplicative (ZMod 2)) swapE ×
        SemiProd (Multiplicative (ZMod 2)) swapE ↦ kappa0 twoPointDatum p.1 p.2)
      = evensNormFun SemiProd.fibre
          ((0 : swapE), Multiplicative.ofAdd (1 : ZMod 2)) fibreCoord := by
    funext p
    rw [evensNormFun]
    by_cases hp : p.1 ∈ SemiProd.fibre
    · rw [if_pos hp, ha1, hbs]
      have h1 : p.1.2 = 1 := (hmemU p.1).mp hp
      show kappa0 twoPointDatum p.1 p.2 = _
      rw [kappa0]
      show twoPointDatum.f p.1.1 (p.1.2 • p.2.1) + twoPointDatum.m p.1.2 p.2.1 = _
      rw [h1]
      simp +decide [twoPointDatum]
    · rw [if_neg hp, ha1, ha1, hbs]
      have h1 : p.1.2 = Multiplicative.ofAdd 1 := by
        rcases hcase p.1.2.toAdd with h | h
        · exact absurd ((hmemU p.1).mpr (by
            have h0 : p.1.2 = Multiplicative.ofAdd (0 : ZMod 2) := by
              rw [← h]
              exact (ofAdd_toAdd _).symm
            simpa using h0)) hp
        · rw [← h]
          exact (ofAdd_toAdd _).symm
      show kappa0 twoPointDatum p.1 p.2 = _
      rw [kappa0]
      show twoPointDatum.f p.1.1 (p.1.2 • p.2.1) + twoPointDatum.m p.1.2 p.2.1 = _
      rw [h1]
      simp +decide [twoPointDatum, Prod.swap]
  have hmem : (fun p : SemiProd (Multiplicative (ZMod 2)) swapE ×
        SemiProd (Multiplicative (ZMod 2)) swapE ↦ kappa0 twoPointDatum p.1 p.2)
      ∈ Z2 (SemiProd (Multiplicative (ZMod 2)) swapE) (ZMod 2) := by
    rw [hfun]
    exact evensNormFun_mem_Z2 htriv hUo hUi hs fibreCoord hα hαc
  rw [H2ofFun_of_mem hmem]
  exact congrArg (H2mk _ _) (Subtype.ext hfun)

end TwoPoint

/-! ## Lemma 6.15: the quadratic orbit–stabilizer Shapiro ledger  (eqs. (103)–(105))

Stated per orbit type on a single regular summand `W = 𝔽₂[G/N]` (the multi-orbit assembly is
additivity of `graphPullback` in the datum; deviation note).  Here `G` is the ambient (profinite)
group, `N ◁ G` open of finite index (`K/F` Galois with group `G/N`), `α ∈ Z¹(N, 𝔽₂)` the scalar
Shapiro coordinate, and `b = Sh(α)` the normalized Shapiro cochain (`GQ2/Corestriction.lean`). -/

section Shapiro

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable (N : Subgroup G) [N.Normal]

-- `RegRep`, `squareOrbitDatum`, `freeOrbitDatum`, `invOrbitDatum` moved to `GQ2/OrbitData.lean`
-- (top-level `namespace GQ2`), reachable here unqualified.  See `docs/orbit-data-refactor.md`.

variable [Finite (G ⧸ N)]

/-- **Lemma 6.15, eq. (103) (square orbits)**: the graph pullback of the square-orbit datum at
the Shapiro cochain of `α` is the corestriction of the cup square `α ⌣ α`.
[P-14 statement; proof P-15.] -/
theorem lemma_6_15_square (hNo : IsOpen (N : Set G)) (α : Z1 N (ZMod 2)) :
    H2ofFun G (graphPullback (squareOrbitDatum N) (QuotientGroup.mk' N) (shapiroFun N α.1))
      = H2ofFun G (cor2Fun N (fun p ↦ α.1 p.1 * α.1 p.2)) := by
  -- The two raw cochains agree on the nose, so `H2ofFun` of them agree (no cocycle needed).
  congr 1
  funext p
  obtain ⟨g, h0⟩ := p
  -- the regular-action index `(ḡ)⁻¹·k` equals the `G`-action `g⁻¹ • k` on `G/N`
  have hact : ∀ u : G ⧸ N, (QuotientGroup.mk' N g)⁻¹ * u = g⁻¹ • u := by
    intro u
    refine QuotientGroup.induction_on u fun u₀ => ?_
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
  -- `graphPullback` reduces definitionally (the regular-action smul is `x (c⁻¹·k)`)
  show (∑ᶠ k : G ⧸ N,
          α.1 (lTrans N k g) * α.1 (lTrans N ((QuotientGroup.mk' N g)⁻¹ * k) h0)) + 0
      = ∑ᶠ u : G ⧸ N, α.1 (lTrans N u g) * α.1 (lTrans N (g⁻¹ • u) h0)
  rw [add_zero]
  refine finsum_congr fun u => ?_
  show α.1 (lTrans N u g) * α.1 (lTrans N ((QuotientGroup.mk' N g)⁻¹ * u) h0)
      = α.1 (lTrans N u g) * α.1 (lTrans N (g⁻¹ • u) h0)
  rw [hact u]

/-- **Lemma 6.15, eq. (104) (free orbits)**: the graph pullback of the free-orbit datum with
shift `ḡ` at the Shapiro cochains of `α, β` is the corestriction of `α ⌣ ḡβ` (`ḡβ` = conjugate
cocycle through a lift `ĝ` of `ḡ`).  [P-14 statement; proof P-15.] -/
theorem lemma_6_15_free (hNo : IsOpen (N : Set G)) (α β : Z1 N (ZMod 2)) (ghat : G) :
    H2ofFun G (graphPullback (freeOrbitDatum N (QuotientGroup.mk' N ghat))
        (QuotientGroup.mk' N) (fun γ ↦ (shapiroFun N α.1 γ, shapiroFun N β.1 γ)))
      = H2ofFun G (cor2Fun N (fun p ↦ α.1 p.1 *
          β.1 ⟨ghat⁻¹ * (p.2 : G) * ghat, by
            simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ p.2.2 ghat⁻¹⟩)) :=
  -- Spliced (P-15c): proved in `GQ2/ShapiroLedger.lean` (`Ax = ∅`, std-3) — the ĝ-shift
  -- coboundary `δ¹Λ` via `H2ofFun_eq_of_sub_mem_B2`.  See `docs/orbit-data-refactor.md`.
  ShapiroLedger.lemma_6_15_free_aux N hNo α β ghat

/-- **Lemma 6.15, eq. (105) (involution orbits)**: for an involution `ḡ = mk ĝ` of `G/N`, the
graph pullback of the involution-orbit datum at the Shapiro cochain of `α` is
`cor_{K₀/F} N^{Ev}_{K/K₀}(α)`, where `U₀ = ⟨N, ĝ⟩` is the index-2-over-`N` subgroup (fixed field
`K₀ = K^{⟨ḡ⟩}`) and the Evens norm is the repo's two-point graph cocycle (98).  This statement
also absorbs the paper's eq. (100) (deviation note).  Quantified over the membership/side proofs.
[P-14 statement; proof P-15.] -/
theorem lemma_6_15_involution (hNo : IsOpen (N : Set G)) (α : Z1 N (ZMod 2)) (ghat : G)
    (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (hs : (⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩ : U₀)
        ∉ N.subgroupOf U₀) :
    H2ofFun G (graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat))
        (QuotientGroup.mk' N) (shapiroFun N α.1))
      = H2ofFun G (cor2Fun U₀ (fun p ↦
          evensNormFun (N.subgroupOf U₀)
            ⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩
            (fun u ↦ α.1 ⟨u.1.1, u.2⟩) (p.1, p.2))) :=
  -- Spliced (P-15c): proved in `GQ2/ShapiroLedger.lean` (`Ax = ∅`, std-3) — the compatible
  -- transversal `invLift` (words based at `phi`'s own orbit-canonical points), the position
  -- identity, the aligned-locus coboundary `invLambda`, and the generic transversal-change
  -- brick `cor2FunT_sub_cor2Fun_mem_B2`, chained through `H2ofFun_eq_of_sub_mem_B2`.
  ShapiroLedger.lemma_6_15_involution_aux N hNo α ghat hg hg2 U₀ hU₀ hs

end Shapiro

/-! ## The Hilbert ledger: deep units  (Lemma 6.16 → Lemma 6.17 → Proposition 6.18) -/

section DeepUnits

/-- **Deep unit** relative to a subgroup `N ≤ G_ℚ₂` with fixed field `K` (§6.3, eqs. (93)/(94)):
`A ∈ U_{e+1}(K) ⊂ K^×/K^{×2}` via the representative `A = 1 + 2b`, `b ∈ 𝔭_K` — phrased through
the spectral norm on `ℚ̄₂` (`‖b‖ < 1 ⟺ v_K(b) ≥ 1`, so `‖A − 1‖ < ‖2‖ ⟺ v_K(A−1) ≥ e+1`,
`e = v_K(2)`); `K`-rationality of `A` and `b` is `N`-fixedness.  No ramification-index
bookkeeping is needed. -/
def IsDeepUnit (N : Subgroup (Kummer.GaloisGroup ℚ_[2])) (A : ℚ̄₂) : Prop :=
  A ≠ 0 ∧ (∀ g ∈ N, g • A = A) ∧
    ∃ b : ℚ̄₂, (∀ g ∈ N, g • b = b) ∧ A = 1 + 2 * b ∧ ‖b‖ < 1

/-- **Lemma 6.16 (deep-unit Evens norm), eq. (110)**: for an unramified quadratic extension
`L/k` of finite dyadic local fields (encoded: `G_L ≤ G_k` of index 2, equal norm value groups)
and a deep unit `a ∈ U_{e+1}(L)`, the index-two Evens norm of the Kummer class `[a]` vanishes:
`N^{Ev}_{L/k}([a]) = 0` in `H²(G_k, 𝔽₂)`.

The Evens norm is the repo's `evensNormH2Z` (the two-point graph cocycle (98)); the proof route
is the Hilbert-symbol ledger (111)–(114) through axioms B9/B11 — `GQ2/HilbertLedger.lean`
(P-15e, Ax: B7′, B9, B11).  Quantified over the side-condition proofs.  [P-14 statement;
**P-15e amendment**: added `[FiniteDimensional ℚ_[2] k]` (the statement's "finite dyadic
local fields", needed by B9/B11) and the **Kummer presentation of `L/k`** — the generator data
`(d, δ, hδ, hLδ)` with `L = k(δ)`, `δ² = d`, and the coordinates `(u, v, hAuv)` of the deep
unit `A = u + vδ` (the paper's "write `L = k(√d)`, `a = u + v√d`"); consumers (6.17, P-15f)
construct these concretely, and char-≠2 Kummer theory guarantees them abstractly.  See
`docs/section67-extraction.md`.] -/
theorem lemma_6_16 (k L : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
    (hkL : k ≤ L)
    (hindex : ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)).index = 2)
    (hunram : ∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y : ℚ̄₂, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖)
    (d : (↥k)ˣ) (δ : ℚ̄₂) (hδ : δ ^ 2 = ((d : ↥k) : ℚ̄₂)) (hδL : δ ∈ L)
    (hLδ : (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
      = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup))
    (A β : ℚ̄₂) (hdeep : IsDeepUnit L.fixingSubgroup A) (hβ : β ^ 2 = A) (hβ0 : β ≠ 0)
    (u : (↥k)ˣ) (v : ↥k) (hAuv : A = ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ)
    (s : k.fixingSubgroup) (hs : s ∉ (L.fixingSubgroup).subgroupOf (k.fixingSubgroup))
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((L.fixingSubgroup).subgroupOf (k.fixingSubgroup) :
        Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (hα : ∀ u v : (L.fixingSubgroup).subgroupOf (k.fixingSubgroup),
      Kummer.kummerCocycleFun β ((u * v : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
        = Kummer.kummerCocycleFun β ((u : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
          + Kummer.kummerCocycleFun β ((v : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hαc : Continuous fun u : (L.fixingSubgroup).subgroupOf (k.fixingSubgroup) ↦
      Kummer.kummerCocycleFun β ((u : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])) :
    evensNormH2 htriv hUo hindex hs
      (fun u ↦ Kummer.kummerCocycleFun β ((u : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
      hα hαc = 0 := by
  -- P-15e splice: reduce to `HilbertLedger.evensNorm_deepUnit_vanish` (self-contained over
  -- `stabilizer δ`).  Extract `b` from the deep unit, build the norm unit `n = u²−d·v²`
  -- (nonzero: `A = β² ≠ 0` and `δ ∉ k`), convert `hunram` via `δ ∈ L`, transport along `hLδ`.
  obtain ⟨hA0, _hAfix, b, _hbfix, hAb, hb⟩ := hdeep
  have hA0' : ((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ ≠ 0 := hAuv ▸ hA0
  -- `δ ∉ k`: else `k.fixingSubgroup ≤ stabilizer δ`, forcing `L.fs.subgroupOf = ⊤`, index 1 ≠ 2.
  have hδnk : δ ∉ k := by
    intro hδk
    have hle : k.fixingSubgroup ≤ MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ := fun g hg =>
      MulAction.mem_stabilizer_iff.mpr (by simpa using fixingSubgroup_smul k hg ⟨δ, hδk⟩)
    rw [hLδ, Subgroup.subgroupOf_eq_top.mpr hle, Subgroup.index_top] at hindex
    exact absurd hindex (by norm_num)
  -- the norm `n = u² − d·v²` is nonzero, hence a unit
  have hne : (u : ↥k) ^ 2 - (d : ↥k) * v ^ 2 ≠ 0 := by
    intro h0
    have hc0 : ((u : ↥k) : ℚ̄₂) ^ 2 - ((d : ↥k) : ℚ̄₂) * (v : ℚ̄₂) ^ 2 = 0 := by
      have h := congrArg (fun t : ↥k => (t : ℚ̄₂)) h0
      push_cast at h; simpa using h
    have hconj0 : ((u : ↥k) : ℚ̄₂) - (v : ℚ̄₂) * δ = 0 := by
      have hfac : (((u : ↥k) : ℚ̄₂) + (v : ℚ̄₂) * δ) * (((u : ↥k) : ℚ̄₂) - (v : ℚ̄₂) * δ) = 0 := by
        have hh : ((u : ↥k) : ℚ̄₂) ^ 2 - δ ^ 2 * (v : ℚ̄₂) ^ 2 = 0 := by
          rw [hδ]; linear_combination hc0
        linear_combination hh
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hA0'
      · exact h
    have hvne : v ≠ 0 := by
      intro hv
      apply unitCoe_ne_zero k u
      rw [hv] at hconj0
      simpa using hconj0
    apply hδnk
    have hδeq : δ = (((u : ↥k) / v : ↥k) : ℚ̄₂) := by
      rw [IntermediateField.coe_div, eq_div_iff (by simpa using hvne)]
      linear_combination -hconj0
    rw [hδeq]
    exact SetLike.coe_mem _
  set n : (↥k)ˣ := Units.mk0 ((u : ↥k) ^ 2 - (d : ↥k) * v ^ 2) hne with hndef
  -- convert `hunram` to the `x + yδ` form (uses `δ ∈ L`)
  have hunram' : ∀ z : ℚ̄₂, z ≠ 0 → (∃ x y : ↥k, z = ↑x + ↑y * δ) →
      ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : ℚ̄₂)‖ := by
    rintro z hz0 ⟨x, y, rfl⟩
    have hzL : (↑x : ℚ̄₂) + ↑y * δ ∈ L :=
      add_mem (hkL x.2) (mul_mem (hkL y.2) hδL)
    obtain ⟨w, hw0, hwk, hnorm⟩ := hunram _ hz0 hzL
    exact ⟨⟨w, hwk⟩, fun h => hw0 (congrArg Subtype.val h), hnorm⟩
  -- transport the goal's `evensNormH2` args along `hLδ`, then apply the capstone
  revert hindex hs hUo hα hαc
  rw [hLδ]
  intro hindex hs hUo hα hαc
  exact evensNorm_deepUnit_vanish k u n d v (by rw [hndef, Units.val_mk0]) δ β hδ
    (hβ.trans hAuv) hβ0 hindex s hs htriv hUo _ (fun _ => rfl) hα hαc b hb (hAuv ▸ hAb) hunram'

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **The deep half `X₊`** (Lemma 6.17): the classes `x ∈ H¹(G_ℚ₂, V)` all of whose scalar
Kummer coordinates are deep units — for every functional `φ ∈ V^∨`, the restriction of `φ∘x`
to `N = ker ρ` (`= G_K`, `K` the splitting field) is the Kummer class of a deep unit of `K`.
Encodes `X₊ = Hom_{H_V}(V^∨, U_{e+1}) ⊂ H¹(ℚ₂, V)` without the Kummer-theoretic
identification of `H¹` (which is proof-side, P-15). -/
def deepPart (ρ : ContinuousMonoidHom AbsGalQ2 C) : Set (H1 AbsGalQ2 V) :=
  {x | ∀ φ : V →+ ZMod 2,
    ∃ (A β : ℚ̄₂) (_ : IsDeepUnit (ρ.toMonoidHom.ker :
        Subgroup AbsGalQ2) A) (_ : β ^ 2 = A) (_ : β ≠ 0),
      H1ofFun ρ.toMonoidHom.ker
          (fun n ↦ Kummer.kummerCocycleFun β (n : AbsGalQ2))
        = H1ofFun ρ.toMonoidHom.ker (fun n ↦ φ ((Quotient.out x).1 (n : AbsGalQ2)))}

/- **Lemma 6.17 (the deep half is totally singular)** — both clauses PROVED downstream, statement
moved out (P-15f8/f2d, the P-15d/`lemma_6_14` statement-move pattern; sorried stubs removed
2026-07-08).  The frozen statements are re-homed with their proofs:

* dimension clause `#X₊² = #H¹` — **`GQ2.ResidueLift.lemma_6_17_dim_final`** (P-15f8, std-3 +
  {B6, B7, B11a, B12, B13}); the graded self-duality count assembled off f5/f6/f7 with the
  residue-trivial tame lift proved in-repo (no residue-field axiom).
* vanishing clause `Q⁰_loc|X₊ = 0` — **`GQ2.VanishClose.lemma_6_17_vanish_final`** (P-15f2d,
  std-3 + {B9, B11a, B11b, B13}); the §6.2 orbit decomposition + §6.3 deepness through the
  regular embedding, amended (P-20 flag) with the reciprocity datum `(R, horient)` its
  involution `hunram` requires.

Their sole consumer `prop_6_18_ramified` is re-homed to **`GQ2.DetRamified`** (downstream of both
proofs) and cited from there.  The amendments (`hc`, `hV2`, the invariant-form package
`(q, hq, hns, hinv)`, and `(R, horient)` on the vanish side) travel with the moved statements;
route analysis / counterexamples: `docs/p15f1-scoping.md`, `docs/p15f2-handoff.md`. -/

/- **Proposition 6.18 (dyadic base determinant theorem), eq. (115), ramified case**: the local
base determinant form has the positive Gauss sign,
`#(Q⁰_loc)⁻¹(0) = 2^{2m−1} + 2^{m−1}` (`#V = 2^{2m}`).  With Prop 6.9 this is Corollary
6.19(iv): the two sources have equal base Gauss sums.
**Proved (P-15f, modulo Lemma 6.17 above) as `GQ2.DeepPart.prop_6_18_ramified`** in
`GQ2/DeepPart.lean` (downstream — its proof consumes the `Q⁰_loc` quadratic/nonsingular
structure layer built there off `RepIndependence`, which imports this file; statement moved
out to break the import cycle, per the P-15d pattern).  The `hc : Surjective ⇑c` amendment
travels with it; `hV2` is derivable there from `hcard` + `hsimple` via additive Cauchy.
Axioms: std-3 + B7 (B6 via the `D` parameter) + `sorryAx` through the two Lemma 6.17 sorries
(the remaining §6.3 Kummer cores). -/

/- **Proposition 6.18, eq. (115), unramified case**: negative Gauss sign,
`#(Q⁰_loc)⁻¹(0) = 2^{2m−1} − 2^{m−1}`.
**Proved (P-15f3, 2026-07-05) as `GQ2.UnramifiedModel.prop_6_18_unramified`** in
`GQ2/UnramifiedModel.lean` (downstream — its proof consumes the `Q0loc` structure layer of
`DeepPart`/`RepIndependence`, which import this file; statement moved out to break the import
cycle, per the `prop_6_18_ramified`/P-15d pattern; sorried copy removed 2026-07-07).
The `hc : Function.Surjective ⇑c` amendment travels with it (flag for P-20), as does the
route: C cyclic → Schur field `F` → `H¹` an `F`-line → C-invariant Hermitian trace model →
`card_normOne_invariant_form_zero`.  Axioms: std-3 + B7 (B6 via the `D : TateDuality 2`
parameter), no `sorryAx`. -/

/- **Lemma 6.14 (regular-module realization), eq. (102)**: the base connecting map computed
through an equivariant split embedding `i : V →+ W` into a regular-type module agrees with the
`W`-level map at the pushed class: `Q⁰_{loc, i^*dat_W}(x) = Q⁰_{loc, dat_W}(i_* x)`.
**Proved (P-15d, std-3, no B-axioms) as `GQ2.RepIndependence.lemma_6_14`** in
`GQ2/RepIndependence.lean` (downstream — its proof uses `Q0loc`/`graphPullback`/`kappa0`/`SemiProd`
from this file, so the statement is moved out to break the import cycle, per the P-08/P-09/P-10
pattern).  The proved statement is **amended** (documented) with the compatibility hypotheses
`Q⁰_loc` requires: `hdatW : IsEquivariantFactorSet q datW`, `hiC : ∀ c v, i (c • v) = c • i v`
(`i` a `C`-module map, eq. (77)'s `i ⋊ 1`), `hρW : ∀ g w, g • w = ρ g • w`.  Proof: `graphPullback`
is a pullback of the factor-cocycle `κ⁰`; changing the `Quotient.out` representative conjugates the
classifying map by `(−w₀,1) ∈ V⋊C`, and inner automorphisms act trivially on `H²`
(`RepIndependence.innerConj` / `repIndep`). -/

end DeepUnits

/-! ## Transgression and the marking-preserving shear  (§6.4: Lemmas 6.21, 6.22) -/

section Transgression

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]

/-- **Lemma 6.21 (determinant transgression), consequence form** — *relative to the fixed
equivariant class* `κ⁰_q`: if a finite extension `1 → V → B → C → 1` (encoded: `p : B ↠ C` with
central-kernel data `i`) admits a class `ξ ∈ Z²(B, 𝔽₂)` whose fibre restriction has square map
a **nonsingular** `q` (i.e. `ξ(i v, i v) = q v`), and an equivariant factor-set datum for `q` is
supplied (`(dat, hdat)` = Lemma 6.1's `κ⁰_q` — the paper's stated hypothesis *"assume a
zero-section-normalized equivariant class restricting to `q` on `V` has been fixed"*), then the
extension splits: `B ≅ V ⋊ C` over `C`.  The paper's obstruction formula `d₂(q) = B_q^♭∘η`
(eq. (116)) is the proof mechanism (P-15i, `GQ2/Transgression.lean`); only the splitting
consequence is consumed (§§8–9).  Deviation note, amended 2026-07-04: the `κ⁰_q` hypothesis
restores the paper's relative clause, dropped by the original consequence-form extraction —
without it the intrinsic equivariance obstruction blocks the proof; see
`docs/p15i-transgression-gap.md`.  [P-14 statement; proof P-15i.] -/
theorem lemma_6_21 {B : Type} [Group B] [Finite B]
    (p : B →* C) (hp : Function.Surjective p)
    (i : Multiplicative V →* B) (hi : Function.Injective i)
    (hrange : i.range = p.ker)
    (hconj : ∀ (b : B) (v : V), b * i (Multiplicative.ofAdd v) * b⁻¹
      = i (Multiplicative.ofAdd (p b • v)))
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ξ : B × B → ZMod 2)
    (hcocycle : ∀ g h k : B, ξ (h, k) + ξ (g, h * k) = ξ (g * h, k) + ξ (g, h))
    (hξq : ∀ v : V, ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd v)) = q v) :
    ∃ s : C →* B, ∀ cc : C, p (s cc) = cc := by
  obtain ⟨t, ht_quad, ht_mul⟩ :=
    Transgression.equivariant_lift_of_factorSet i q hq hns ξ hcocycle hξq dat hdat
  exact Transgression.splitting_of_global_cocycle p hp i hrange hconj q hq hns ξ hcocycle hξq
    t ht_quad ht_mul

/-- The filtration-one difference term `Γ_γ` (eq. (64)) as a raw function on the product
carrier `V × C`: `Γ_γ((v,c),(w,d)) = γ(c)(c·w)`. -/
def gammaEdge (γ : C → V →+ ZMod 2) : (V × C) → (V × C) → ZMod 2 :=
  fun p q ↦ γ p.2 (p.2 • q.1)

/-- The inflated scalar term `inf δ` as a raw function on `V × C`. -/
def inflScalar (δ : C × C → ZMod 2) : (V × C) → (V × C) → ZMod 2 :=
  fun p q ↦ δ (p.2, q.2)

/-- The shear `s_a(v, c) = (v + a(c), c)` (Lemma 6.22). -/
def shear (a : C → V) : V × C → V × C := fun p ↦ (p.1 + a p.2, p.2)

/-- The base phase term `Θ⁰_q(a) = (a, id_C)^* κ⁰_q` (eq. (122)), a raw function on `C × C`. -/
def thetaPhase (dat : FactorSet C V) (a : C → V) : C × C → ZMod 2 :=
  graphPullback dat id a

/-- The mixed term `(γ ⌣ a)(c, d) = γ(c)(c·a(d))` (eq. (123)). -/
def gammaCupA (γ : C → V →+ ZMod 2) (a : C → V) : C × C → ZMod 2 :=
  fun p ↦ γ p.1 (p.1 • a p.2)

/-- **Lemma 6.22 (marking-preserving shear), eq. (121)**: pulling a general determinant class
`κ = κ⁰_q + Γ_γ + inf δ` back along the shear `s_a` (for a 1-cocycle `a ∈ Z¹(C, V)`) shifts the
edge by the polar adjoint and the scalar by the phase terms:

  `s_a^*κ = κ⁰_q + Γ_{γ + B_q^♭ a} + inf(δ + Θ⁰_q(a) + γ ⌣ a)`,

as an identity of `𝔽₂`-valued functions on `(V ⋊ C)²` **up to a normalized coboundary** — here
stated cochain-exactly modulo the coboundary of an explicit 1-cochain `w`, quantified
existentially.  In particular (`q` nonsingular) a unique edge-killing shear class exists —
recorded as the paper's phase-cover input to §8 (Prop 8.8).  [P-14 statement; proof P-15.] -/
theorem lemma_6_22 (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (γ : C → V →+ ZMod 2) (δ : C × C → ZMod 2)
    (a : C → V) (ha : ∀ c d : C, a (c * d) = a c + c • a d) :
    ∃ w : V × C → ZMod 2,
      ∀ p q' : V × C,
        (kappa0 dat (shear a p) (shear a q') + gammaEdge γ (shear a p) (shear a q')
            + inflScalar δ (shear a p) (shear a q'))
          = (kappa0 dat p q'
              + gammaEdge (fun c ↦ γ c + AddMonoidHom.mk' (polar q (a c))
                  (fun v v' ↦ hq.polar_add_right (a c) v v')) p q'
              + inflScalar (fun cd ↦ δ cd + thetaPhase dat a cd + gammaCupA γ a cd) p q')
            + (w (p.1 + p.2 • q'.1, p.2 * q'.2) + w p + w q') := by
  -- the marking cochain: `w(v,c) = f(v, a(c))`
  refine ⟨fun p => dat.f p.1 (a p.2), ?_⟩
  rintro ⟨v, c⟩ ⟨w, d⟩
  obtain ⟨fcoc, _fdiag, fpol, _fzl, _fzr, mquad, _mmul, _mone⟩ := hdat
  simp only [kappa0, gammaEdge, inflScalar, shear, thetaPhase, gammaCupA, graphPullback,
    id_eq, AddMonoidHom.add_apply, AddMonoidHom.mk'_apply, map_add, smul_add]
  rw [ha c d]
  set X := c • w with hX
  set Y := c • a d with hY
  -- structural identities
  have hmq := mquad c w (a d)
  rw [← hX, ← hY] at hmq
  have hp := fpol (a c) X
  have hc1 := fcoc v (a c) (X + Y)
  have hc2 := fcoc v X (a c + Y)
  have hc3 := fcoc (a c) X Y
  have hc4 := fcoc X (a c) Y
  -- normalize `dat.f` arguments so the atoms match across instances
  have harg1 : a c + (X + Y) = X + (a c + Y) := by abel
  have harg2 : a c + X = X + a c := by abel
  rw [harg1] at hc1
  rw [harg2] at hc3
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    hmq + hp + hc1 + hc2 + hc3 + hc4

end Transgression

end SectionSix

end

end GQ2
