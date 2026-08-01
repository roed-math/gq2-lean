/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.Mpc

/-!
# Dyadic campaign, ticket WMP-d: the procyclic `M_α` closer's standard items

WMP-c (`GQ2/Dyadic/Certificates/Mpc.lean`) discharged WMP-b's five-item handoff; this leaf
carries the *standard* `-c` closer items every sibling lane already has — the Stokes family, the
endpoint condition, the duality instantiation and a scalar Gram — plus WMP-c's one named
computational residual, the linear copy's Fox row.

-/

namespace GQ2.Dyadic.Certificates.MProcyclic

open GQ2.FoxH GQ2.Dyadic.Words.Mpc

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## §1 The traced mod-2 exponent, constructor by constructor

`heisEps i ∘ heisToFree E E₂` is what the endpoint condition measures.  The siblings computed it
by unfolding each word by hand; the target `Multiplicative (ZMod 2)` is *commutative and of
exponent two*, so every constructor has a one-line rule and the whole computation becomes
arithmetic.  Lane-generic — nothing below mentions this word (hoist candidate). -/

section Eps

variable {X : Type*} [DecidableEq X] (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : X)

/-- **The traced mod-2 exponent of a reflected word** at a resolver pair: the `i`-slot of the
abelianized, mod-2 exponent vector of `heisToFree E E₂ w`. -/
noncomputable def epsZ (w : PWord X) : Multiplicative (ZMod 2) :=
  heisEps i (heisToFree E E₂ w)

@[simp] theorem epsZ_one : epsZ E E₂ i (.one : PWord X) = 1 := map_one _

@[simp] theorem epsZ_gen (j : X) :
    epsZ E E₂ i (.gen j) = Multiplicative.ofAdd (if j = i then (1 : ZMod 2) else 0) :=
  Certificates.heisEps_of i j

@[simp] theorem epsZ_mul (u v : PWord X) :
    epsZ E E₂ i (.mul u v) = epsZ E E₂ i u * epsZ E E₂ i v :=
  map_mul _ _ _

@[simp] theorem epsZ_inv (u : PWord X) : epsZ E E₂ i (.inv u) = (epsZ E E₂ i u)⁻¹ :=
  map_inv _ _

/-- Conjugation is invisible: the target is commutative. -/
@[simp] theorem epsZ_conj (u g : PWord X) : epsZ E E₂ i (.conj u g) = epsZ E E₂ i u := by
  show heisEps i (conjR (heisToFree E E₂ u) (heisToFree E E₂ g)) = _
  rw [map_conjR, conjR_eq_self_of_comm]
  rfl

/-- Commutators are invisible. -/
@[simp] theorem epsZ_comm (u v : PWord X) : epsZ E E₂ i (.comm u v) = 1 := by
  show heisEps i (commR (heisToFree E E₂ u) (heisToFree E E₂ v)) = _
  exact monoidHom_commR_eq_one _ _ _

@[simp] theorem epsZ_zpow (u : PWord X) (k : ℤ) :
    epsZ E E₂ i (.zpow u k) = (epsZ E E₂ i u) ^ k :=
  map_zpow _ _ _

@[simp] theorem epsZ_z2pow (u : PWord X) (z : ℤ_[2]) :
    epsZ E E₂ i (.z2pow u z) = (epsZ E E₂ i u) ^ E₂ z :=
  map_zpow _ _ _

@[simp] theorem epsZ_profPow (u : PWord X) (γ : Zhat) :
    epsZ E E₂ i (.profPow u γ) = (epsZ E E₂ i u) ^ E γ :=
  map_zpow _ _ _

@[simp] theorem epsZ_omega2Pow (u : PWord X) :
    epsZ E E₂ i (PWord.omega2Pow u) = (epsZ E E₂ i u) ^ E omega2 :=
  map_zpow _ _ _

theorem epsZ_prodList : ∀ ws : List (PWord X),
    epsZ E E₂ i (PWord.prodList ws) = (ws.map (epsZ E E₂ i ·)).prod
  | [] => map_one _
  | w :: ws => by
      rw [PWord.prodList_cons, epsZ_mul, epsZ_prodList ws, List.map_cons, List.prod_cons]

/-! ### The two arithmetic facts of an exponent-two target -/

/-- Every element of the traced target is an involution. -/
theorem mult_zmod2_sq (u : Multiplicative (ZMod 2)) : u * u = 1 := by revert u; decide

/-- Even integer powers are trivial. -/
theorem mult_zmod2_even_zpow (u : Multiplicative (ZMod 2)) {k : ℤ} (hk : Even k) : u ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [show j + j = 2 * j by ring, zpow_mul, zpow_two, mult_zmod2_sq, one_zpow]

/-- A natural even power is trivial. -/
theorem epsZ_even_zpow (u : PWord X) {k : ℕ} (hk : Even k) :
    epsZ E E₂ i (.zpow u (k : ℤ)) = 1 := by
  rw [epsZ_zpow]
  exact mult_zmod2_even_zpow _ (by exact_mod_cast hk)

end Eps

/-! ## §2 The `E₂^pc` count, and the traced vector of the procyclic-`M` word

⚠ The finding WMP-c predicted **by inspection**, machine-checked here.  The orbit-norm block
`E₂^pc = δ₂^{σ₂^s} · 𝒩_{U,m}(z)^{U^m}` carries the letter `δ₂` exactly `1 + 2m` times — one from
the head conjugate, two per orbit-norm factor (`z = δ₂δ₂^{σ₂^p}` in both emitted spellings, the
`p = 0` display `δ₂²` included).  That count is **odd at every `p`**, so `E₂^pc` is *visible* in
the traced vector: `2m` of the occurrences cancel in pairs and the head survives.

Consequence: the procyclic-`M` row does **not** die syntactically the way the compact-`M` row
does (`MCompact.heisEps_eRevW`: there each `δ` occurs exactly twice).  The endpoint condition
needs the **tame row** to absorb the surviving `δ₂`, exactly as in the pilot — WN0-c's route,
not WM0-c's.  Everything else in the word — both squares, all four commutators, both `E₀₁^pc`
copies, the plus block's `D₀²`, `Ĉ₀^{2^α}`, `C₀^{2^α}` and the handles — is invisible, and the
last two need `α ≥ 1`.  -/

section TracedVector

variable {h : ℕ} (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Generator (2 + 2 * h))

/-- `σ₂ = σ^{ω₂}` resolves to the `E ω₂`-th power of `σ`. -/
@[simp] theorem epsZ_sigma2W :
    epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))
      = (epsZ E E₂ i (PWord.gen (Generator.sigma : Generator (2 + 2 * h)))) ^ E omega2 :=
  map_zpow _ _ _

/-- Every `σ₂`-power display is a power of `σ₂`. -/
theorem epsZ_sig2PowW : ∀ k : ℕ,
    epsZ E E₂ i (sig2PowW h k) = (epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))) ^ (k : ℤ)
  | 0 => by rw [show sig2PowW h 0 = .zpow sigma2W ((0 : ℕ) : ℤ) from rfl, epsZ_zpow]
  | 1 => by rw [show sig2PowW h 1 = sigma2W from rfl]; simp
  | k + 2 => by rw [show sig2PowW h (k + 2) = .zpow sigma2W ((k + 2 : ℕ) : ℤ) from rfl, epsZ_zpow]

/-- **The `δ`-row**: `δ_i = (x_iτ)^{ω₂}x_i⁻¹` resolves to `(x_iτ)^{E ω₂}x_i⁻¹`.  This is the only
letter of the whole word that ever reaches the traced vector. -/
theorem epsZ_dW (j : Fin 3) :
    epsZ E E₂ i (dW h j)
      = (epsZ E E₂ i (PWord.gen (coreLetter h j)) * epsZ E E₂ i (PWord.gen Generator.tau))
            ^ E omega2
          * (epsZ E E₂ i (PWord.gen (coreLetter h j)))⁻¹ := by
  rw [dW, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, uW,
    epsZ_omega2Pow, epsZ_prodList, epsZ_inv]

/-- `C₀ = x₂σ₂^s`. -/
theorem epsZ_c0W (s' : ℕ) :
    epsZ E E₂ i (c0W h s')
      = epsZ E E₂ i (PWord.gen (coreLetter h 2))
          * (epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))) ^ (s' : ℤ) := by
  rw [c0W, epsZ_prodList]
  simp

/-- `Ĉ₀ = σ₂^s`. -/
theorem epsZ_c0HatW (s' : ℕ) :
    epsZ E E₂ i (c0HatW h s')
      = (epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))) ^ (s' : ℤ) :=
  epsZ_zpow _ _ _ _ _

/-- **`E₀₁^pc` is invisible**: each of `δ₀`, `δ₁` occurs exactly twice. -/
theorem epsZ_e01W (aa bb : ℕ) : epsZ E E₂ i (e01W h aa bb) = 1 := by
  rw [e01W, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_conj,
    epsZ_prodList]
  rw [show ∀ u v : Multiplicative (ZMod 2), u * (u * v) * v = (u * u) * (v * v) by
      intro u v; group,
    mult_zmod2_sq, mult_zmod2_sq, one_mul]

/-- **The orbit-norm base is invisible**: `z = δ₂δ₂^{σ₂^p}` carries `δ₂` twice, in both emitted
spellings — the `p = 0` display `δ₂²` included. -/
theorem epsZ_zW : ∀ pp : ℕ, epsZ E E₂ i (zW h pp) = 1
  | 0 => by
      rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl]
      exact epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩
  | q + 1 => by
      rw [show zW h (q + 1) = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (q + 1))] from rfl,
        epsZ_prodList]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_conj]
      exact mult_zmod2_sq _

/-- **The `E₂^pc` count, machine-checked**: the orbit-norm block contributes exactly the head
`δ₂`, because the `2m` occurrences inside the norm cancel in pairs.  `1 + 2m` is odd, so the
block is *visible* — the finding this ticket was asked to verify. -/
theorem epsZ_e2W (s' mm pp : ℕ) : epsZ E E₂ i (e2W h s' mm pp) = epsZ E E₂ i (dW h 2) := by
  rw [e2W, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_conj,
    epsZ_prodList]
  rw [List.prod_eq_one, mul_one]
  intro u hu
  rw [Export.orbitNormFactors, List.map_map, List.mem_map] at hu
  obtain ⟨j, -, rfl⟩ := hu
  rw [Function.comp_apply, epsZ_conj, epsZ_zW]

/-- The handle block is invisible (commutators). -/
theorem epsZ_handlesW : epsZ E E₂ i (handlesW h) = 1 := by
  rw [handlesW, epsZ_prodList]
  refine List.prod_eq_one fun u hu => ?_
  rw [List.map_map, List.mem_map] at hu
  obtain ⟨j, -, rfl⟩ := hu
  rw [Function.comp_apply, epsZ_comm]

/-- The handle tail's product is the handle block's exponent. -/
theorem epsZ_prod_handleTailW :
    (((handleTailW h).map (epsZ E E₂ i ·)).prod) = 1 := by
  cases h with
  | zero => rfl
  | succ n =>
      rw [show handleTailW (n + 1) = [handlesW (n + 1)] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact epsZ_handlesW _ _ _

/-- **The linear copy's traced vector is the `E₂^pc` head, and nothing else.** -/
theorem epsZ_mpcLinW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    epsZ E E₂ i (mpcLinW α r pp η h) = epsZ E E₂ i (dW h 2) := by
  rw [mpcLinW, linFactors, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm,
    epsZ_e01W, epsZ_e2W]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩,
    epsZ_even_zpow _ _ _ _ (Nat.even_pow.mpr ⟨even_two, by omega⟩)]
  group

/-- **The hat copy is invisible to the traced vector** — every factor is a square, a commutator,
an even power or the `E₀₁^pc` block. -/
theorem epsZ_mpcHatW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    epsZ E E₂ i (mpcHatW α r pp η h) = 1 := by
  rw [mpcHatW, hatFactors, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm,
    epsZ_e01W]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩,
    epsZ_even_zpow _ _ _ _ (Nat.even_pow.mpr ⟨even_two, by omega⟩)]
  group

/-- The plus block `D₀²[D₀,D₁]` is invisible. -/
theorem epsZ_plusW : epsZ E E₂ i (plusW h) = 1 := by
  rw [plusW, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩]

/-- **The whole procyclic-`M` word's traced vector is one `δ₂`**, at every resolver pair, every
`(r, p, η, h)` and every `α ≥ 1`.  The head of `E₂^pc` survives and nothing else does. -/
theorem epsZ_mpcW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    epsZ E E₂ i (mpcW α r pp η h) = epsZ E E₂ i (dW h 2) := by
  rw [mpcW, epsZ_prodList, List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append,
    show ((linFactors α r pp η h).map (epsZ E E₂ i ·)).prod = epsZ E E₂ i (mpcLinW α r pp η h) from
      (epsZ_prodList E E₂ i _).symm,
    show ((hatFactors α r pp η h).map (epsZ E E₂ i ·)).prod = epsZ E E₂ i (mpcHatW α r pp η h) from
      (epsZ_prodList E E₂ i _).symm,
    epsZ_mpcLinW E E₂ i hα r pp η, epsZ_mpcHatW E E₂ i hα r pp η,
    epsZ_prod_handleTailW E E₂ i]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩]
  group

end TracedVector

/-! ## §3 The resolved relator family and the endpoint condition

The two-relator family of `⟨σ, τ, x₀, …, x_{2h+2} ∣ τ^σ(τ^q)⁻¹, R_{M,pc}⟩` resolved at the
constant integer representative `e` of every profinite exponent, in WMP-b's Jacobian row order
(tame first, wild second).

**The route is the pilot's, and §2 says why it has to be.**  On the compact-`M` row every branch
factor dies syntactically, so `WM0-c`'s endpoint proof carries no `α`-hypothesis; here the
surviving `δ₂` of `E₂^pc` reaches the traced vector and has to be absorbed by the *tame* row.
The per-letter coefficients are then the pilot's exactly — `1 − q + e` on `τ` and `e − 1` on
`x₂`, both even — so the condition holds for all `α ≥ 1`, all `r, p, h`, every `η̂` display,
every even `q` and every odd `e`. -/

section Family

variable {α r pp h q e : ℕ} {η : EtaDisplay}

/-- **The resolved procyclic-`M` relator family** — the `ρ = Fin 2` family the WW3 machinery
consumes, in WMP-b's `foxJacobian` row order. -/
noncomputable def mpcFam (α r pp h q e : ℕ) (η : EtaDisplay) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  ![heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q),
    heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h)]

@[simp] theorem mpcFam_zero :
    mpcFam α r pp h q e η 0
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) := rfl

@[simp] theorem mpcFam_one :
    mpcFam α r pp h q e η 1
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h) := rfl

/-- The tame relator's traced exponent. -/
theorem epsZ_tameRelW (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Generator (2 + 2 * h)) (q' : ℕ) :
    epsZ E E₂ i (tameRelW (2 + 2 * h) q')
      = epsZ E E₂ i (PWord.gen (Generator.tau : Generator (2 + 2 * h)))
          * (epsZ E E₂ i (PWord.gen (Generator.tau : Generator (2 + 2 * h))) ^ (q' : ℤ))⁻¹ := by
  rw [tameRelW, epsZ_mul, epsZ_conj, epsZ_inv, epsZ_zpow]

/-- **The endpoint condition holds at every procyclic-`M` instance** (`α ≥ 1`, any `r, p, h`,
every `η̂` display, `q` even, `e` odd).

The traced vector of the branch word is the single `δ₂` that survives `E₂^pc`'s odd occurrence
count (§2's `epsZ_mpcW`), i.e. `(e − 1)·x₂ + e·τ`; the tame row contributes `(1 − q)·τ`; both
coefficients are even.  So the procyclic row's endpoint data is the *pilot's*, not the compact
`M` row's — the `E₂^pc` block is exactly the difference. -/
theorem mpc_isStokesEndpoint (hα : 1 ≤ α) (hq : Even q) (he : Odd e) :
    IsStokesEndpoint (mpcFam α r pp h q e η) := by
  intro i
  rw [Fin.sum_univ_two, mpcFam_zero, mpcFam_one]
  show Multiplicative.toAdd (epsZ (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) i
      (tameRelW (2 + 2 * h) q))
    + Multiplicative.toAdd (epsZ (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) i (mpcW α r pp η h)) = 0
  rw [epsZ_tameRelW, epsZ_mpcW _ _ _ hα, epsZ_dW]
  simp only [epsZ_gen, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq, zsmul_natCast_zmod2_odd he, CharTwo.neg_eq, CharTwo.neg_eq]
  abel_nf
  simp [CharTwo.two_eq_zero]

/-- The `√−10` instance pin — merge gate 9's row at `(α, r, p, η, h) = (2, 1, 1, .one, 0)`, the
ramified quadratic `q_K = 2` and the odd representative `e = 3`. -/
theorem sqrtNeg10_isStokesEndpoint : IsStokesEndpoint (mpcFam 2 1 1 0 2 3 .one) :=
  mpc_isStokesEndpoint (by norm_num) (by decide) (by decide)

/-- The `√10` twin (`ε = 0`, so `p = 0`): the `zW 0` display `δ₂²` is the case where the
orbit-norm base is a *literal square*, and the count is still odd. -/
theorem sqrt10_isStokesEndpoint : IsStokesEndpoint (mpcFam 2 1 0 0 2 3 .one) :=
  mpc_isStokesEndpoint (by norm_num) (by decide) (by decide)

end Family

/-! ## §4 The Stokes duality payload

WW3's packet-Lem-5.1 engine at the procyclic-`M` family.  The relator hypotheses are gate-level
`evalZ = 1` facts converted through `lift_heisToFree_eq_one_iff`; the endpoint condition is §3's
theorem; per-simple-module duality stays the hypothesis slot it is in the frozen `ℚ₂` chain
(gate-F / AS-lane discharge) — **`hsimp` is AS1's, as in every sibling lane**. -/

section Duality

universe u

variable {C : Type*} [Group C]

/-- **Packet Lem 5.1 at the procyclic-`M` row**: `stokesDuality_of_simple` instantiated at
`mpcFam`.  Downstream, WW3b's `stokesChi1_bijective` turns the conclusion into the perfect
pairing on `H¹` with no further row-specific input. -/
theorem mpc_stokesDuality {α r pp h q e : ℕ} {η : EtaDisplay} [Finite C]
    (t : Marking (2 + 2 * h) C) (hα : 1 ≤ α) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h) = 1)
    (hsimp : ∀ (V : Type u) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (mpcFam α r pp h q e η) V)
    (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : StokesDuality ⇑t (mpcFam α r pp h q e η) A := by
  refine stokesDuality_of_simple ⇑t (mpcFam α r pp h q e η) ?_
    (mpc_isStokesEndpoint hα hq he) hsimp A hA₂
  intro k
  fin_cases k
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrt
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrw

/-- **The traced Stokes pairing of the family** is the sum of the two second-order values — the
bridge between `heisEta1`/`stokesGram` entries and the per-word `heisEvalZ` closed forms, and in
particular the point where WMP-c's `mpcCopiesCancel` enters the Gram. -/
theorem heisEta1_mpcFam_apply {α r pp h q e : ℕ} {η : EtaDisplay} {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) :
    heisEta1 ⇑t (mpcFam α r pp h q e η) x y
      = (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
          (tameRelW (2 + 2 * h) q)).z
        + (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two, mpcFam_zero, mpcFam_one,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

end Duality

/-! ## §5 The scalar certificate: the `√−10` Gram matrices, by kernel `decide`

The cup–Bockstein comparison matrix (`stokesGram`) of the procyclic family on the scalar module
`A = 𝔽₂` (trivial action), at the standard letter basis in the packet column order
`σ, τ, x₀, x₁, x₂`; rows index the primal basis vector, columns the dual one.  Three pins, and
they separate **two** independent sensitivities:

* `√−10` at `e = 1` — the honest resolver class for a 2-group target.  Bockstein diagonals at
  `τ` and `x₀`; cup blocks `(σ,x₀)`, `(σ,x₂)`, `(τ,x₂)`, `(x₀,x₁)`.  Symmetric, as it must be.
* `√−10` at `e = 3` — the other odd class.  Exactly the `{τ,x₂}²` block moves, from
  `[[1,1],[1,0]]` to `[[0,0],[0,1]]`: ticket S1.T's "the lift level is 4, not 2" as a
  kernel-checked matrix pair, on this row as on all four siblings.
* `√10` at `e = 1` — the `ε = 0` twin of the same `(α, r) = (2, 1)` family.

⚠ **Finding — this row is *not* the pilot's, and `ε` is why.**  WM0-c recorded that the compact
`M` scalar Gram reproduces the pilot's entry for entry, because every `σ₂`-power in that word is
even and therefore carries no jet.  Here `p = ε·2^{r−1}` is **odd** at the packet's `√−10`
instance, so `B = x₁σ₂` and the `E₀₁^pc` outer conjugator `σ₂^{p+sm}` are odd `σ₂`-powers and do
carry one.  Comparing the two pins isolates the effect exactly: the `√10` (`ε = 0`) matrix is
the pilot's plus the symmetric `(τ,x₂)` block, and turning `ε` on moves precisely the σ-row's
`{τ, x₀}` entries — `(σ,τ)` off, `(σ,x₀)` on.  So `ε` is visible at second order on the scalar
module, where at first order the pair's σ-column is *zero* (WMP-c's
`foxColumn_sigma_mpcProductW_eq_zero`).  The two statements are about different orders and do
not conflict; recording both is the point.

The kernel budget: three `decide +kernel` calls on a one-dimensional module over a two-element
group — WMP-c drew on the budget not at all, and the dimension here is `1`, far below the
dim-8 orbits that are uncomfortable. -/

section ScalarGram

/-- The trivial action for the scalar pins (WW3's non-exporting `local instance` idiom). -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The all-trivial (scalar/split) marking of the procyclic-`M` alphabet at `h = 0`. -/
def scalarMarkP : Marking (2 + 2 * 0) (Multiplicative (ZMod 2)) := Marking.ofLetters 1 1 ![1, 1, 1]

/-- The packet column order `σ, τ, x₀, x₁, x₂`. -/
def scalarLetterP : Fin 5 → Generator (2 + 2 * 0) := ![.sigma, .tau, .wild 0, .wild 1, .wild 2]

/-- The standard primal basis: a unit offset on one letter. -/
def scalarXP (p : Fin 5) : Generator (2 + 2 * 0) → ZMod 2 :=
  fun g => if g = scalarLetterP p then 1 else 0

/-- The standard dual basis: the identity functional on one letter. -/
noncomputable def scalarYP (p : Fin 5) : Generator (2 + 2 * 0) → ElemDual (ZMod 2) :=
  fun g => if g = scalarLetterP p then (AddMonoidHom.id (ZMod 2) : ElemDual (ZMod 2)) else 0

/-- **The `√−10` scalar Gram at the honest resolver class** (`e = 1`) — merge gate 9's row on
the scalar module.  Bockstein diagonals at `τ` and `x₀`; cup blocks `(σ,x₀)`, `(σ,x₂)`,
`(τ,x₂)`, `(x₀,x₁)`. -/
theorem sqrtNeg10_scalarGram :
    stokesGram ⇑scalarMarkP (mpcFam 2 1 1 0 2 1 .one) scalarXP scalarYP
      = !![0,0,1,0,1; 0,1,0,0,1; 1,0,1,1,0; 0,0,1,0,0; 1,1,0,0,0] := by
  decide +kernel

/-- **The `e = 3` twin**: exactly the `{τ,x₂}²`-block moves with the resolver class — the mod-4
(ℤ/4-lift-level) sensitivity, kernel-checked, and the reason the certificate class is pinned at
`e ≡ 1 (mod 4)`. -/
theorem sqrtNeg10_scalarGram_three :
    stokesGram ⇑scalarMarkP (mpcFam 2 1 1 0 2 3 .one) scalarXP scalarYP
      = !![0,0,1,0,1; 0,0,0,0,0; 1,0,1,1,0; 0,0,1,0,0; 1,0,0,0,1] := by
  decide +kernel

/-- **The `√10` (`ε = 0`) twin at `e = 1`** — the pilot's matrix plus the `(τ,x₂)` block.  The
difference from `sqrtNeg10_scalarGram` is exactly the σ-row's `{τ, x₀}` entries, which is the
`ε`-signature of the row at second order. -/
theorem sqrt10_scalarGram :
    stokesGram ⇑scalarMarkP (mpcFam 2 1 0 0 2 1 .one) scalarXP scalarYP
      = !![0,1,0,0,1; 1,1,0,0,1; 0,0,1,1,0; 0,0,1,0,0; 1,1,0,0,0] := by
  decide +kernel

/-- **The `ε`-difference, isolated**: the two `e = 1` Gram matrices differ in exactly the four
entries of the symmetric `{σ}×{τ,x₀}` block.  Stated as an equation between the *difference* and
the block, so the claim is checkable without reading either matrix. -/
theorem scalarGram_eps_difference :
    stokesGram ⇑scalarMarkP (mpcFam 2 1 1 0 2 1 .one) scalarXP scalarYP
        - stokesGram ⇑scalarMarkP (mpcFam 2 1 0 0 2 1 .one) scalarXP scalarYP
      = !![0,1,1,0,0; 1,0,0,0,0; 1,0,0,0,0; 0,0,0,0,0; 0,0,0,0,0] := by
  rw [sqrtNeg10_scalarGram, sqrt10_scalarGram]
  decide

end ScalarGram

/-! ## §6 The linear copy's Fox row — WMP-c's residual (i)

`mpcProductRowCert` takes the linear copy's row at σ-free offsets (`hlinrow`) as an **input**,
and WMP-c named its closed form as the one `-b`-shaped computation nobody owned: *"the Fox row
of the orbit-norm block `E₂^pc`"*.  This section computes it.

Two structural facts make the assembly finite.  First, **every prefix weight of `R_lin^pc` is a
power of the single procyclic letter `S₂ = σ^{ω₂}`** — that is WMP-c's `ActsAsPow` calculus read
at first order — so the six-factor product rule collapses to four terms, the two commutators and
the two `𝓔`-blocks having trivially-acting values.  Second, the two genuinely `α`- and
`m`-dependent pieces are **geometric**: `D(C₀^k)` and `D(A)` are `𝒢_c^k`-sums of `S₂`-powers
applied to `a(x₂)`, and so is the orbit norm, whose `m` conjugated copies of `z = δ₂δ₂^{σ₂^p}`
contribute `S₂^{−s}·𝒢_{−s}^m` applied to `D(z)`.

Everything is stated in **characteristic two** (`hV₂`), which is the only regime the row is
consumed in — WMP-b's `foxD_mpcHatW_ram` sets the same precedent — and that is what removes every
sign.  The one datum the row cannot name for itself is `η̂`: the value of `D = σ^{η̂}` is a power
of `σ` whose exponent is a *marking-dependent* integer, so it enters as the hypothesis `hη`,
and at the `√−10` instance (`η = 1`) it is `rfl`. -/

section LinRow

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **The `S₂`-geometric operator** `𝒢_c^k = 1 + S₂^c + ⋯ + S₂^{c(k−1)}`, the shape every
`α`- and `m`-dependent entry of this row takes. -/
noncomputable def geomS (c : ℤ) (k : ℕ) (v : V) : V :=
  ∑ i ∈ Finset.range k, ((powOmega2 t.σ) ^ (c * i)) • v

omit [Finite C] [Finite V] in
@[simp] theorem geomS_zero (c : ℤ) (v : V) : geomS t c 0 v = 0 := by rw [geomS]; simp

omit [Finite C] [Finite V] in
theorem geomS_succ (c : ℤ) (k : ℕ) (v : V) :
    geomS t c (k + 1) v = geomS t c k v + ((powOmega2 t.σ) ^ (c * k)) • v := by
  rw [geomS, geomS, Finset.sum_range_succ]

omit [Finite C] [Finite V] in
/-- Splitting a geometric operator: `𝒢_c^{k+l} = 𝒢_c^k + S₂^{ck}·𝒢_c^l`. -/
theorem geomS_add (c : ℤ) (k l : ℕ) (v : V) :
    geomS t c (k + l) v = geomS t c k v + ((powOmega2 t.σ) ^ (c * k)) • geomS t c l v := by
  rw [geomS, geomS, geomS, Finset.sum_range_add, Finset.smul_sum]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [← mul_smul, ← zpow_add]
  congr 1
  push_cast
  ring

omit [Finite C] [Finite V] in
/-- Geometric operators are additive in the vector. -/
theorem geomS_add_vec (c : ℤ) (k : ℕ) (v w : V) :
    geomS t c k (v + w) = geomS t c k v + geomS t c k w := by
  rw [geomS, geomS, geomS, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => smul_add _ _ _

omit [Finite C] [Finite V] in
/-- Geometric operators commute with `S₂`-powers. -/
theorem geomS_smul (c : ℤ) (k : ℕ) (d : ℤ) (v : V) :
    geomS t c k (((powOmega2 t.σ) ^ d) • v) = ((powOmega2 t.σ) ^ d) • geomS t c k v := by
  rw [geomS, geomS, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_smul, ← mul_smul, ← zpow_add, ← zpow_add, add_comm (c * (i : ℤ)) d]

omit [Finite C] [Finite V] in
/-- **The geometric reflection.**  Reading the same `k` powers of `S₂^c` from the other end
turns `𝒢_c^k` into `𝒢_{−c}^k` and shifts the weight by `c(k−1)`.  This one identity is the whole
reason the procyclic row collapses: the `C₀^{2^α}`-block's forward geometric sum and the
orbit-norm's backward one are *the same operator*, so they cancel over `𝔽₂`. -/
theorem smul_geomS_reflect (c : ℤ) (k : ℕ) (d : ℤ) (v : V) :
    ((powOmega2 t.σ) ^ d) • geomS t c k v
      = ((powOmega2 t.σ) ^ (d + c * ((k : ℤ) - 1))) • geomS t (-c) k v := by
  rw [geomS, geomS, Finset.smul_sum, Finset.smul_sum,
    ← Finset.sum_range_reflect
      (fun i => ((powOmega2 t.σ) ^ d) • (((powOmega2 t.σ) ^ (c * i)) • v)) k]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [← mul_smul, ← mul_smul, ← zpow_add, ← zpow_add]
  congr 1
  have hcast : ((k - 1 - i : ℕ) : ℤ) = (k : ℤ) - 1 - (i : ℤ) := by omega
  rw [hcast]
  ring

omit [Finite C] [Finite V] in
/-- `2^α = 2·m` for `α ≥ 1` — the exponent identity that lets the `C₀^{2^α}` block split into
two copies of `𝒢_s^m`. -/
theorem two_pow_eq_two_mul_m {α : ℕ} (hα : 1 ≤ α) : (2 : ℕ) ^ α = 2 * m α := by
  rw [m, ← pow_succ']
  congr 1
  omega

omit [Finite C] [Finite V] in
/-- The `S₂`-inverse-power action in `zpow` normal form. -/
theorem inv_pow_smul (k : ℕ) (v : V) :
    (((powOmega2 t.σ) ^ k)⁻¹) • v = ((powOmega2 t.σ) ^ (-(k : ℤ))) • v := by
  rw [← zpow_natCast, ← zpow_neg]

omit [Finite C] [Finite V] in
/-- The `List.range` form of a `Finset.range` sum — the bridge the orbit-norm expansion needs,
since `Export.orbitNormFactors` is a `List.range` map. -/
theorem sum_map_list_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) : ∀ k : ℕ,
    (((List.range k).map f).sum) = ∑ i ∈ Finset.range k, f i
  | 0 => rfl
  | k + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, sum_map_list_range f k,
        Finset.sum_range_succ]
      simp

omit [Finite C] [Finite V] in
/-- **The orbit-norm expansion in `List.range` normal form.**  `Export.orbitNormFactors`
elaborates its `(j + 1 : ℤ)` binder through a coercion that Lean spells as a monadic bind over
`List.range` — WMP-a's documented friction, one level down — so every consumer that wants to
reindex the product has to normalize first.  This is that normalization. -/
theorem orbitNormFactors_map {Gen : Type*} (z u : PWord Gen) (k : ℕ) :
    Export.orbitNormFactors z u k
      = (List.range k).map (fun j : ℕ => PWord.conj z (PWord.zpow u ((j : ℤ) + 1))) := by
  simp [Export.orbitNormFactors, ← List.map_eq_flatMap, List.map_map, Function.comp_def]

section Factors

variable (hσ : a Generator.sigma = 0)
  (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
  (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)

include hσ hwild hτfpf hTodd

/-- `D(C₀) = a(x₂)`: the `σ₂^s` tail is σ-only, so `C₀ = x₂σ₂^s` has the boundary letter's row
outright.  (Contrast the hat copy, where `Ĉ₀ = σ₂^s` has **no** first-order content at all —
WMP-b's `foxD_c0HatW_of_sigma_free`.) -/
theorem foxD_c0W (s' : ℕ) : foxD ⇑t a E E₂ (c0W h s') = a (coreLetter h 2) := by
  rw [c0W, MCompact.foxD_prodList_pair,
    show foxD ⇑t a E E₂ (PWord.gen (coreLetter h 2)) = a (coreLetter h 2) from rfl,
    foxD_sigma2Pow_of_sigma_free t E E₂ a hσ, smul_zero, add_zero]

/-- `D(C₀^k) = 𝒢_s^k·a(x₂)` — the geometric sum with ratio `S₂^s`, because `C₀` acts as `S₂^s`.
This is the `C₀^{2^α}` factor's whole content, and the only place `α` enters the row. -/
theorem foxD_c0W_zpow (s' k : ℕ) :
    foxD ⇑t a E E₂ (.zpow (c0W h s') (k : ℤ)) = geomS t (s' : ℤ) k (a (coreLetter h 2)) := by
  rw [foxD_zpow_natCast, geomS]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [foxD_c0W t E E₂ a hσ hwild hτfpf hTodd s', ← zpow_natCast _ i,
    (actsAsPow_c0W t E E₂ hwild s').zpow (i : ℤ) (a (coreLetter h 2)),
    show (i : ℤ) * (s' : ℤ) = (s' : ℤ) * (i : ℤ) by ring]

/-- `D(A) = a(x₀) + S₂^{−sm}·𝒢_s^m·a(x₂)` in characteristic two: the `x₀⁻¹` head plus the
`C₀^{−m}` tail read through the geometric sum. -/
theorem foxD_aW (hV₂ : ∀ w : V, w + w = 0) (s' mm : ℕ) :
    foxD ⇑t a E E₂ (aW h s' mm)
      = a (coreLetter h 0)
        + ((powOmega2 t.σ) ^ (-(s' * mm : ℕ) : ℤ)) • geomS t (s' : ℤ) mm (a (coreLetter h 2)) := by
  have hx0 : ⇑t (coreLetter h 0) ∈ trivAct C V := trivAct_coreLetterM t hwild 0
  have htail : foxD ⇑t a E E₂ (.zpow (c0W h s') (-(mm : ℤ)))
      = ((powOmega2 t.σ) ^ (-(s' * mm : ℕ) : ℤ))
          • geomS t (s' : ℤ) mm (a (coreLetter h 2)) := by
    rw [foxD_zpow_neg', foxEval_g, foxD_c0W_zpow t E E₂ a hσ hwild hτfpf hTodd s' mm,
      ← zpow_natCast (PWord.evalFin ⇑t E E₂ (c0W h s')) mm,
      ((actsAsPow_c0W t E E₂ hwild s').zpow (mm : ℤ)).inv
        (geomS t (s' : ℤ) mm (a (coreLetter h 2))),
      Certificates.neg_eq_self hV₂,
      show -((mm : ℤ) * (s' : ℤ)) = (-(s' * mm : ℕ) : ℤ) by push_cast; ring]
  rw [aW, MCompact.foxD_prodList_pair, htail, foxD_inv, PWord.evalFin_inv, PWord.evalFin_gen,
    show foxD ⇑t a E E₂ (PWord.gen (coreLetter h 0)) = a (coreLetter h 0) from rfl]
  simp only [mem_trivAct.mp (inv_mem hx0), Certificates.neg_eq_self hV₂]

/-- `D(B) = a(x₁)`: the `σ₂^p` tail is σ-only, in both emitted spellings. -/
theorem foxD_bW : ∀ pp : ℕ, foxD ⇑t a E E₂ (bW h pp) = a (coreLetter h 1)
  | 0 => rfl
  | q + 1 => by
      rw [show bW h (q + 1) = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (q + 1)] from rfl,
        MCompact.foxD_prodList_pair,
        show foxD ⇑t a E E₂ (PWord.gen (coreLetter h 1)) = a (coreLetter h 1) from rfl]
      have hs : foxD ⇑t a E E₂ (sig2PowW h (q + 1)) = 0 := by
        match q with
        | 0 => exact foxD_sigma2W_of_sigma_free t E E₂ a hσ
        | j + 1 =>
            rw [show sig2PowW h (j + 2) = .zpow sigma2W ((j + 2 : ℕ) : ℤ) from rfl]
            exact foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
      rw [hs, smul_zero, add_zero]

/-- **The orbit-norm base's row**: `D(z) = a(x₂) + S₂^{−p}·a(x₂)` in characteristic two, in both
emitted spellings — the `p = 0` display `δ₂²` (where the two summands coincide) included. -/
theorem foxD_zW (hV₂ : ∀ w : V, w + w = 0) : ∀ pp : ℕ,
    foxD ⇑t a E E₂ (zW h pp)
      = a (coreLetter h 2) + ((powOmega2 t.σ) ^ (-(pp : ℤ))) • a (coreLetter h 2)
  | 0 => by
      have hsum : ∀ i ∈ Finset.range 2,
          PWord.evalFin ⇑t E E₂ (dW h 2) ^ i • foxD ⇑t a E E₂ (dW h 2)
            = -a (coreLetter h 2) := fun i _ => by
        rw [foxD_dW_ram t E E₂ a hwild hτfpf hTodd 2,
          mem_trivAct.mp (pow_mem (trivAct_dW_ram t E E₂ hwild hTodd 2) i)]
      rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl, foxD_zpow_natCast,
        Finset.sum_congr rfl hsum, Finset.sum_const, Finset.card_range, two_nsmul, ← neg_add,
        hV₂, neg_zero, Nat.cast_zero, neg_zero, zpow_zero, one_smul, hV₂]
  | q + 1 => by
      rw [show zW h (q + 1) = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (q + 1))] from rfl,
        MCompact.foxD_prodList_pair, foxD_dW_ram t E E₂ a hwild hτfpf hTodd 2,
        mem_trivAct.mp (trivAct_dW_ram t E E₂ hwild hTodd 2), foxD_conj,
        foxD_dW_ram t E E₂ a hwild hτfpf hTodd 2]
      have hs : foxD ⇑t a E E₂ (sig2PowW h (q + 1)) = 0 := by
        match q with
        | 0 => exact foxD_sigma2W_of_sigma_free t E E₂ a hσ
        | j + 1 =>
            rw [show sig2PowW h (j + 2) = .zpow sigma2W ((j + 2 : ℕ) : ℤ) from rfl]
            exact foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
      rw [hs, smul_zero, add_zero, sub_zero,
        ((actsAsPow_sig2PowW t E E₂ (q + 1)).inv) (-a (coreLetter h 2))]
      simp only [Certificates.neg_eq_self hV₂]

omit hσ hwild hτfpf hTodd in
/-- Powers of a first-order-silent word are first-order silent, at every integer exponent. -/
theorem foxD_zpow_eq_zero {u : PWord (Generator (2 + 2 * h))} (hu : foxD ⇑t a E E₂ u = 0) :
    ∀ k : ℤ, foxD ⇑t a E E₂ (.zpow u k) = 0
  | .ofNat j => by
      rw [show (Int.ofNat j) = ((j : ℕ) : ℤ) from rfl, foxD_zpow_natCast]
      exact Finset.sum_eq_zero fun i _ => by rw [hu, smul_zero]
  | .negSucc j => by
      rw [Int.negSucc_eq, show -((j : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
        foxD_zpow_neg', foxD_zpow_natCast,
        Finset.sum_eq_zero fun i _ => by rw [hu, smul_zero], smul_zero, neg_zero]

omit [Finite C] [Finite V] hσ hwild hτfpf hTodd in
/-- The `σ₂`-tower's value, in closed form. -/
theorem evalFin_sigma2Pow (k : ℤ) :
    PWord.evalFin ⇑t E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) k)
      = (powOmega2 t.σ) ^ k := by
  rw [PWord.evalFin_zpow, MCompact.evalFin_sigma2W]

omit [Finite C] [Finite V] hσ hwild hτfpf hTodd in
/-- **The orbit-norm shift**: the `m` conjugated copies `z^{U}, …, z^{U^m}` sum to
`S₂^c·𝒢_c^m` applied to `D(z)`.  This is what turns the orbit norm — the block WMP-c flagged as
the hard piece — into one geometric operator. -/
theorem sum_orbit_geomS (c : ℤ) (k : ℕ) (v : V) :
    ∑ j ∈ Finset.range k, ((powOmega2 t.σ) ^ (c * ((j : ℤ) + 1))) • v
      = ((powOmega2 t.σ) ^ c) • geomS t c k v := by
  rw [geomS, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_smul, ← zpow_add, show c + c * (i : ℤ) = c * ((i : ℤ) + 1) by ring]

/-- **The `E₂^pc` row — the orbit-norm block in closed form.**

WMP-c named exactly this as the residual: *"the Fox row of the orbit-norm block `E₂^pc`"*.  It
is the head conjugate `δ₂^{σ₂^s}` plus the norm, and the norm is one geometric operator applied
to the base's row:

```
D(E₂^pc) = S₂^{−s}·a(x₂) + S₂^{−sm}·S₂^{−s}·𝒢_{−s}^m·(a(x₂) + S₂^{−p}·a(x₂))
```

in characteristic two.  Note where `ε` lives: the *only* appearance of `p` is the `S₂^{−p}` of
`D(z)`, so at `ε = 0` the base's two summands coincide and the whole block doubles away — the
first-order face of the `ε`-visibility §5 measured at second order. -/
theorem foxD_e2W (hV₂ : ∀ w : V, w + w = 0) (s' mm pp : ℕ) :
    foxD ⇑t a E E₂ (e2W h s' mm pp)
      = ((powOmega2 t.σ) ^ (-(s' : ℤ))) • a (coreLetter h 2)
        + ((powOmega2 t.σ) ^ (-(s' * mm : ℕ) : ℤ)) • (((powOmega2 t.σ) ^ (-(s' : ℤ)))
            • geomS t (-(s' : ℤ)) mm
              (a (coreLetter h 2)
                + ((powOmega2 t.σ) ^ (-(pp : ℤ))) • a (coreLetter h 2))) := by
  have hd2 := foxD_dW_ram t E E₂ a hwild hτfpf hTodd 2
  have ht2 := trivAct_dW_ram t E E₂ hwild hTodd 2
  have hsig : ∀ k : ℤ,
      foxD ⇑t a E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) k) = 0 := fun k =>
    foxD_zpow_eq_zero t E E₂ a (foxD_sigma2W_of_sigma_free t E E₂ a hσ) k
  -- the head conjugate
  have hhead : foxD ⇑t a E E₂ (.conj (dW h 2) (.zpow sigma2W (s' : ℤ)))
      = ((powOmega2 t.σ) ^ (-(s' : ℤ))) • a (coreLetter h 2) := by
    rw [foxD_conj, hd2, hsig, smul_zero, add_zero, sub_zero, evalFin_sigma2Pow, ← zpow_neg,
      smul_neg, Certificates.neg_eq_self hV₂]
  -- every orbit-norm factor
  have hfac : ∀ j : ℕ,
      foxD ⇑t a E E₂ (.conj (zW h pp) (.zpow (.zpow sigma2W (s' : ℤ)) ((j : ℤ) + 1)))
        = ((powOmega2 t.σ) ^ (-(s' : ℤ) * ((j : ℤ) + 1)))
            • (a (coreLetter h 2) + ((powOmega2 t.σ) ^ (-(pp : ℤ))) • a (coreLetter h 2)) := by
    intro j
    rw [foxD_conj, foxD_zW t E E₂ a hσ hwild hτfpf hTodd hV₂ pp,
      foxD_zpow_eq_zero t E E₂ a (hsig (s' : ℤ)), smul_zero, add_zero, sub_zero,
      PWord.evalFin_zpow, evalFin_sigma2Pow, ← zpow_mul, ← zpow_neg,
      show -((s' : ℤ) * ((j : ℤ) + 1)) = -(s' : ℤ) * ((j : ℤ) + 1) by ring]
  -- the norm block
  have hnorm : foxD ⇑t a E E₂
      (PWord.prodList (Export.orbitNormFactors (zW h pp) (.zpow sigma2W (s' : ℤ)) mm))
      = ((powOmega2 t.σ) ^ (-(s' : ℤ))) • geomS t (-(s' : ℤ)) mm
          (a (coreLetter h 2) + ((powOmega2 t.σ) ^ (-(pp : ℤ))) • a (coreLetter h 2)) := by
    rw [foxD_prodList_of_trivial _ _ _ _ _ (fun w hw => by
      rw [orbitNormFactors_map, List.mem_map] at hw
      obtain ⟨j, -, rfl⟩ := hw
      rw [PWord.evalFin_conj]
      exact trivAct_conjR (trivAct_zW t E E₂ hwild hTodd pp) _)]
    rw [orbitNormFactors_map, List.map_map, sum_map_list_range]
    simp only [Function.comp_apply]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.range mm) => hfac j, sum_orbit_geomS]
  rw [e2W, MCompact.foxD_prodList_pair, hhead, PWord.evalFin_conj,
    mem_trivAct.mp (trivAct_conjR ht2 _), foxD_conj, hnorm, hsig, smul_zero, add_zero, sub_zero,
    evalFin_sigma2Pow, ← zpow_neg,
    show -((s' * mm : ℕ) : ℤ) = (-(s' * mm : ℕ) : ℤ) from rfl]

/-- `D(A²) = (1 + S₂^{−sm})·D(A)`, the leading square's row. -/
theorem foxD_aW_sq (s' mm : ℕ) :
    foxD ⇑t a E E₂ (.zpow (aW h s' mm) ((2 : ℕ) : ℤ))
      = foxD ⇑t a E E₂ (aW h s' mm)
        + ((powOmega2 t.σ) ^ (-(s' * mm : ℕ) : ℤ)) • foxD ⇑t a E E₂ (aW h s' mm) := by
  rw [foxD_zpow_natCast, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    pow_zero, one_smul, pow_one, zero_add,
    (actsAsPow_aW t E E₂ hwild s' mm) (foxD ⇑t a E E₂ (aW h s' mm))]

/-- **`D([A,B])`** — the one commutator on this row whose *both* entries act nontrivially
(`A` as `S₂^{−sm}`, `B` as `S₂^{p}`; WMP-b's §4 contrast with the compact row's bare `x₁`).
In characteristic two the four terms of `foxD_comm_general` become a plain sum. -/
theorem foxD_commAB (hV₂ : ∀ w : V, w + w = 0) (s' mm pp : ℕ) :
    foxD ⇑t a E E₂ (.comm (aW h s' mm) (bW h pp))
      = ((powOmega2 t.σ) ^ ((s' * mm : ℕ) : ℤ)) • foxD ⇑t a E E₂ (aW h s' mm)
        + ((powOmega2 t.σ) ^ (((s' * mm : ℕ) : ℤ) - (pp : ℤ)))
            • foxD ⇑t a E E₂ (aW h s' mm)
        + ((powOmega2 t.σ) ^ (((s' * mm : ℕ) : ℤ) - (pp : ℤ))) • a (coreLetter h 1)
        + ((powOmega2 t.σ) ^ (-(pp : ℤ))) • a (coreLetter h 1) := by
  have hA := actsAsPow_aW t E E₂ hwild s' mm
  have hB := actsAsPow_bW t E E₂ hwild pp
  have h1 : ActsAsPow (powOmega2 t.σ) ((s' * mm : ℕ) : ℤ)
      (PWord.evalFin ⇑t E E₂ (aW h s' mm))⁻¹ V :=
    ActsAsPow.congr_exp (by ring) hA.inv
  have h2 : ActsAsPow (powOmega2 t.σ) (((s' * mm : ℕ) : ℤ) - (pp : ℤ))
      ((PWord.evalFin ⇑t E E₂ (aW h s' mm))⁻¹ * (PWord.evalFin ⇑t E E₂ (bW h pp))⁻¹) V :=
    ActsAsPow.congr_exp (by ring) (h1.mul hB.inv)
  have h3 : ActsAsPow (powOmega2 t.σ) (-(pp : ℤ))
      ((PWord.evalFin ⇑t E E₂ (aW h s' mm))⁻¹ * (PWord.evalFin ⇑t E E₂ (bW h pp))⁻¹
        * PWord.evalFin ⇑t E E₂ (aW h s' mm)) V :=
    ActsAsPow.congr_exp (by push_cast; ring) (h2.mul hA)
  rw [foxD_comm_general, foxD_bW t E E₂ a hσ hwild hτfpf hTodd pp, h1 _, h2 _, h2 _, h3 _]
  simp only [sub_eq_add_neg, Certificates.neg_eq_self hV₂]
  abel

/-- **`D([C₀,D])`** — the `η̂` commutator.  `D = σ^{η̂}` has no first-order content of its own
(WMP-b's `foxD_etaDisplay_of_sigma_free`), so only the `C₀`-entry survives, weighted once by
`S₂^{−s}` and once by `S₂^{−s}σ^{−n}`.  The exponent `n` is the marking-level integer power that
`D` acts by; it cannot be read off the display, which is why it enters as `hη`. -/
theorem foxD_commC0D (hV₂ : ∀ w : V, w + w = 0) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow t.σ nη
      (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h))) V) (s' : ℕ) :
    foxD ⇑t a E E₂ (.comm (c0W h s') (η.toPWord (n := 2 + 2 * h)))
      = ((powOmega2 t.σ) ^ (-(s' : ℤ))) • a (coreLetter h 2)
        + ((powOmega2 t.σ) ^ (-(s' : ℤ))) • ((t.σ ^ (-nη)) • a (coreLetter h 2)) := by
  have hC : ActsAsPow (powOmega2 t.σ) (-(s' : ℤ))
      (PWord.evalFin ⇑t E E₂ (c0W h s'))⁻¹ V :=
    ActsAsPow.congr_exp rfl (actsAsPow_c0W t E E₂ hwild s').inv
  rw [foxD_comm_general, foxD_c0W t E E₂ a hσ hwild hτfpf hTodd s',
    foxD_etaDisplay_of_sigma_free t E E₂ a hσ η, smul_zero, smul_zero, hC _, mul_smul, hC _,
    hη.inv (a (coreLetter h 2))]
  simp only [sub_eq_add_neg, Certificates.neg_eq_self hV₂, neg_zero, add_zero, zero_add]

/-! ### The assembled row — the headline

**Every prefix weight of `R_lin^pc` is a power of the single procyclic letter `S₂`.**  Four of
the six factors have trivially-acting values — the two commutators by WMP-c's `ActsAsPow`
commutator clause, the two `𝓔`-blocks outright — so only `A²` and `C₀^{2^α}` weight anything at
all, and packet Prop. 9.2's balance `s·2^α = 2·sm` makes *their product* the identity.  The
six-factor product rule therefore collapses to five terms with exactly one surviving weight. -/

/-- **The linear copy's Fox row at σ-free offsets, at general `(α, r, p, η, h)`** — WMP-c's
residual (i), assembled.

The five summands are this section's factor rows (`foxD_aW_sq`, `foxD_commAB`, `foxD_c0W_zpow`,
`foxD_commC0D`, `foxD_e2W`) together with WMP-b's `foxD_e01W_ram`, and the single surviving
prefix `S₂^{−2sm}` is what Prop. 9.2's balance leaves behind: it weights the `[A,B]`-and-
`C₀^{2^α}` middle block and nothing else, because `S₂^{−2sm}·S₂^{s·2^α} = 1`. -/
theorem foxD_mpcLinW_ram {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow t.σ nη (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h))) V) :
    foxD ⇑t a E E₂ (mpcLinW α r pp η h)
      = foxD ⇑t a E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ))
        + ((powOmega2 t.σ) ^ (-(2 * (s r * m α) : ℕ) : ℤ))
            • (foxD ⇑t a E E₂ (.comm (aW h (s r) (m α)) (bW h pp))
                + foxD ⇑t a E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ)))
        + foxD ⇑t a E E₂ (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)))
        + foxD ⇑t a E E₂ (e01W h (pp + s r * m α) (s r * m α))
        + foxD ⇑t a E E₂ (e2W h (s r) (m α) pp) := by
  have hU : powOmega2 t.σ = t.σ ^ ((omega2Exp (orderOf t.σ) : ℕ) : ℤ) := powOmega2_sigma_eq_zpow t
  have hAB : PWord.evalFin ⇑t E E₂ (.comm (aW h (s r) (m α)) (bW h pp)) ∈ trivAct C V :=
    (actsAsPow_aW t E E₂ hwild (s r) (m α)).trivAct_commR (actsAsPow_bW t E E₂ hwild pp)
  have hCD : PWord.evalFin ⇑t E E₂ (.comm (c0W h (s r)) (η.toPWord (n := 2 + 2 * h)))
      ∈ trivAct C V :=
    ActsAsPow.trivAct_commR (U := t.σ)
      ((actsAsPow_c0W t E E₂ hwild (s r)).base_zpow hU) hη
  have h01 := trivAct_e01W t E E₂ hwild hTodd (pp + s r * m α) (s r * m α)
  have hsq : ActsAsPow (powOmega2 t.σ) (-(2 * (s r * m α) : ℕ) : ℤ)
      (PWord.evalFin ⇑t E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ))) V := by
    rw [PWord.evalFin_zpow]
    exact ActsAsPow.congr_exp (by push_cast; ring)
      ((actsAsPow_aW t E E₂ hwild (s r) (m α)).zpow ((2 : ℕ) : ℤ))
  have hc0 : ActsAsPow (powOmega2 t.σ) (((2 ^ α : ℕ) : ℤ) * (s r : ℤ))
      (PWord.evalFin ⇑t E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ))) V := by
    rw [PWord.evalFin_zpow]
    exact (actsAsPow_c0W t E E₂ hwild (s r)).zpow ((2 ^ α : ℕ) : ℤ)
  have hbal : PWord.evalFin ⇑t E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ))
      * PWord.evalFin ⇑t E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ)) ∈ trivAct C V := by
    refine ActsAsPow.trivial_of_zero (U := powOmega2 t.σ) (ActsAsPow.congr_exp ?_ (hsq.mul hc0))
    have hb := congrArg (fun k : ℕ => (k : ℤ)) (s_mul_two_pow hα r)
    push_cast at hb ⊢
    linarith
  have key : ∀ X₂ X₃ X₄ X₅ X₆ : V,
      PWord.evalFin ⇑t E E₂ (.zpow (aW h (s r) (m α)) ((2 : ℕ) : ℤ))
          • (X₂ + (X₃ + PWord.evalFin ⇑t E E₂ (.zpow (c0W h (s r)) ((2 ^ α : ℕ) : ℤ))
              • (X₄ + (X₅ + X₆))))
        = ((powOmega2 t.σ) ^ (-(2 * (s r * m α) : ℕ) : ℤ)) • (X₂ + X₃) + X₄ + X₅ + X₆ := by
    intro X₂ X₃ X₄ X₅ X₆
    rw [smul_add, smul_add, ← mul_smul, mem_trivAct.mp hbal, hsq _, hsq _, smul_add]
    abel
  rw [mpcLinW, linFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_one, PWord.evalFin_mul,
    PWord.evalFin_one, smul_zero, add_zero, mul_one]
  rw [mem_trivAct.mp hAB, mem_trivAct.mp hCD, mem_trivAct.mp h01, key]
  abel

/-! ### The collapse

Substituting the six factor rows into `foxD_mpcLinW_ram` and reading the result column by column
gives **nineteen terms in ten weights, and nine of the ten weights occur an even number of
times.**  Three cancellations do the work, and each is a structural statement:

* the `x₀`- and `x₁`-columns of the head block `A²[A,B]` are reproduced *exactly* by `E₀₁^pc` —
  the freeze's "`E₀₁^pc` is first-order redundant", now visible as a column-level identity rather
  than as the shadow-reproduction statement of WMP-b's `foxD_e01_reproduced_by_shadow`;
* the `C₀^{2^α}` block splits as `𝒢_s^m + S₂^{sm}𝒢_s^m` (because `2^α = 2m`), which absorbs the
  head block's remaining `x₂`-content;
* what is left of `C₀^{2^α}` is the **reflection** of the orbit norm — the same `m` powers of
  `S₂^s` read from the other end — so `E₂^pc` cancels it, and its head `S₂^{−s}a(x₂)` cancels
  the `[C₀,D]` block's first term.

What survives is one entry, in the `x₂`-column, and it comes from the `η̂` commutator. -/

/-- **The linear copy's Fox row is a single entry.**

```
D(R_lin^pc)(a) = S₂^{−s}·σ^{−n}·a(x₂)
```

at σ-free offsets, at the ramified reading, in characteristic two, at **every** `(α ≥ 1, r, p, η,
h)`.  This is WMP-c's residual (i) discharged, and it is sharper than the transport shape needed
it to be: the row has no `σ`-, `τ`-, `x₀`- or `x₁`-entry at all.

⚠ Consistency check against the siblings: `MCompact.mCompactWildRow` read at the **ramified**
interpretation (`P ↦ 0`) is `(0, 0, 0, 0, S⁻¹)` — also supported on `x₂` alone, also a single
`σ`-power.  The procyclic row is the same shape with `S⁻¹` replaced by `S₂^{−s}σ^{−n}`, which is
exactly the two data the procyclic display adds (`C₀`'s `σ₂^s` tail and `D = σ^{η̂}`). -/
theorem foxD_mpcLinW_x2 {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow t.σ nη (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcLinW α r pp η h)
      = ((powOmega2 t.σ) ^ (-(s r : ℤ))) • ((t.σ ^ (-nη)) • a (coreLetter h 2)) := by
  rw [foxD_mpcLinW_ram t E E₂ a hσ hwild hτfpf hTodd hα r pp hη, smul_add,
    foxD_aW_sq t E E₂ a hσ hwild hτfpf hTodd,
    foxD_aW t E E₂ a hσ hwild hτfpf hTodd hV₂,
    foxD_commAB t E E₂ a hσ hwild hτfpf hTodd hV₂,
    foxD_aW t E E₂ a hσ hwild hτfpf hTodd hV₂,
    foxD_c0W_zpow t E E₂ a hσ hwild hτfpf hTodd,
    foxD_commC0D t E E₂ a hσ hwild hτfpf hTodd hV₂ hη,
    foxD_e01W_ram t E E₂ a hσ hwild hτfpf hTodd,
    foxD_e2W t E E₂ a hσ hwild hτfpf hTodd hV₂,
    two_pow_eq_two_mul_m hα, show 2 * m α = m α + m α from by ring, geomS_add,
    geomS_add_vec, geomS_smul]
  simp only [smul_add, mul_smul, inv_pow_smul, Certificates.neg_eq_self hV₂, sub_eq_add_neg]
  simp only [← mul_smul, ← zpow_add]
  push_cast
  ring_nf
  -- the two reflections: what is left of `C₀^{2^α}` *is* the orbit norm, read backwards
  have href1 : ((powOmega2 t.σ) ^ (-((s r : ℤ) * (m α : ℤ) * 2)))
        • geomS t (s r : ℤ) (m α) (a (coreLetter h 2))
      = ((powOmega2 t.σ) ^ (-(s r : ℤ) - (s r : ℤ) * (m α : ℤ)))
          • geomS t (-(s r : ℤ)) (m α) (a (coreLetter h 2)) := by
    rw [smul_geomS_reflect]
    congr 2
    ring
  have href2 : ((powOmega2 t.σ) ^ (-((s r : ℤ) * (m α : ℤ) * 2) - (pp : ℤ)))
        • geomS t (s r : ℤ) (m α) (a (coreLetter h 2))
      = ((powOmega2 t.σ) ^ (-(s r : ℤ) - (s r : ℤ) * (m α : ℤ) - (pp : ℤ)))
          • geomS t (-(s r : ℤ)) (m α) (a (coreLetter h 2)) := by
    rw [smul_geomS_reflect]
    congr 2
    ring
  have hev2 : ∀ x : V, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul, hV₂]
  have hev4 : ∀ x : V, (4 : ℕ) • x = 0 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, mul_nsmul, hev2]
  have hevz2 : ∀ x : V, (2 : ℤ) • x = 0 := fun x => by rw [two_zsmul, hV₂]
  have hevz4 : ∀ x : V, (4 : ℤ) • x = 0 := fun x => by
    rw [show (4 : ℤ) = 2 * 2 from rfl, mul_zsmul, hevz2]
  rw [href1, href2]
  abel_nf
  simp [hev2, hev4, hevz2, hevz4]

end Factors

end LinRow

/-! ## §7 The formal row, and merge gate 9

`mpcProductRowCert`'s last open input was `hlinrow`.  §6 computed it, so the formal row is now
one entry of `TameSym` data and the `√−10` certificate is unconditional (in the ramified class:
`hwild`, `hτfpf`, `hTodd`, `hV₂` — the same four hypotheses every sibling row carries).

⚠ The row's σ-entry is `.zero`, which is exactly `mpcProductRowCert`'s `hσzero`: WMP-c observed
that both sibling frozen rows have that shape and that neither copy of *this* row has an
available σ-entry; §6 shows the linear copy's σ-entry is not merely unavailable but **zero**, so
the transport's hypothesis is discharged rather than assumed. -/

section FormalRow

/-- **The procyclic-`M` linear row**, as pure `FoxCoeff` data over WW2's standard atom alphabet:

```
(σ, τ, x₀, x₁, x₂) = (0, 0, 0, 0, S₂^{−s}·σ^{−n})
```

— one entry, in the `x₂`-column, at every `(α ≥ 1, r, p, η, h)`.  `n` is the integer power the
`η̂`-letter acts by; the row is parametrized by it, exactly as the compact rows are parametrized
by the projector assignment. -/
def mpcLinRow (r : ℕ) (nη : ℤ) (h : ℕ) :
    FoxRowNormalForm (Generator (2 + 2 * h)) (TameSym (2 + 2 * h)) :=
  ⟨fun g => match g with
    | .sigma => .zero
    | .tau => .zero
    | .wild i =>
        if (i : ℕ) = 2 then
          .comp (.atom (.sigma2 (-(s r : ℤ)))) (.atom (.gen Generator.sigma (-nη)))
        else .zero⟩

variable {h : ℕ} {r : ℕ} {nη : ℤ}

@[simp] theorem mpcLinRow_sigma : (mpcLinRow r nη h).row .sigma = .zero := rfl

@[simp] theorem mpcLinRow_tau : (mpcLinRow r nη h).row .tau = .zero := rfl

@[simp] theorem mpcLinRow_x2 :
    (mpcLinRow r nη h).row (coreLetter h 2)
      = .comp (.atom (.sigma2 (-(s r : ℤ)))) (.atom (.gen Generator.sigma (-nη))) := rfl

/-- **The row's denotation** at the standard interpretation: `a ↦ S₂^{−s}·σ^{−n}·a(x₂)`.  Note
that the projector assignment `π` is irrelevant — this row uses no `P` atom, which is the
formal-data face of "the procyclic linear row is a *ramified* row". -/
theorem mpcLinRow_toHom {C : Type*} [Group C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (π : AddMonoid.End V)
    (a : Generator (2 + 2 * h) → V) :
    (mpcLinRow r nη h).toHom (TameSym.toEnd t π) a
      = ((powOmega2 t.σ) ^ (-(s r : ℤ))) • ((t.σ ^ (-nη)) • a (coreLetter h 2)) := by
  rw [FoxRowNormalForm.toHom_apply,
    sum_generator_wild _ (⟨2, by omega⟩ : Fin (2 + 2 * h + 1)) rfl rfl (fun j hj => by
      show ((if (j : ℕ) = 2 then
          FoxCoeff.comp (.atom (.sigma2 (-(s r : ℤ)))) (.atom (.gen Generator.sigma (-nη)))
        else .zero)).eval (TameSym.toEnd t π) (a (.wild j)) = 0
      rw [if_neg fun hc => hj (Fin.ext hc)]
      rfl)]
  rfl

end FormalRow

/-! ### Merge gate 9 — the `ℚ₂(√−10)` procyclic row -/

section Gate9

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking 2 C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- The `η = 1` display acts as the first power of `σ` — the `hη` datum at the packet's
`√−10` instance, where it is definitional rather than a hypothesis. -/
theorem actsAsPow_etaOne :
    ActsAsPow t.σ 1 (PWord.evalFin ⇑t E E₂ (EtaDisplay.one.toPWord (n := 2 + 2 * 0))) V := by
  intro v
  rw [zpow_one]
  rfl

/-- **`hlinrow` at the `√−10` instance** — the input `sqrtNeg10ProductRowCert` was waiting on. -/
theorem sqrtNeg10_hlinrow (π : AddMonoid.End V) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin 3) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (a : Generator 2 → V) (hσ : a Generator.sigma = 0) :
    foxD ⇑t a E E₂ (mpcLinW 2 1 1 .one 0)
      = (mpcLinRow 1 1 0).toHom (TameSym.toEnd t π) a := by
  rw [mpcLinRow_toHom (h := 0) (r := 1) (nη := 1) t π a,
    foxD_mpcLinW_x2 (h := 0) t E E₂ a hσ hwild hτfpf hTodd (α := 2) (by norm_num) 1 1
      (actsAsPow_etaOne t E E₂) hV₂]

/-- **Merge gate 9, closed.**

WMP-c built `sqrtNeg10ProductRowCert` with `hlinrow` as its one remaining input and named that
input as what AS3 still owed.  Here it is discharged, so the `√−10` procyclic row's WW2
certificate is a **term**, not a transport waiting on a hypothesis: at every finite ramified
elementary module the pair `R_lin^pc·R̂^pc` has the normal form `mpcLinRow 1 1 0`, whose only
entry is `S₂^{−2}σ^{−1}` in the `x₂`-column.

The remaining hypotheses are the ramified class conditions (`hwild`, `hτfpf`, `hTodd`, `hV₂`),
which every sibling row carries and which AS1 supplies per module; nothing about the row itself
is left open. -/
noncomputable def sqrtNeg10ProductCert (π : AddMonoid.End V) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin 3) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    FoxRowCertificate (TameSym.toEnd t π)
      (foxDHom (A := V) ⇑t E E₂ sqrtNeg10ProductW) :=
  sqrtNeg10ProductRowCert t E E₂ (TameSym.toEnd t π) hV₂ hwild hτfpf hTodd
    (mpcLinRow 1 1 0) rfl (sqrtNeg10_hlinrow t E E₂ π hV₂ hwild hτfpf hTodd)

/-- The gate-9 certificate's target is the single-entry row — stated so that a consumer can read
the normal form off the certificate without unfolding the construction. -/
theorem sqrtNeg10ProductCert_target (π : AddMonoid.End V) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin 3) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) :
    (sqrtNeg10ProductCert t E E₂ π hV₂ hwild hτfpf hTodd).target = mpcLinRow 1 1 0 ∧
      (sqrtNeg10ProductCert t E E₂ π hV₂ hwild hτfpf hTodd).colOps = [] :=
  ⟨rfl, rfl⟩

end Gate9

end GQ2.Dyadic.Certificates.MProcyclic
