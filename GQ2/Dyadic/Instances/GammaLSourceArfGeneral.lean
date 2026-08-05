/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.RamifiedCountPow
import GQ2.Dyadic.Instances.GammaLDeterminantResidue

/-!
# The ramified source-Arf datum of the L row, at a general residue cardinality

`GQ2/Dyadic/Instances/GammaLDeterminantResidue.lean` reduces every analytic leaf of the improved
`L_sq` row to one arithmetic input, `LRamifiedSourceArfSupply`: the descended continuous source
form has Arf invariant zero.  At `q = 2` that input is a **theorem**, through the tame action
(`lRamifiedPhasePackage_of_action_pointwise`).  This file carries that route to a general
residue cardinality, and records exactly how far it goes.

## Result

`lRamifiedSourceArfData_of_headAction` builds the datum from action-level hypotheses on the head
quotient, for

  `q = 2 ^ F` with `F` **odd**  (`q = 2, 8, 32, 128, …`),

and `wordPhaseResidueK_ramified_lSq_of_action` feeds it into the existing determinant residue, so
that the ramified word phase of the L row costs nothing beyond the ramification hypothesis
`hram` that its consumer already carries.

## The Wall-operator mismatch, resolved

The `q = 2` package runs at `U = powOmega2 (c σ)` while the head-mark route delivers
`U = (powOmega2 (π σ))⁻¹`.  No Arf comparison is needed: the two Wall doublings are the *same
function*.  For a `q`-preserving `g`,

  `polar q x (g⁻¹ • x) = polar q (g • x) (g • g⁻¹ • x) = polar q (g • x) x = polar q x (g • x)`,

so `qDouble q (g⁻¹ • ·) = qDouble q (g • ·)` on the nose (`qDouble_smul_inv_eq`), hence also
`lSqWallHandlePhase q U⁻¹ h = lSqWallHandlePhase q U h`.  This is the identity anticipated by the
parenthetical in `GQ2.QuadraticFp2.qDouble`'s docstring.

## Two refutations (see `docs`-free notes below)

**(1) General even `q` is false; `q` must be a power of two.**  The isotype-stability engine is
the char-2 polynomial Frobenius `P(X^{2^j}) = P(X)^{2^j}`, so `RamifiedPack`'s single-isotype
theorem needs every conjugate of `t` to be a `2`-power power of `t`.  For `q ≡ 3 (mod 7)` and
`q` even — take `q = 10` — the group `C = C₇ ⋊ C₆` with `s⁻¹ t s = t³` acts simply and faithfully
on `V = 𝔽₂[C₇]/(trivial) ≅ 𝔽₈ ⊕ 𝔽₈` of dimension `6`, and `s` **swaps** the two `⟨t⟩`-isotypes
`(X³+X+1)` and `(X³+X²+1)`: `s` sends the isotype of `α` to that of `α^{3⁻¹} = α⁵`, and `α⁵` is
not a Frobenius conjugate of `α`.  So `V` is not `⟨t⟩`-isotypic and
`RamifiedPack.exists_single_isotype` has no general-even-`q` form.

**(2) Even among powers of two, `F` must be odd; `q = 4` is a genuine counterexample to the
ramified Arf-zero statement itself.**  Take `q = 4`, `C = D₅ = ⟨s, t⟩` with `t⁵ = s² = 1` and
`s⁻¹ t s = t⁴`, `V = 𝔽₁₆` with `t` acting as multiplication by a primitive fifth root of unity
`ζ` and `s` acting as `x ↦ x⁴ = Frob²`.  Then `V` is simple, faithful and ramified, and
`q̄(x) = Tr_{𝔽₁₆/𝔽₂}(c x⁵)` with `c ∉ 𝔽₄` is a nonsingular invariant quadratic form.  Here
`m = 2`, `s_V = 1`, `deg P = 4 = 2² · 1` so `a = 2`, `r = 1`, and:

* `Arf(q̄) = 1 = s_V mod 2`   (eq. (87) is `q`-free and still holds);
* `U = powOmega2 s = s = Frob²`, so `V^U = 𝔽₄` has `4` elements, **not** `2^{r·s_V} = 2`;
* `rank(1 + U) = 4 − 2 = 2 ≡ 0 ≢ s_V`, so Wall gives `Arf(q̄_U) = Arf(q̄) + 2 = 1 ≠ 0`.

The general count is `#V^U = 2^{gcd(deg P, F·ω)·s_V}`, whose exponent is odd exactly when `F` is
odd; that is the whole of the parity condition.  So the ramified branch of the L determinant is
**sign-flipped** at `q = 4`, and `LRamifiedSourceArfSupply` cannot hold for all even `q`.

**(3) A statement-shape caveat.**  `LRamifiedSourceArfSupply` as spelled in
`GammaLDeterminantResidue.lean` quantifies over *every* block, level and boundary lift, with no
ramification hypothesis, while its only consumer `wordPhaseResidueK_ramified_lSq` supplies one
(`hram`).  In an unramified block the descended source form has `Arf = 1` (the negative Gauss
sign of `prop_6_9_unramified`), so the literal supply is not provable — from any route.  The
`hram`-conditioned form `LRamifiedSourceArfSupplyRam` below is what the determinant residue
actually needs, and `determinantWordPhaseSupply_lSq_ram` shows it suffices.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes
open GQ2.Dyadic.Count
open GQ2.QuadraticFp2
open GQ2.Dyadic.TameSpec

local instance finiteSemiProdSourceArf {C V : Type} [Group C] [AddCommGroup V]
    [DistribMulAction C V] [Finite V] [Finite C] :
    Finite (SectionSix.SemiProd C V) := inferInstanceAs (Finite (V × C))

/-! ## The Wall-operator bridge

`qDouble` by an isometry and by its inverse are the *same function*. -/

section WallBridge

variable {V : Type*} [AddCommGroup V] {C : Type*} [Group C] [DistribMulAction C V]

/-- An isometry preserves the polar form. -/
theorem polar_smul_smul (q : V → ZMod 2) {g : C} (hg : ∀ v : V, q (g • v) = q v) (a b : V) :
    polar q (g • a) (g • b) = polar q a b := by
  unfold polar
  rw [← smul_add, hg, hg, hg]

/-- **The Wall-operator bridge**: for an isometry `g`, the Wall doubling by `g⁻¹` and by `g`
agree pointwise.  (The parenthetical in `GQ2.QuadraticFp2.qDouble`'s docstring, proved.) -/
theorem qDouble_smul_inv_eq (q : V → ZMod 2) {g : C} (hg : ∀ v : V, q (g • v) = q v) :
    qDouble q (fun v => g⁻¹ • v) = qDouble q (fun v => g • v) := by
  funext x
  show q x + polar q x (g⁻¹ • x) = q x + polar q x (g • x)
  congr 1
  calc polar q x (g⁻¹ • x) = polar q (g • x) (g • (g⁻¹ • x)) :=
        (polar_smul_smul q hg x (g⁻¹ • x)).symm
    _ = polar q (g • x) x := by rw [smul_inv_smul]
    _ = polar q x (g • x) := polar_comm q _ _

/-- The bridge, transported to the evaluated word phase. -/
theorem lSqWallHandlePhase_smul_inv_eq {V : Type} [AddCommGroup V] {C : Type} [Group C]
    [DistribMulAction C V] (q : V → ZMod 2) {g : C} (hg : ∀ v : V, q (g • v) = q v)
    (Uinv U : V ≃+ V) (hUinv : ⇑Uinv = fun v => g⁻¹ • v) (hU : ⇑U = fun v => g • v) (h : ℕ) :
    lSqWallHandlePhase q Uinv h = lSqWallHandlePhase q U h := by
  funext p
  show qDouble q Uinv p.1 + _ = qDouble q U p.1 + _
  congr 1
  rw [hUinv, hU]
  exact congrFun (qDouble_smul_inv_eq q hg) p.1

end WallBridge

/-! ## The action-level ramified Arf-zero at `q = 2 ^ F`, `F` odd -/

section Action

/-- **The ramified Wall head has Arf invariant zero** at the general two-power tame relation
`s⁻¹ t s = t ^ 2 ^ F` with `F` odd.  The general-`q` twin of
`lSqWallHandlePhase_ramified_of_action`, with the marking `c : T_tame ↠ C` replaced by the pair
of elements it names. -/
theorem arf_qDouble_ramified_of_action_pow
    {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (s t : C) {F : ℕ} (hFodd : Odd F)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2 ^ F)
    (hsimple : ∀ W : AddSubgroup V,
      (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    arf (qDouble q (fun v => powOmega2 s • v)) = 0 := by
  letI : Fintype V := Fintype.ofFinite V
  have hzero := RamifiedPow.zeroCount_qDouble_ramified_of_action_pow s t hFodd hgen hrel
    hsimple hram q hq hns hinv m hm hcard
  exact arf_eq_zero_of_zeroCount_add _ hm (by rwa [← Nat.card_eq_fintype_card]) hzero

end Action

/-! ## The source-Arf datum from head-level action data -/

set_option maxHeartbeats 2400000 in
/-- **The ramified source-Arf datum is a theorem at `q = 2 ^ F`, `F` odd.**

Every hypothesis is either an already-available head fact (`G`, the factor-set comparison
`base/π/hpi/hf/hmbase`) or the tame action data that the block frame supplies
(`hgen`/`hrel`/`hsimpleC`/`hramC`).  The output is exactly the binder that
`GQ2.Dyadic.LSquare.lSqRamifiedPhaseModel_of_headData` — and hence
`wordPhaseResidueK_ramified_lSq` — consumes.

Structure of the proof: the head normal form gives the pointwise identity
`QZeroBar = lSqWallHandlePhase q̄ U h ∘ e` with `U = (powOmega2 s)⁻¹`; the Wall-operator bridge
turns its head into `qDouble q̄ (powOmega2 s • ·)`, whose Arf invariant the general-`q` ramified
count kills; the hyperbolic handles have positive Gauss factor, so the whole source form has
positive Gauss sum, i.e. Arf zero. -/
def lRamifiedSourceArfData_of_headAction
    {h q : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom ((gamma h q : Type)) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [IsTopologicalAddGroup DD.Vmod]
    [DiscreteTopology DD.Vmod] [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [DistribMulAction ((gamma h q : Type)) DD.Vmod]
    [ContinuousSMul ((gamma h q : Type)) DD.Vmod]
    {Cbar : Type} [Group Cbar] [Finite Cbar] [DistribMulAction Cbar DD.Vmod]
    (base : FactorSet Cbar DD.Vmod) (hbase : IsEquivariantFactorSet DD.qbar base)
    (π : DD.C0 →* Cbar) (hpi : ∀ (cc : DD.C0) (v : DD.Vmod), cc • v = π cc • v)
    (hf : ∀ a b : DD.Vmod, DD.dat.f a b = base.f a b)
    (hmbase : ∀ (cc : DD.C0) (v : DD.Vmod), DD.dat.m cc v = base.m (π cc) v)
    (hcompat : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
      g • v = rho0 DD rho g • v)
    (hA2 : ∀ v : DD.Vmod, v + v = 0)
    (hqe : Even q) (m : ℕ)
    (hcard : Nat.card DD.Vmod = 2 ^ (2 * m))
    (G : LRamifiedHeadData (DD := DD) rho π)
    (tC : Cbar) {F : ℕ} (hFodd : Odd F)
    (hgen : Subgroup.closure
      ({π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)), tC} : Set Cbar) = ⊤)
    (hrel : (π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)))⁻¹ * tC *
      π (rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)) = tC ^ 2 ^ F)
    (hsimpleC : ∀ W : AddSubgroup DD.Vmod,
      (∀ (g : Cbar), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hramC : ∃ v : DD.Vmod, tC • v ≠ v) :
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    LRamifiedSourceArfData rho (scalarActionZmodTwo_triv _) hcompat := by
  letI : Fintype DD.Vmod := Fintype.ofFinite DD.Vmod
  letI : Module (ZMod 2) DD.Vmod :=
    AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA2 v)
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  let N := 4 * Monoid.exponent L
  let c0 := rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) .sigma)
  let s := π c0
  let U : DD.Vmod ≃+ DD.Vmod :=
    smulAddEquiv (V := DD.Vmod) ((s ^ (omega2Exp N : ℤ))⁻¹)
  have hwildAct : ∀ (i : Fin (2 * h + 1 + 1)) (v : DD.Vmod),
      rho0 DD rho (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) • v = v := by
    intro i v
    rw [hpi, G.wild_head i, one_smul]
  let e : H1 (gamma h q : Type) DD.Vmod ≃
      DD.Vmod × (Fin h → DD.Vmod × DD.Vmod) :=
    lSqRamifiedActionSourceH1Equiv rho hcompat hwildAct
      G.tau_fixedPointFree G.tau_oddPart_fixed
  have hinvC : ∀ (g : Cbar) (v : DD.Vmod), DD.qbar (g • v) = DD.qbar v :=
    fun g v => factorSet_q_invariant base hbase hA2 g v
  have hUq : ∀ v, DD.qbar (U v) = DD.qbar v := by
    intro v
    change DD.qbar (((s ^ (omega2Exp N : ℤ))⁻¹) • v) = DD.qbar v
    exact hinvC _ v
  have hc0Exp : c0 ^ Monoid.exponent L = 1 := by
    let p : L := (0, c0)
    have hp : p ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one p
    calc
      c0 ^ Monoid.exponent L = sdSnd (p ^ Monoid.exponent L) :=
        (map_pow sdSnd p _).symm
      _ = 1 := by rw [hp]; exact map_one sdSnd
  have hsExp : s ^ Monoid.exponent L = 1 := by
    change π c0 ^ Monoid.exponent L = 1
    rw [← map_pow, hc0Exp, map_one]
  have hsN : s ^ N = 1 := by
    rw [show N = Monoid.exponent L * 4 by simp [N, Nat.mul_comm], pow_mul, hsExp, one_pow]
  have hord : orderOf s ∣ N := orderOf_dvd_of_pow_eq_one hsN
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hresolved : s ^ omega2Exp N = powOmega2 s := powOmega2_pow_eq s hord hN
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := by
    refine ⟨(orderOf s).factorization 2, ?_⟩
    have hp : powOmega2 s ^ 2 ^ (orderOf s).factorization 2 = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_powOmega2_dvd_two_pow s)
    have hinv : (s ^ omega2Exp N)⁻¹ ^ 2 ^ (orderOf s).factorization 2 = 1 := by
      rw [hresolved, inv_pow, hp, inv_one]
    funext v
    dsimp [U]
    show (((s ^ (omega2Exp N : ℤ))⁻¹ • ·)^[2 ^ (orderOf s).factorization 2]) v = v
    rw [zpow_natCast, smul_iterate_apply, hinv, one_smul]
  have hphase : LRamifiedPointwisePhaseIdentity
      (scalarActionZmodTwo_triv ((gamma h q : Type))) hcompat DD.qbar U h e :=
    lRamifiedPointwisePhaseIdentity_of_headNormalForm rho DD.hdat base hbase π hpi hf hmbase
      hqe hcompat G.wild_head hwildAct G.tau_fixedPointFree G.tau_oddPart_fixed
  -- `m ≥ 1`: a one-point module cannot be ramified
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with hm0 | hpos
    · exfalso
      obtain ⟨v, hv⟩ := hramC
      have hc1 : Nat.card DD.Vmod = 1 := by rw [hcard, hm0]; norm_num
      haveI : Subsingleton DD.Vmod := (Nat.card_eq_one_iff_unique.mp hc1).1
      exact hv (Subsingleton.elim _ _)
    · exact hpos
  -- the Wall-operator bridge: `U = (powOmega2 s)⁻¹` doubles like `powOmega2 s`
  have hUfun : ⇑U = fun v : DD.Vmod => (powOmega2 s)⁻¹ • v := by
    funext v
    show ((s ^ (omega2Exp N : ℤ))⁻¹) • v = (powOmega2 s)⁻¹ • v
    rw [zpow_natCast, hresolved]
  have harf : arf (qDouble DD.qbar ⇑U) = 0 := by
    rw [hUfun, qDouble_smul_inv_eq DD.qbar (g := powOmega2 s) (fun v => hinvC _ v)]
    exact arf_qDouble_ramified_of_action_pow s tC hFodd hgen hrel hsimpleC hramC
      DD.qbar DD.hquad DD.hns hinvC m hm1 hcard
  -- the source form and its Gauss sum
  have hgauss : QuadraticFp2.gaussSum (lSqWallHandlePhase DD.qbar U h) =
      (standardNumerics (2 * h + 1)).gaussRam m :=
    lSqWallHandlePhase_gaussSum_standardRam DD.hquad DD.hns hA2
      (by rwa [Nat.card_eq_fintype_card] at hcard) U hUq hU2 harf h
  letI : Fintype (H1 (gamma h q : Type) DD.Vmod) :=
    Fintype.ofEquiv (DD.Vmod × (Fin h → DD.Vmod × DD.Vmod)) e.symm
  refine { qSource := fun x => lSqWallHandlePhase DD.qbar U h (e x)
           source_eq := hphase
           arf_zero := ?_ }
  rw [arf_eq_zero_iff_gaussSum_pos]
  rw [gaussSum_comp_equiv (lSqWallHandlePhase DD.qbar U h) e, hgauss]
  show (0 : ℤ) < (2 : ℤ) ^ ((2 * h + 1) * m)
  positivity

/-! ## The block-level source-Arf datum, and the ramified word phase without a binder -/

set_option linter.unusedVariables false in
set_option maxHeartbeats 800000 in
/-- **The source-Arf input of `wordPhaseResidueK_ramified_lSq` is a theorem at `q = 2 ^ F`,
`F` odd.**  Same block hypotheses as that theorem, plus the ramification hypothesis `hram` it
already carries. -/
def lRamifiedSourceArf_blockK
    {h q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
    (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
    (F : BoundaryFrameK q P H E)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    {f : ℕ} (hfodd : Odd f) (hqf : q = 2 ^ f)
    (m : ℕ)
    (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
    (l : (SectionNine.blockFrame T Blk hE2).DR)
    (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
    (hram :
      letI := blockPS_commGroup Blk
      letI := SectionNine.headAct T Blk
      ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v) :
    let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
    let DD := En.descData l hl
    letI : TopologicalSpace DD.Vmod := ⊥
    letI : DiscreteTopology DD.Vmod := ⟨rfl⟩
    letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
      scalarActionZmodTwo ((gamma h q : Type))
    ∀ rho : BoundaryLiftsK (sourceBoundaryMapK tame pro2 compat) F
        (SectionNine.blockFrame T Blk hE2).TC,
      let rhoM := rhoPrimeK (SectionNine.blockFrame T Blk hE2)
        (sourceBoundaryMapK tame pro2 compat) F (En.radData l hl) rfl rho
      letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
        DistribMulAction.compHom DD.Vmod (rho0 DD rhoM)
      let hcomp : ∀ (g : (gamma h q : Type)) (v : DD.Vmod),
          g • v = rho0 DD rhoM g • v := fun _ _ ↦ rfl
      LRamifiedSourceArfData rhoM (scalarActionZmodTwo_triv _) hcomp := by
  letI := blockPS_commGroup Blk
  letI := blockActVY Blk
  letI := blockActV Blk
  letI := SectionNine.headAct T Blk
  letI := SectionNine.hvAct T Blk
  have hl' : l.1 ≠ Blk.frattiniK := fun heq => hl (Subtype.ext heq)
  intro En DD rho rhoM hcompat
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) (ZMod 2) :=
    scalarActionZmodTwo ((gamma h q : Type))
  letI : DistribMulAction ((gamma h q : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (rho0 DD rhoM)
  letI : TopologicalSpace DD.C0 :=
    (inferInstance : TopologicalSpace (SectionNine.blockFrame T Blk hE2).YC)
  haveI : DiscreteTopology DD.C0 :=
    (inferInstance : DiscreteTopology (SectionNine.blockFrame T Blk hE2).YC)
  letI : DistribMulAction (SectionNine.blockFrame T Blk hE2).YC DD.Vmod := blockActV Blk
  letI : DistribMulAction (SectionNine.HVq T Blk) DD.Vmod := SectionNine.hvAct T Blk
  set theta := Count.rho0Continuous DD rhoM with htheta
  haveI : ContinuousSMul ((gamma h q : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((gamma h q : Type)) × DD.Vmod ↦ p.1 • p.2) =
          (fun p : DD.C0 × DD.Vmod ↦ p.1 • p.2) ∘
            (fun p : ((gamma h q : Type)) × DD.Vmod ↦ (theta p.1, p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hround : ∀ γ : (gamma h q : Type), rho0 DD rhoM γ = rho.1.1 γ :=
    rho0_descData_rhoPrimeK (sourceBoundaryMapK tame pro2 compat) F En l hl rho
  have hheadFac : ∀ γ : (gamma h q : Type),
      SectionNine.blockProjF T Blk (rho0 DD rhoM γ) = headTameSurjK T Blk F (tame γ) := by
    intro γ
    rw [hround γ]
    exact congrArg (⇑(QuotientGroup.mk' (SectionNine.headActKer T Blk)))
      (boundaryLift_headK T Blk hE2 (sourceBoundaryMapK tame pro2 compat) F rho γ)
  have hwildHead : ∀ i : Fin (2 * h + 1 + 1),
      SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) (.wild i))) = 1 := by
    intro i
    rw [hheadFac, htameWild i]
    show QuotientGroup.mk' (SectionNine.headActKer T Blk) (F.alpha 1) = 1
    rw [map_one, map_one]
  have hsigmaHead :
      SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .sigma)) = hvSigmaK T Blk F := by
    rw [hheadFac, htameSigma]
    rfl
  have htauHead :
      SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) = hvTauK T Blk F := by
    rw [hheadFac, htameTau]
    rfl
  have hrelHV : (hvSigmaK T Blk F)⁻¹ * hvTauK T Blk F * hvSigmaK T Blk F
      = hvTauK T Blk F ^ q := hv_relK T Blk F
  haveI hnormHV : (Subgroup.zpowers (hvTauK T Blk F)).Normal :=
    tame_zpowers_normal_pow (hv_genK T Blk F) hrelHV
  have hoddHV : Odd (orderOf (hvTauK T Blk F)) :=
    tame_odd_order_pow (orderOf_pos (hvSigmaK T Blk F)).ne' hq0 hqe hrelHV
  have hramF : ∃ v : DD.Vmod, hvTauK T Blk F • v ≠ v := hram
  have htauFPF : ∀ v : DD.Vmod, hvTauK T Blk F • v = v → v = 0 :=
    tau_fixed_eq_zero_of_zpowers_normal (hvTauK T Blk F) hnormHV
      (SectionNine.hv_simple T Blk) hramF
  have hτfpf : ∀ v : DD.Vmod,
      rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau) • v = v → v = 0 := by
    intro v hv
    apply htauFPF v
    have hstep : rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau) • v
        = SectionNine.blockProjF T Blk
            (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rwa [hstep, htauHead] at hv
  have hTodd : ∀ v : DD.Vmod,
      powOmega2 (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v = v := by
    intro v
    have hstep : powOmega2 (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau)) • v
        = SectionNine.blockProjF T Blk
            (powOmega2 (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .tau))) • v :=
      SectionNine.blockProjF_compat T Blk _ v
    rw [hstep, powOmega2_map (SectionNine.blockProjF T Blk), htauHead,
      powOmega2_eq_one_of_odd hoddHV, one_smul]
  -- the tame pair at the head, in the shape the general-`q` pack consumes
  have hgenC : Subgroup.closure
      ({SectionNine.blockProjF T Blk
          (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .sigma)),
        hvTauK T Blk F} : Set (SectionNine.HVq T Blk)) = ⊤ := by
    rw [hsigmaHead]
    exact hv_genK T Blk F
  have hrelC : (SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .sigma)))⁻¹ * hvTauK T Blk F *
      SectionNine.blockProjF T Blk
        (rho0 DD rhoM (gammaGen (2 * h + 1) q (lSqW h) .sigma)) =
      hvTauK T Blk F ^ 2 ^ f := by
    rw [hsigmaHead, hrelHV, ← hqf]
  exact lRamifiedSourceArfData_of_headAction (DD := DD) (Cbar := SectionNine.HVq T Blk) rhoM
    (blockDatHVK T Blk hq0 hqe F l hl') (blockDatHV_specK T Blk hq0 hqe F l hl')
    (SectionNine.blockProjF T Blk) (SectionNine.blockProjF_compat T Blk)
    (fun _ _ => rfl) (fun _ _ => rfl) hcompat (Vmod_exp2 DD) hqe m hcard
    { wild_head := hwildHead
      tau_fixedPointFree := hτfpf
      tau_oddPart_fixed := hTodd }
    (hvTauK T Blk F) hfodd hgenC hrelC (SectionNine.hv_simple T Blk) hramF

/-! ## The L row, unconditional at `q = 2 ^ f` with `f` odd

`LRamifiedSourceArfSupply` is not available (see (3) in the module docstring: it is stated
without a ramification hypothesis).  What the determinant residue actually needs is the
`hram`-conditioned datum, and `lRamifiedSourceArf_blockK` supplies it, so the whole word-phase
supply is a theorem. -/

set_option maxHeartbeats 1200000 in
/-- **The complete word-phase supply for the improved L presentation, with no arithmetic
binder**, at `q = 2 ^ f` with `f` odd.  Compare `determinantWordPhaseSupply_lSq`, which takes
`LRamifiedSourceArfSupply` as an argument. -/
def determinantWordPhaseSupply_lSq_pow {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    {f : ℕ} (hfodd : Odd f) (hqf : q = 2 ^ f) :
    DeterminantWordPhaseSupply nuP tame pro2 compat where
  unramified := fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram =>
    wordPhaseResidueK_unramified_lSq T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild hsimple hVne hnt m hm hcard l hl hunram
  ramified := fun T Blk _ _ _ hE2 hq0 hqe F _ _ _ m _ hcard l hl hram =>
    wordPhaseResidueK_ramified_lSq T Blk hE2 hq0 hqe F tame pro2 compat
      htameSigma htameTau htameWild m hcard l hl hram
      (lRamifiedSourceArf_blockK T Blk hE2 hq0 hqe F tame pro2 compat
        htameSigma htameTau htameWild hfodd hqf m hcard l hl hram)

set_option maxHeartbeats 1200000 in
/-- **The determinant residue for the improved L presentation, unconditionally**, at
`q = 2 ^ f` with `f` odd. -/
theorem determinantResidue_lSq_pow {h q : ℕ} {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma h q) P)
    (compat : ∀ g : (gamma h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (htameSigma : tame (gammaGen (2 * h + 1) q (lSqW h) .sigma) = tqSigma q)
    (htameTau : tame (gammaGen (2 * h + 1) q (lSqW h) .tau) = tqTau q)
    (htameWild : ∀ i : Fin (2 * h + 1 + 1),
      tame (gammaGen (2 * h + 1) q (lSqW h) (.wild i)) = 1)
    {f : ℕ} (hfodd : Odd f) (hqf : q = 2 ^ f) :
    DeterminantResidue nuP tame pro2 compat :=
  affineDeterminantCertificate_of_wordPhaseSupply nuP tame pro2 compat
    (determinantWordPhaseSupply_lSq_pow nuP tame pro2 compat htameSigma htameTau htameWild
      hfodd hqf)

/-- **`LSquareAnalyticLeavesRN` with no arithmetic binder** at `q = 2 ^ f`, `f` odd. -/
def lSquareAnalyticLeavesRN_pow {h q : ℕ} (hq2 : 2 ≤ q) (hqe : Even q)
    {f : ℕ} (hfodd : Odd f) (hqf : q = 2 ^ f) :
    LSquareAnalyticLeavesRN h q hq2 hqe where
  determinant :=
    determinantResidue_lSq_pow (Instances.LSquareCore.lNu h)
      (tameOfSpec (2 * h + 1) q (lSqW h) (lCanonicalTameSpecialization h q hq2 hqe))
      (lCanonicalPro2 h q hq2 hqe) (lCanonicalCompat h q hq2 hqe)
      (tameOfSpec_lSq_sigma hq2 hqe) (tameOfSpec_lSq_tau hq2 hqe)
      (tameOfSpec_lSq_wild hq2 hqe) hfodd hqf

/-- **The corrected L word certificate, unconditional at `q = 2 ^ f` with `f` odd.**  This is
`wordCertificateRN_lSq_of_sourceArf` with its arithmetic binder discharged. -/
noncomputable def wordCertificateRN_lSq_pow {h f : ℕ} (hfodd : Odd f) :
    WordCertificateRN (2 * h + 1) (2 ^ f) (lSqW h) (SqCore.DSq h)
      (SqCore.isProP_DSq h) (Instances.LSquareCore.lNu h)
      (standardNumerics (2 * h + 1)) := by
  have hf1 : 1 ≤ f := hfodd.pos
  have hq2 : 2 ≤ (2 : ℕ) ^ f := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  have hqe : Even ((2 : ℕ) ^ f) := by
    obtain ⟨j, hj⟩ : ∃ j, f = j + 1 := ⟨f - 1, by omega⟩
    exact ⟨2 ^ j, by rw [hj, pow_succ]; ring⟩
  exact wordCertificateRN_lSq_of_actionImage hq2 hqe
    (lSquareAnalyticLeavesRN_pow hq2 hqe hfodd rfl)


/-! ## Regression: the `q = 2` instances

`f = 1` is odd and `2 ^ 1 = 2`, so every generalized statement specializes to its `ℚ₂`
original.  (`Tq 2` is *definitionally* `Ttame`, `tqSigma 2 = tameSigma`, `tqTau 2 = tameTau`,
so these are the same objects, not isomorphic copies.) -/

section Regression

/-- The `q = 2` instance of the general two-power ramified count is the `ℚ₂` statement. -/
example {C : Type} [Group C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V] (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (fun v => powOmega2 s • v)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) :=
  RamifiedPow.zeroCount_qDouble_ramified_of_action_pow s t odd_one hgen
    (by rw [hrel, pow_one]) hsimple hram q hq hns hinv m hm hcard

/-- The `q = 2` instance of the unconditional L word certificate. -/
example (h : ℕ) :
    WordCertificateRN (2 * h + 1) 2 (lSqW h) (SqCore.DSq h)
      (SqCore.isProP_DSq h) (Instances.LSquareCore.lNu h)
      (standardNumerics (2 * h + 1)) :=
  wordCertificateRN_lSq_pow (f := 1) odd_one

end Regression

end

end GQ2.Dyadic.LSquare

#print axioms GQ2.Dyadic.LSquare.qDouble_smul_inv_eq
#print axioms GQ2.Dyadic.LSquare.arf_qDouble_ramified_of_action_pow
#print axioms GQ2.Dyadic.LSquare.lRamifiedSourceArfData_of_headAction
#print axioms GQ2.Dyadic.LSquare.lRamifiedSourceArf_blockK
#print axioms GQ2.Dyadic.LSquare.determinantWordPhaseSupply_lSq_pow
#print axioms GQ2.Dyadic.LSquare.determinantResidue_lSq_pow
#print axioms GQ2.Dyadic.LSquare.lSquareAnalyticLeavesRN_pow
#print axioms GQ2.Dyadic.LSquare.wordCertificateRN_lSq_pow
