import GQ2.GaussZ.CoordGammaA
import GQ2.GaussZ.RelatorGammaA
import GQ2.GaussZ.Final
import GQ2.RamifiedPack

/-!
# P-16d6e4aA (A-4): the `Γ_A` Gauss residue — assembly shell + the pinned-value seams

The final brick of the (83)-for-`Γ_A` lane: `gaussZResidue_gammaA_{unramified,ramified}`
discharge the `prop_8_9` ledger hypothesis `hGaussZA` at the pinned values `∓2^m`, mirroring
`GaussZFinal.gaussZResidue_local_*` with the `Γ_A` toolkit:

* the reduction `gaussZ_reduction` (generic) at `Γ := GammaA`, with `Z¹`-finiteness from
  `GaussZCoordGammaA.finite_vcocycle_gammaA` and the `V^{C₀} = 0` freeness from
  `hfix_of_simple_nt` (`hnt`-only — no `hfaith` on the source side);
* the **pinned-value seams** `sum_sign_QZeroBar_gammaA_{unramified,ramified}`:
  `∑ sign(Q̄⁰) = ∓2^m` over `Z¹⧸B¹` — **the A-4 core, currently SORRIED (skeleton-first)**.
  Route (`docs/p16d6e4aA-a4-prep.md`, the paper's Prop 6.5/6.9): reindex the quotient by the
  `x₀`-supported section (`FoxHeisenberg.x0Supported`, the paper's gauge; bijective onto
  `H¹_w` by the `d¹`-closed forms + `card_H1w_gammaA`); evaluate `Q̄⁰` on the section through
  A-3's `QZero_eq_relZPair_kappa0` by the κ⁰-ledger (the quadratic mirror of the banked
  mixed ledgers `heisMarking_wildValue_z`/`_ramified` — Prop 6.5's table: `h₀ ↦ q(c)` via
  `classTwoIdentity`, `[d₀,z₀] ↦ B(c, U⁻¹c)` ram / `0` split); identify with `q̄` (unram,
  `T = 1` ⟹ `U = 1` collapse) / `qDouble q̄ U` (ram) and count via `prop_6_9_unramified` /
  `lemma_6_8` clause 4 + `gaussSum_eq_of_arf_eq`.

Axioms: the shell is std-3; the seams are expected std-3 (word-side; the pins are proved).
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridge FoxH RStageGammaA WordCoh2 QuadraticFp2

/-! ## A-4.1: the `x₀`-supported section of `H¹_w`  (generic marking level)

The paper's "only `x₀` varies" gauge (Prop 6.5's normalization), as a bijective
parametrization `V ≃ H¹_w`: membership and bijectivity fall out of the banked
`lemma_5_13_split` shape characterizations (`Z¹_w = {x₁-row = x₃-row = 0}`,
`B¹_w = σ-row of coboundaries`).  Ramified twin in the next increment via
`lemma_5_13_ramified`. -/

section X0Section

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- **The `x₀`-supported tuples are word cocycles** (split regime): immediate from the
`lemma_5_13_split` `Z¹`-shape (`x 1 = x 3 = 0`). -/
theorem x0Supported_mem_Z1w_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (hVS : ∀ v : V, t.σ • v = v → v = 0) (v : V) :
    x0Supported v ∈ Z1w (A := V) t :=
  ((lemma_5_13_split t ht hw hV₂ hsimple hcore htau hU hVS).1 (x0Supported v)).mpr ⟨rfl, rfl⟩

/-- The `H¹_w`-class equality criterion in `h1wMk` vocabulary (`H1w` is a semireducible
`def`, so the quotient lemmas do not elaborate against it directly — the
`GaussZLocal.H1mk_eq_iff` idiom). -/
theorem h1wMk_eq_iff {t : Marking C} [Finite V] (x y : ↥(Z1w (A := V) t)) :
    h1wMk t x = h1wMk t y
      ↔ (x - y : ↥(Z1w (A := V) t)).1 ∈ B1w (A := V) t := by
  show (QuotientAddGroup.mk x
      : ↥(Z1w (A := V) t) ⧸ (B1w (A := V) t).addSubgroupOf (Z1w (A := V) t))
    = QuotientAddGroup.mk y ↔ _
  exact QuotientAddGroup.eq_iff_sub_mem

/-- **The `x₀`-supported section of `H¹_w` is bijective** (split regime): injectivity from
the `B¹`-shape (coboundaries live in the `σ`-row, so an `x₀`-row difference must vanish);
surjectivity by normalizing the `σ`-row away (`(σ − 1)` is onto by `hVS` + finiteness). -/
theorem x0Section_bijective_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v)
    (hVS : ∀ v : V, t.σ • v = v → v = 0) :
    Function.Bijective (fun v : V => h1wMk t
      ⟨x0Supported v, x0Supported_mem_Z1w_split t ht hw hV₂ hsimple hcore htau hU hVS v⟩) := by
  have hshape := lemma_5_13_split t ht hw hV₂ hsimple hcore htau hU hVS
  constructor
  · -- injective: an `x₀`-row coboundary difference is `σ`-row–shaped, hence zero
    intro v v' hvv'
    have hmem := (h1wMk_eq_iff _ _).mp hvv'
    obtain ⟨w, hw'⟩ := (hshape.2 _).mp hmem
    have h2 := congrFun hw' 2
    exact sub_eq_zero.mp (by simpa [x0Supported] using h2)
  · -- surjective: normalize the `σ`-row away
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨h1, h3⟩ := (hshape.1 z.1).mp z.2
      have hsurj : Function.Surjective (fun w : V => t.σ • w - w) :=
        FoxH.surjective_smul_sub_of_fixedPointFree hVS
      obtain ⟨w, hw'⟩ := hsurj (z.1 0)
      refine ⟨z.1 2, ?_⟩
      show h1wMk t ⟨x0Supported (z.1 2), _⟩ = QuotientAddGroup.mk z
      rw [show (QuotientAddGroup.mk z
          : ↥(Z1w (A := V) t) ⧸ (B1w (A := V) t).addSubgroupOf (Z1w (A := V) t))
        = h1wMk t z from rfl,
        h1wMk_eq_iff]
      refine (hshape.2 _).mpr ⟨-w, ?_⟩
      have hw'' : t.σ • w - w = z.1 0 := hw'
      funext i
      show x0Supported (z.1 2) i - z.1 i = _
      fin_cases i
      · show (0 : V) - z.1 0 = t.σ • (-w) - (-w)
        rw [smul_neg, ← hw'']
        abel
      · show (0 : V) - z.1 1 = 0
        rw [h1, sub_zero]
      · show z.1 2 - z.1 2 = 0
        exact sub_self _
      · show (0 : V) - z.1 3 = 0
        rw [h3, sub_zero]

/-- **The `x₀`-supported section of `H¹_w` is bijective** (ramified regime): both halves
from `lemma_5_13_ramified`'s unique normal form. -/
theorem x0Section_bijective_ramified (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    Function.Bijective (fun v : V => h1wMk t
      ⟨x0Supported v, x0Supported_mem_Z1w_ramified t ht hV₂ hx0 hx1 htau hTodd v⟩) := by
  have hnf := lemma_5_13_ramified t ht hw hV₂ hx0 hx1 htau hTodd
  constructor
  · -- injective: apply the unique-witness clause at `x := x0Supported (v − v')`
    intro v v' hvv'
    have hmem := (h1wMk_eq_iff _ _).mp hvv'
    have hdiff : ((⟨x0Supported v,
          x0Supported_mem_Z1w_ramified t ht hV₂ hx0 hx1 htau hTodd v⟩
        - ⟨x0Supported v',
          x0Supported_mem_Z1w_ramified t ht hV₂ hx0 hx1 htau hTodd v'⟩
        : ↥(Z1w (A := V) t)) : Fin 4 → V) = x0Supported (v - v') := by
      funext i
      show x0Supported v i - x0Supported v' i = x0Supported (v - v') i
      fin_cases i <;> simp [x0Supported]
    rw [hdiff] at hmem
    -- `x0Supported (v − v') ∈ Z1w` with two normal-form witnesses `v − v'` and `0`
    obtain ⟨cne, -, huniq⟩ :=
      hnf (x0Supported (v - v'))
        (x0Supported_mem_Z1w_ramified t ht hV₂ hx0 hx1 htau hTodd (v - v'))
    have h1 : (v - v') = cne := huniq (v - v') (by
      show x0Supported (v - v') - x0Supported (v - v') ∈ B1w (A := V) t
      rw [sub_self]
      exact zero_mem _)
    have h2 : (0 : V) = cne := huniq 0 (by
      show x0Supported (v - v') - x0Supported (0 : V) ∈ B1w (A := V) t
      rw [show x0Supported (0 : V) = (0 : Fin 4 → V) from by
          funext i; fin_cases i <;> simp [x0Supported],
        sub_zero]
      exact hmem)
    exact sub_eq_zero.mp (h1.trans h2.symm)
  · -- surjective: the normal-form witness of any representative
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨c, hc, -⟩ := hnf z.1 z.2
      refine ⟨c, ?_⟩
      show h1wMk t ⟨x0Supported c, _⟩ = QuotientAddGroup.mk z
      rw [show (QuotientAddGroup.mk z
          : ↥(Z1w (A := V) t) ⧸ (B1w (A := V) t).addSubgroupOf (Z1w (A := V) t))
        = h1wMk t z from rfl,
        h1wMk_eq_iff]
      show ((⟨x0Supported c, _⟩ - z : ↥(Z1w (A := V) t)) : Fin 4 → V) ∈ B1w (A := V) t
      have hneg : ((⟨x0Supported c,
            x0Supported_mem_Z1w_ramified t ht hV₂ hx0 hx1 htau hTodd c⟩
          - z : ↥(Z1w (A := V) t)) : Fin 4 → V)
          = -(z.1 - x0Supported c) := by
        funext i
        show x0Supported c i - z.1 i = -(z.1 i - x0Supported c i)
        abel
      rw [hneg]
      exact neg_mem hc

end X0Section

/-! ## A-4.2: the κ⁰-ledger, tame value — the base-slice section

The tame relator only walks the `σ`/`τ`-slots; on the `x₀`-supported gauge those have
zero `V`-part, and `κ⁰` vanishes when both arguments do (`f_zero_left` + `m_zero`), so
the whole walk stays in the image of the base-slice section hom `sdSec : C →* CentExt κ⁰`
— the κ⁰-analog of the mixed ledger's `secHom`.  Hence the tame fibre is `0`. -/

section Kappa0Ledger

variable {C V : Type*} [Group C] [AddCommGroup V] [DistribMulAction C V]
variable {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- The base-slice section `cc ↦ ((0, cc), 0)` is a homomorphism into `CentExt κ⁰`. -/
noncomputable def sdSec : C →* CentExt (kappa0Cocycle dat hdat) where
  toFun cc := (Sd.mk (0 : V) cc, 0)
  map_one' := rfl
  map_mul' cc dd := by
    refine (CentExt.ext ?_ ?_).symm
    · refine Sd.ext ?_ rfl
      show (0 : V) + cc • (0 : V) = 0
      rw [smul_zero, add_zero]
    · show (0 : ZMod 2) + 0 + (kappa0Cocycle dat hdat).κ (Sd.mk (0 : V) cc) (Sd.mk (0 : V) dd)
        = 0
      rw [kappa0Cocycle_κ]
      show (0 : ZMod 2) + 0 + (dat.f (0 : V) (cc • (0 : V)) + dat.m cc (0 : V)) = 0
      rw [smul_zero, hdat.f_zero_left, hdat.m_zero]
      decide


@[simp] theorem sdSec_fib (cc : C) : (sdSec dat hdat cc).fib = 0 := rfl

/-- **The tame κ⁰-value is base-slice**: at any lifted marking whose `σ`/`τ`-slots have
zero `V`-part, the tame relator value is the `sdSec`-image of the `C`-level tame value —
its fibre vanishes (no `TameRel` needed). -/
theorem liftMark_kappa0_tameValue_fib (t : Marking (Sd C V))
    (hσ : t.σ.v = 0) (hτ : t.τ.v = 0) :
    (liftMark t (kappa0Cocycle dat hdat)).tameValue.fib = 0 := by
  have hσ' : (liftMark t (kappa0Cocycle dat hdat)).σ = sdSec dat hdat t.σ.cc :=
    CentExt.ext (Sd.ext hσ rfl) rfl
  have hτ' : (liftMark t (kappa0Cocycle dat hdat)).τ = sdSec dat hdat t.τ.cc :=
    CentExt.ext (Sd.ext hτ rfl) rfl
  show (conjP (liftMark t (kappa0Cocycle dat hdat)).τ
      (liftMark t (kappa0Cocycle dat hdat)).σ
    * ((liftMark t (kappa0Cocycle dat hdat)).τ ^ 2)⁻¹).fib = 0
  rw [hσ', hτ', ← Marking.map_conjP, ← map_pow, ← map_inv, ← map_mul]
  rfl

/-- The A-3 interface form: the FIRST relator-`z` component vanishes on base-slice
`σ`/`τ`-slots. -/
theorem relZPair_kappa0_fst_eq_zero [Finite C] [Finite V] (t : Marking (Sd C V))
    (hσ : t.σ.v = 0) (hτ : t.τ.v = 0) :
    (relZPair t (kappa0Cocycle dat hdat)).1 = 0 :=
  liftMark_kappa0_tameValue_fib dat hdat t hσ hτ

/-! ### A-4.3a: the coordinate transport toolkit

The `Sd`-parts of the wild-word factors transport to the BANKED `liftMarking_*_u`
V-part ledger through the carrier identification `Sd C V ≅ WordLift V C` (same
semidirect law), and the `CentExt κ⁰`-factors project to the `Sd`-factors through
`CentExt.proj` — so every base coordinate in the κ⁰-peel is already computed.  The
fibre cells are then `CentExt.mul_fib` + the evaluated `κ⁰`-values; the first
(and quadratically decisive) cell is the `x₀`-square `q(v) + m_{P}(v)`. -/

/-- The carrier identification `Sd C V →* WordLift V C` (the two semidirect laws agree). -/
noncomputable def sdToWL : Sd C V →* WordLift V C where
  toFun p := ⟨p.v, p.cc⟩
  map_one' := rfl
  map_mul' _ _ := rfl


/-- The `C`-level base marking of an `Sd`-marking. -/
noncomputable def sdBaseMarking (tS : Marking (Sd C V)) : Marking C :=
  ⟨tS.σ.cc, tS.τ.cc, tS.x₀.cc, tS.x₁.cc⟩

/-- The `V`-offset tuple of an `Sd`-marking. -/
noncomputable def sdOffsets (tS : Marking (Sd C V)) : Fin 4 → V :=
  ![tS.σ.v, tS.τ.v, tS.x₀.v, tS.x₁.v]

/-- Under the carrier identification, an `Sd`-marking IS the `liftMarking` of its base
marking at its offset tuple. -/
theorem sdToWL_marking (tS : Marking (Sd C V)) :
    tS.map sdToWL = liftMarking (sdBaseMarking tS) (sdOffsets tS) :=
  rfl

section FactorTransport

variable [Finite C] [Finite V]

/-- `d₀`'s `V`-part transports to the banked `WordLift` ledger. -/
theorem sd_d0_v (tS : Marking (Sd C V)) :
    tS.d0.v = (liftMarking (sdBaseMarking tS) (sdOffsets tS)).d0.u := by
  have h := Marking.map_d0 (f := sdToWL) (t := tS)
  rw [sdToWL_marking] at h
  exact (congrArg WordLift.u h).symm


/-- The `CentExt κ⁰`-level factors project to the `Sd`-level factors (`d₀` case; the
projection is `liftMark_map_proj` + word functoriality). -/
theorem liftMark_d0_base (tS : Marking (Sd C V)) :
    ((liftMark tS (kappa0Cocycle dat hdat)).d0).base = tS.d0 := by
  have h := Marking.map_d0 (f := CentExt.proj (kappa0Cocycle dat hdat))
    (t := liftMark tS (kappa0Cocycle dat hdat))
  rw [liftMark_map_proj] at h
  exact h.symm

end FactorTransport


/-! ### A-4.3b: conjugation and base-slice fibre cells + the `m`-calculus

The κ⁰-peel's step lemmas: on `V`-part-zero prefixes the fibre accumulates only
`m`-corrections (`f` dies on a zero slot); conjugation by an `sdSec`-image shifts the
fibre by one `m`-value; `m` at squares/inverses of `V`-fixing elements vanishes/reflects
(`m_mul` + char 2).  These are the `CentExt κ⁰`-analogs of the `HeisLift.mul_z_of_trivial`
family. -/

theorem sdSec_inv (w : C) : (sdSec dat hdat w)⁻¹ = sdSec dat hdat w⁻¹ :=
  (map_inv (sdSec dat hdat) w).symm


/-- **The fibre step on a `V`-part-zero left factor**: only the `m`-correction survives. -/
theorem mul_fib_of_v_zero (p r : CentExt (kappa0Cocycle dat hdat))
    (hp : p.base.v = 0) :
    (p * r).fib = p.fib + r.fib + dat.m p.base.cc r.base.v := by
  rw [CentExt.mul_fib, kappa0Cocycle_κ, hp, hdat.f_zero_left, zero_add]


/-- **The fibre step on a `V`-part-zero RIGHT factor**: `κ⁰(·, v-part 0)` dies entirely. -/
theorem mul_fib_of_v_zero_right (p r : CentExt (kappa0Cocycle dat hdat))
    (hr : r.base.v = 0) :
    (p * r).fib = p.fib + r.fib := by
  rw [CentExt.mul_fib, kappa0Cocycle_κ, hr, smul_zero, hdat.f_zero_right, hdat.m_zero,
    add_zero, add_zero]

/-- The base of a conjugate by an `sdSec`-image (through `CentExt.proj`). -/
theorem conjP_sdSec_base (x : CentExt (kappa0Cocycle dat hdat)) (w : C) :
    (conjP x (sdSec dat hdat w)).base = conjP x.base (Sd.mk (0 : V) w) :=
  Marking.map_conjP (CentExt.proj (kappa0Cocycle dat hdat)) x (sdSec dat hdat w)

/-- The `V`-part of an `Sd`-conjugate by a `V`-part-zero element: the `w⁻¹`-twist. -/
theorem sd_conjP_v (p : Sd C V) (w : C) :
    (conjP p (Sd.mk (0 : V) w)).v = w⁻¹ • p.v := by
  show ((Sd.mk (0 : V) w)⁻¹ * p * Sd.mk (0 : V) w).v = w⁻¹ • p.v
  show ((Sd.mk (0 : V) w)⁻¹ * p).v + ((Sd.mk (0 : V) w)⁻¹ * p).cc • (0 : V) = w⁻¹ • p.v
  rw [smul_zero, add_zero]
  show (Sd.mk (0 : V) w)⁻¹.v + (Sd.mk (0 : V) w)⁻¹.cc • p.v = w⁻¹ • p.v
  show -(w⁻¹ • (0 : V)) + w⁻¹ • p.v = w⁻¹ • p.v
  rw [smul_zero, neg_zero, zero_add]

/-- **The conjugation fibre cell**: conjugating by an `sdSec`-image shifts the fibre by
the single `m`-correction `m_{w⁻¹}` at the `V`-part. -/
theorem conjP_sdSec_fib (x : CentExt (kappa0Cocycle dat hdat)) (w : C) :
    (conjP x (sdSec dat hdat w)).fib = x.fib + dat.m w⁻¹ x.base.v := by
  show ((sdSec dat hdat w)⁻¹ * x * sdSec dat hdat w).fib = _
  rw [mul_fib_of_v_zero_right dat hdat _ _ (show (sdSec dat hdat w).base.v = 0 from rfl),
    sdSec_inv,
    mul_fib_of_v_zero dat hdat _ _ (show (sdSec dat hdat w⁻¹).base.v = 0 from rfl),
    sdSec_fib, sdSec_fib, zero_add, add_zero]
  rfl

include hdat in
/-- `m` at an inverse of a `V`-fixing element reflects (from `m_mul` + `m_one` + char 2). -/
theorem m_inv_of_fixed (w : C) (v : V) (hfix : w • v = v) :
    dat.m w⁻¹ v = dat.m w v := by
  have h := hdat.m_mul w⁻¹ w v
  rw [inv_mul_cancel, hdat.m_one, hfix] at h
  exact CharTwo.add_eq_zero.mp h.symm

include hdat in
/-- `m` at a square of a `V`-fixing element vanishes. -/
theorem m_sq_of_fixed (w : C) (v : V) (hfix : w • v = v) :
    dat.m (w * w) v = 0 := by
  rw [hdat.m_mul, hfix]
  exact CharTwo.add_self_eq_zero _

/-! ### A-4.3c: the split wild value = the `x₀`-square

With the structural pack (`x₀.cc = x₁.cc = 1` from the tame factorization, `τ.cc` of odd
order — prep doc §6), `d₀` has base `1`, hence is CENTRAL in `CentExt κ⁰`: the whole wild
word collapses (`d₀² = 1`, `d_g = d₀`, `h_c = c₀ = 1`, `u₁ = 1`, `x₁^σ = 1`, and
`h₀ = x₀²` on the nose — the paper's p. 15 "replacing `h₀` by `x₀²`").  The split wild
fibre is therefore the `x₀`-square `q(v)`, with every starred `m`-entry dying on
`m_one`. -/

/-- The `C`-component projection `Sd C V →* C`. -/
noncomputable def sdCcHom : Sd C V →* C where
  toFun := Sd.cc
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Base-`1` elements of `CentExt κ⁰` are central (`κ⁰` dies against `1` on both sides). -/
theorem central_of_base_one (p : CentExt (kappa0Cocycle dat hdat)) (hp : p.base = 1)
    (x : CentExt (kappa0Cocycle dat hdat)) : p * x = x * p := by
  refine CentExt.ext ?_ ?_
  · show p.base * x.base = x.base * p.base
    rw [hp, one_mul, mul_one]
  · show p.fib + x.fib + (kappa0Cocycle dat hdat).κ p.base x.base
      = x.fib + p.fib + (kappa0Cocycle dat hdat).κ x.base p.base
    rw [hp, kappa0Cocycle_κ, kappa0Cocycle_κ]
    show p.fib + x.fib + (dat.f (0 : V) ((1 : C) • x.base.v) + dat.m (1 : C) x.base.v)
      = x.fib + p.fib + (dat.f x.base.v (x.base.cc • (0 : V)) + dat.m x.base.cc (0 : V))
    rw [hdat.f_zero_left, hdat.m_one, smul_zero, hdat.f_zero_right, hdat.m_zero]
    ring

/-- **The split wild κ⁰-value is the `x₀`-square** (paper (83), `T = 1` case): with the
structural pack, the lifted wild relator value has fibre `q(x₀.v)` — every starred
`m`-entry dies on `m_one`, and the base-central `d₀` collapses the word to `x₀²`. -/
theorem liftMark_kappa0_wildValue_fib_split [Finite C] [Finite V]
    (tS : Marking (Sd C V))
    (hσv : tS.σ.v = 0) (hτv : tS.τ.v = 0) (hx1v : tS.x₁.v = 0)
    (hx0cc : tS.x₀.cc = 1) (hx1cc : tS.x₁.cc = 1)
    (hV₂ : ∀ w : V, w + w = 0)
    (htau : ∀ w : V, tS.τ.cc • w = w)
    (hU : ∀ w : V, Marking.sigma2 (sdBaseMarking tS) • w = w)
    (hτodd : Odd (orderOf tS.τ.cc)) :
    (liftMark tS (kappa0Cocycle dat hdat)).wildValue.fib = q tS.x₀.v := by
  classical
  set M := liftMark tS (kappa0Cocycle dat hdat) with hM
  -- slot forms
  have hMx1 : M.x₁ = 1 := CentExt.ext (Sd.ext hx1v hx1cc) rfl
  have hMτ : M.τ = sdSec dat hdat tS.τ.cc := CentExt.ext (Sd.ext hτv rfl) rfl
  have hMσ : M.σ = sdSec dat hdat tS.σ.cc := CentExt.ext (Sd.ext hσv rfl) rfl
  -- `u₁ = 1` and `x₁^σ = 1`
  have hu1 : M.u1 = 1 := by
    show powOmega2 (M.x₁ * M.τ) = 1
    rw [hMx1, one_mul, hMτ, ← powOmega2_map, powOmega2_eq_one_of_odd hτodd, map_one]
  have hx1s : conjP M.x₁ M.σ = 1 := by
    rw [conjP, hMx1, mul_one, inv_mul_cancel]
  -- `d₀.base = 1`: the `cc`-part by the `C`-level collapse, the `v`-part by the banked row
  have hd0cc : tS.d0.cc = 1 := by
    have h := (Marking.map_d0 (sdCcHom (C := C) (V := V)) tS).symm
    rw [show tS.map (sdCcHom (C := C) (V := V)) = sdBaseMarking tS from rfl] at h
    show sdCcHom (C := C) (V := V) tS.d0 = 1
    rw [h]
    show powOmega2 (tS.x₀.cc * tS.τ.cc) * (tS.x₀.cc)⁻¹ = 1
    rw [hx0cc, one_mul, inv_one, mul_one, powOmega2_eq_one_of_odd hτodd]
  have hd0v : tS.d0.v = 0 := by
    rw [sd_d0_v, liftMarking_d0_u (sdBaseMarking tS) (sdOffsets tS) hV₂
      (fun w => by show tS.x₀.cc • w = w; rw [hx0cc, one_smul]) htau]
    exact hτv
  have hd0base : M.d0.base = 1 := by
    show ((liftMark tS (kappa0Cocycle dat hdat)).d0).base = 1
    rw [liftMark_d0_base dat hdat tS]
    exact Sd.ext hd0v hd0cc
  -- `d₀` is central; the word collapses
  have hcen := central_of_base_one dat hdat M.d0 hd0base
  have hdg : M.dg = M.d0 := by
    show conjP M.d0 M.g0 = M.d0
    rw [conjP, mul_assoc, hcen M.g0, ← mul_assoc, inv_mul_cancel, one_mul]
  have hd0sq : M.d0 ^ 2 = 1 := by
    rw [pow_two]
    refine CentExt.ext ?_ ?_
    · show M.d0.base * M.d0.base = 1
      rw [hd0base, one_mul]
    · show M.d0.fib + M.d0.fib + (kappa0Cocycle dat hdat).κ M.d0.base M.d0.base = 0
      rw [hd0base, kappa0Cocycle_κ]
      show M.d0.fib + M.d0.fib + (dat.f (0 : V) ((1 : C) • (0 : V)) + dat.m (1 : C) (0 : V)) = 0
      rw [smul_zero, hdat.f_zero_left, hdat.m_zero, add_zero, add_zero]
      exact CharTwo.add_self_eq_zero _
  have hhc : M.hc = 1 := by
    show commP M.dg M.d0 = 1
    rw [hdg, commP]
    group
  have hc0 : M.c0 = 1 := by
    show commP M.d0 M.z0 = 1
    rw [commP]
    calc M.d0⁻¹ * M.z0⁻¹ * M.d0 * M.z0
        = M.d0⁻¹ * (M.z0⁻¹ * (M.d0 * M.z0)) := by group
      _ = M.d0⁻¹ * (M.z0⁻¹ * (M.z0 * M.d0)) := by rw [hcen M.z0]
      _ = 1 := by group
  -- `x₀^{g₀} = x₀` (the `hU`-collapse; every `m` dies on `m_sq`/`m_inv`)
  have hs2 : M.sigma2 = sdSec dat hdat (Marking.sigma2 (sdBaseMarking tS)) := by
    show powOmega2 M.σ = _
    rw [hMσ, ← powOmega2_map]
    rfl
  have hMg0 : M.g0 = sdSec dat hdat (Marking.g0 (sdBaseMarking tS)) := by
    show M.sigma2 ^ 2 = _
    rw [hs2, ← map_pow]
    rfl
  have hg0fix : ∀ w : V, Marking.g0 (sdBaseMarking tS) • w = w := by
    intro w
    show (Marking.sigma2 (sdBaseMarking tS) ^ 2) • w = w
    rw [pow_two, mul_smul, hU, hU]
  have hA : conjP M.x₀ M.g0 = M.x₀ := by
    rw [hMg0]
    refine CentExt.ext ?_ ?_
    · rw [conjP_sdSec_base]
      refine Sd.ext ?_ ?_
      · rw [sd_conjP_v, inv_smul_eq_iff]
        exact (hg0fix _).symm
      · show (Marking.g0 (sdBaseMarking tS))⁻¹ * tS.x₀.cc * Marking.g0 (sdBaseMarking tS)
          = tS.x₀.cc
        rw [hx0cc, mul_one, inv_mul_cancel]
    · rw [conjP_sdSec_fib,
        m_inv_of_fixed dat hdat _ _ (hg0fix _)]
      show M.x₀.fib + dat.m (Marking.sigma2 (sdBaseMarking tS) ^ 2) M.x₀.base.v = M.x₀.fib
      rw [pow_two, m_sq_of_fixed dat hdat _ _ (hU _), add_zero]
  -- `h₀ = x₀²`
  have hh0 : M.h0 = M.x₀ ^ 2 := by
    show (conjP M.x₀ M.g0) * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc = M.x₀ ^ 2
    rw [hA, hdg, hd0sq, hhc, mul_one, mul_one]
    calc M.x₀ * M.x₀ * M.d0 * M.d0
        = (M.x₀ * M.x₀) * (M.d0 * M.d0) := by group
      _ = M.x₀ ^ 2 * M.d0 ^ 2 := by rw [pow_two, pow_two]
      _ = M.x₀ ^ 2 := by rw [hd0sq, mul_one]
  -- assemble
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).fib = q tS.x₀.v
  rw [hu1, hx1s, hc0, inv_one, mul_one, mul_one, mul_one, hh0, pow_two, CentExt.mul_fib]
  show (0 : ZMod 2) + 0 + (kappa0Cocycle dat hdat).κ tS.x₀ tS.x₀ = q tS.x₀.v
  rw [kappa0Cocycle_κ]
  show (0 : ZMod 2) + 0 + (dat.f tS.x₀.v (tS.x₀.cc • tS.x₀.v) + dat.m tS.x₀.cc tS.x₀.v)
    = q tS.x₀.v
  rw [hx0cc, one_smul, hdat.f_diag, hdat.m_one]
  ring

/-! ### A-4.4: the ramified wild value = the Wall double

Ramified regime (`V^T = 0`): the structural pack persists, so `d₀` still has `cc = 1`,
but its `V`-part is now `a := x₀.v` (`liftMarking_d0_u_ramified`).  The `cc = 1` elements
form the abelian `V`-slice, whose `CentExt` is the `E_f`-Heisenberg: commutators produce
the polar form (`commP_fib_cc_one`), so `c₀ = [d₀,z₀] ↦ B(a, U⁻¹a)` — the p. 15 table's
ramified entry.  The `h₀`-peel telescopes to `q(g₀⁻¹a)` on one `f_cocycle` + `f_diag` +
`f_polar`, and `q`-invariance gives `q(a)`.  Total: `q(a) + B(a, U⁻¹a)`. -/

/-- `Sd`-elements with `cc = 1` commute (the abelian `V`-slice). -/
theorem sd_mul_comm_cc_one (p r : Sd C V) (hp : p.cc = 1) (hr : r.cc = 1) :
    p * r = r * p := by
  refine Sd.ext ?_ ?_
  · show p.v + p.cc • r.v = r.v + r.cc • p.v
    rw [hp, hr, one_smul, one_smul, add_comm]
  · show p.cc * r.cc = r.cc * p.cc
    rw [hp, hr]

/-- `commP` of two `V`-slice elements of `Sd` is `1`. -/
theorem sd_commP_cc_one (p r : Sd C V) (hp : p.cc = 1) (hr : r.cc = 1) :
    commP p r = 1 := by
  rw [commP]
  calc p⁻¹ * r⁻¹ * p * r = p⁻¹ * (r⁻¹ * (p * r)) := by group
    _ = p⁻¹ * (r⁻¹ * (r * p)) := by rw [sd_mul_comm_cc_one p r hp hr]
    _ = 1 := by group

/-- The κ⁰-value on two `V`-slice bases is the bare `f`-value. -/
theorem kappa0_cc_one (p r : Sd C V) (hp : p.cc = 1) :
    (kappa0Cocycle dat hdat).κ p r = dat.f p.v r.v := by
  rw [kappa0Cocycle_κ, hp, one_smul, hdat.m_one, add_zero]

/-- The inverse of a `V`-slice `CentExt`-element: same base (char 2), fibre shifted by
`q` of the `V`-part. -/
theorem inv_cc_one (p : CentExt (kappa0Cocycle dat hdat)) (hp : p.base.cc = 1)
    (hV₂ : ∀ w : V, w + w = 0) :
    p⁻¹.base = p.base ∧ p⁻¹.fib = p.fib + q p.base.v := by
  have hbv : p.base⁻¹.v = p.base.v := by
    show -(p.base.cc⁻¹ • p.base.v) = p.base.v
    rw [hp, inv_one, one_smul]
    exact neg_eq_of_add_eq_zero_left (hV₂ _)
  refine ⟨Sd.ext hbv (by show p.base.cc⁻¹ = p.base.cc; rw [hp, inv_one]), ?_⟩
  show p.fib + (kappa0Cocycle dat hdat).κ p.base p.base⁻¹ = p.fib + q p.base.v
  rw [kappa0_cc_one dat hdat _ _ hp, hbv, hdat.f_diag]

/-- **The `V`-slice commutator fibre is the polar form** (the `[d₀,z₀]`-cell): for
`CentExt κ⁰`-elements over `cc = 1` bases, `commP` has base `1` and fibre
`polar q` of the `V`-parts. -/
theorem commP_fib_cc_one (p r : CentExt (kappa0Cocycle dat hdat))
    (hp : p.base.cc = 1) (hr : r.base.cc = 1) (hV₂ : ∀ w : V, w + w = 0) :
    (commP p r).fib = polar q p.base.v r.base.v := by
  obtain ⟨hpib, hpif⟩ := inv_cc_one dat hdat p hp hV₂
  obtain ⟨hrib, hrif⟩ := inv_cc_one dat hdat r hr hV₂
  set a := p.base.v with ha
  set b := r.base.v with hb
  -- the four-step peel
  have h1 : (p⁻¹ * r⁻¹).fib = (p.fib + q a) + (r.fib + q b) + dat.f a b := by
    rw [CentExt.mul_fib, hpif, hrif, hpib, hrib, kappa0_cc_one dat hdat _ _ hp]
  have h1b : (p⁻¹ * r⁻¹).base.v = a + b := by
    show (p⁻¹.base * r⁻¹.base).v = a + b
    rw [hpib, hrib]
    show a + p.base.cc • b = a + b
    rw [hp, one_smul]
  have h1c : (p⁻¹ * r⁻¹).base.cc = 1 := by
    show (p⁻¹.base * r⁻¹.base).cc = 1
    rw [hpib, hrib]
    show p.base.cc * r.base.cc = 1
    rw [hp, hr, one_mul]
  have h2 : (p⁻¹ * r⁻¹ * p).fib
      = ((p.fib + q a) + (r.fib + q b) + dat.f a b) + p.fib + dat.f (a + b) a := by
    rw [CentExt.mul_fib, h1, kappa0_cc_one dat hdat _ _ h1c, h1b]
  have h2b : (p⁻¹ * r⁻¹ * p).base.v = b := by
    show ((p⁻¹ * r⁻¹).base * p.base).v = b
    show (p⁻¹ * r⁻¹).base.v + (p⁻¹ * r⁻¹).base.cc • a = b
    rw [h1b, h1c, one_smul]
    rw [show a + b + a = b + (a + a) from by abel, hV₂ a, add_zero]
  have h2c : (p⁻¹ * r⁻¹ * p).base.cc = 1 := by
    show ((p⁻¹ * r⁻¹).base * p.base).cc = 1
    show (p⁻¹ * r⁻¹).base.cc * p.base.cc = 1
    rw [h1c, hp, one_mul]
  show (p⁻¹ * r⁻¹ * p * r).fib = polar q a b
  rw [CentExt.mul_fib, h2, kappa0_cc_one dat hdat _ _ h2c, h2b, ← hb, hdat.f_diag b]
  -- the target is now linear over `ZMod 2` in the `f`-atoms; two cocycle instances + polar
  have hc1 : dat.f (a + b) a + dat.f a b = dat.f a (b + a) + dat.f b a := hdat.f_cocycle a b a
  rw [add_comm b a] at hc1
  have hc1' : dat.f (a + a) b + dat.f a a = dat.f a (a + b) + dat.f a b := hdat.f_cocycle a a b
  rw [hV₂ a, hdat.f_zero_left, hdat.f_diag] at hc1'
  have hpol : dat.f a b + dat.f b a = polar q a b := hdat.f_polar a b
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]; try ring_nf))
    hc1 + hc1' + hpol

/-- **The ramified wild κ⁰-value is the Wall double** (paper (83), `V^T = 0` case): with
the structural pack, the lifted wild relator value has fibre
`q(x₀.v) + polar q x₀.v (σ₂⁻¹ • x₀.v)`.  Unlike the split case `d₀` is no longer central —
it carries the `V`-coordinate `x₀.v` (the banked ramified row `liftMarking_d0_u_ramified`) —
but every `h₀`-factor stays in the abelian `V`-slice (`cc = 1`), so the peel proceeds by
`kappa0_cc_one` steps: the `[d₀,z₀]`-commutator `c₀` contributes the polar term
(`commP_fib_cc_one`), and the `h₀`-telescope closes on `q(g₀⁻¹ • x₀.v) = q(x₀.v)` by the
`q`-invariance hypothesis `hqg0`. -/
theorem liftMark_kappa0_wildValue_fib_ramified [Finite C] [Finite V]
    (tS : Marking (Sd C V))
    (hσv : tS.σ.v = 0) (hτv : tS.τ.v = 0) (hx1v : tS.x₁.v = 0)
    (hx0cc : tS.x₀.cc = 1) (hx1cc : tS.x₁.cc = 1)
    (hV₂ : ∀ w : V, w + w = 0)
    (htauf : ∀ w : V, tS.τ.cc • w = w → w = 0)
    (hτodd : Odd (orderOf tS.τ.cc))
    (hqg0 : q ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) = q tS.x₀.v) :
    (liftMark tS (kappa0Cocycle dat hdat)).wildValue.fib
      = q tS.x₀.v + polar q tS.x₀.v ((Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₀.v) := by
  classical
  set M := liftMark tS (kappa0Cocycle dat hdat) with hM
  -- generator slot forms
  have hMx1 : M.x₁ = 1 := CentExt.ext (Sd.ext hx1v hx1cc) rfl
  have hMτ : M.τ = sdSec dat hdat tS.τ.cc := CentExt.ext (Sd.ext hτv rfl) rfl
  have hMσ : M.σ = sdSec dat hdat tS.σ.cc := CentExt.ext (Sd.ext hσv rfl) rfl
  have hMx0bv : M.x₀.base.v = tS.x₀.v := rfl
  have hMx0bcc : M.x₀.base.cc = tS.x₀.cc := rfl
  have hMx0f : M.x₀.fib = 0 := rfl
  -- `u₁ = 1` and `x₁^σ = 1` (as in the split case)
  have hu1 : M.u1 = 1 := by
    show powOmega2 (M.x₁ * M.τ) = 1
    rw [hMx1, one_mul, hMτ, ← powOmega2_map, powOmega2_eq_one_of_odd hτodd, map_one]
  have hx1s : conjP M.x₁ M.σ = 1 := by
    rw [conjP, hMx1, mul_one, inv_mul_cancel]
  -- `d₀.base = (x₀.v, 1)`: the `cc`-part as in the split case; the `v`-part is the banked
  -- RAMIFIED row (`= x 2`, the `x₀`-slot)
  have hd0cc : tS.d0.cc = 1 := by
    have h := (Marking.map_d0 (sdCcHom (C := C) (V := V)) tS).symm
    rw [show tS.map (sdCcHom (C := C) (V := V)) = sdBaseMarking tS from rfl] at h
    show sdCcHom (C := C) (V := V) tS.d0 = 1
    rw [h]
    show powOmega2 (tS.x₀.cc * tS.τ.cc) * (tS.x₀.cc)⁻¹ = 1
    rw [hx0cc, one_mul, inv_one, mul_one, powOmega2_eq_one_of_odd hτodd]
  have hd0v : tS.d0.v = tS.x₀.v := by
    rw [sd_d0_v, liftMarking_d0_u_ramified (sdBaseMarking tS) (sdOffsets tS) hV₂
      (fun w => by show tS.x₀.cc • w = w; rw [hx0cc, one_smul]) htauf
      (fun w => by
        show powOmega2 tS.τ.cc • w = w
        rw [powOmega2_eq_one_of_odd hτodd, one_smul])]
    rfl
  have hd0bv : M.d0.base.v = tS.x₀.v := by
    show ((liftMark tS (kappa0Cocycle dat hdat)).d0).base.v = tS.x₀.v
    rw [liftMark_d0_base dat hdat tS]
    exact hd0v
  have hd0bcc : M.d0.base.cc = 1 := by
    show ((liftMark tS (kappa0Cocycle dat hdat)).d0).base.cc = 1
    rw [liftMark_d0_base dat hdat tS]
    exact hd0cc
  -- `σ₂` and `g₀` are base-slice section values
  have hs2 : M.sigma2 = sdSec dat hdat (Marking.sigma2 (sdBaseMarking tS)) := by
    show powOmega2 M.σ = _
    rw [hMσ, ← powOmega2_map]
    rfl
  have hMg0 : M.g0 = sdSec dat hdat (Marking.g0 (sdBaseMarking tS)) := by
    show M.sigma2 ^ 2 = _
    rw [hs2, ← map_pow]
    rfl
  -- `z₀`: base `(σ₂⁻¹ • x₀.v, 1)`
  have hz0v : M.z0.base.v = (Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₀.v := by
    show (conjP M.x₀ M.sigma2).base.v = _
    rw [hs2, conjP_sdSec_base, sd_conjP_v, hMx0bv]
  have hz0cc : M.z0.base.cc = 1 := by
    show (conjP M.x₀ M.sigma2).base.cc = 1
    rw [hs2, conjP_sdSec_base]
    show (Marking.sigma2 (sdBaseMarking tS))⁻¹ * tS.x₀.cc * Marking.sigma2 (sdBaseMarking tS)
      = 1
    rw [hx0cc, mul_one, inv_mul_cancel]
  -- `c₀ = [d₀,z₀]`: the polar-form cell
  have hc0f : M.c0.fib
      = polar q tS.x₀.v ((Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₀.v) := by
    show (commP M.d0 M.z0).fib = _
    rw [commP_fib_cc_one dat hdat M.d0 M.z0 hd0bcc hz0cc hV₂, hd0bv, hz0v]
  -- the `x₀^{g₀}`-cell
  have hAv : (conjP M.x₀ M.g0).base.v = (Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v := by
    rw [hMg0, conjP_sdSec_base, sd_conjP_v, hMx0bv]
  have hAcc : (conjP M.x₀ M.g0).base.cc = 1 := by
    rw [hMg0, conjP_sdSec_base]
    show (Marking.g0 (sdBaseMarking tS))⁻¹ * tS.x₀.cc * Marking.g0 (sdBaseMarking tS) = 1
    rw [hx0cc, mul_one, inv_mul_cancel]
  have hAf : (conjP M.x₀ M.g0).fib
      = dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v := by
    rw [hMg0, conjP_sdSec_fib, hMx0f, hMx0bv, zero_add]
  -- the `d_g`-cell
  have hdgv : M.dg.base.v = (Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v := by
    show (conjP M.d0 M.g0).base.v = _
    rw [hMg0, conjP_sdSec_base, sd_conjP_v, hd0bv]
  have hdgcc : M.dg.base.cc = 1 := by
    show (conjP M.d0 M.g0).base.cc = 1
    rw [hMg0, conjP_sdSec_base]
    show (Marking.g0 (sdBaseMarking tS))⁻¹ * M.d0.base.cc * Marking.g0 (sdBaseMarking tS) = 1
    rw [hd0bcc, mul_one, inv_mul_cancel]
  have hdgf : M.dg.fib
      = M.d0.fib + dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v := by
    show (conjP M.d0 M.g0).fib = _
    rw [hMg0, conjP_sdSec_fib, hd0bv]
  -- the `h_c`-cell (slice commutator)
  have hhcbase : M.hc.base = 1 := by
    show (commP M.dg M.d0).base = 1
    rw [show (commP M.dg M.d0).base = commP M.dg.base M.d0.base from rfl]
    exact sd_commP_cc_one M.dg.base M.d0.base hdgcc hd0bcc
  have hhcf : M.hc.fib
      = polar q ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v := by
    show (commP M.dg M.d0).fib = _
    rw [commP_fib_cc_one dat hdat M.dg M.d0 hdgcc hd0bcc hV₂, hdgv, hd0bv]
  -- the `h₀`-peel, prefix by prefix (all factors in the `V`-slice)
  have hP1v : (conjP M.x₀ M.g0 * M.x₀).base.v
      = (Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v + tS.x₀.v := by
    rw [CentExt.mul_base, Sd.mul_v, hAv, hAcc, one_smul, hMx0bv]
  have hP1cc : (conjP M.x₀ M.g0 * M.x₀).base.cc = 1 := by
    rw [CentExt.mul_base, Sd.mul_cc, hAcc, one_mul, hMx0bcc, hx0cc]
  have hP1f : (conjP M.x₀ M.g0 * M.x₀).fib
      = dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v := by
    rw [CentExt.mul_fib, hAf, hMx0f, add_zero, kappa0_cc_one dat hdat _ _ hAcc, hAv, hMx0bv]
  have hP2v : (conjP M.x₀ M.g0 * M.x₀ * M.dg).base.v = tS.x₀.v := by
    rw [CentExt.mul_base, Sd.mul_v, hP1v, hP1cc, one_smul, hdgv,
      show (Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v + tS.x₀.v
          + (Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v
        = tS.x₀.v + ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v
          + (Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) from by abel,
      hV₂ ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v), add_zero]
  have hP2cc : (conjP M.x₀ M.g0 * M.x₀ * M.dg).base.cc = 1 := by
    rw [CentExt.mul_base, Sd.mul_cc, hP1cc, hdgcc, one_mul]
  have hP2f : (conjP M.x₀ M.g0 * M.x₀ * M.dg).fib
      = dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
        + (M.d0.fib + dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v)
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v + tS.x₀.v)
            ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) := by
    rw [CentExt.mul_fib, hP1f, hdgf, kappa0_cc_one dat hdat _ _ hP1cc, hP1v, hdgv]
  have hP3v : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).base.v = 0 := by
    rw [CentExt.mul_base, Sd.mul_v, hP2v, hP2cc, one_smul, hd0bv]
    exact hV₂ tS.x₀.v
  have hP3cc : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).base.cc = 1 := by
    rw [CentExt.mul_base, Sd.mul_cc, hP2cc, hd0bcc, one_mul]
  have hP3f : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0).fib
      = dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
        + (M.d0.fib + dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v)
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v + tS.x₀.v)
            ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v)
        + M.d0.fib + q tS.x₀.v := by
    rw [CentExt.mul_fib, hP2f, kappa0_cc_one dat hdat _ _ hP2cc, hP2v, hd0bv, hdat.f_diag]
  have hd0sqv : (M.d0 ^ 2).base.v = 0 := by
    rw [pow_two, CentExt.mul_base, Sd.mul_v, hd0bv, hd0bcc, one_smul]
    exact hV₂ tS.x₀.v
  have hd0sqcc : (M.d0 ^ 2).base.cc = 1 := by
    rw [pow_two, CentExt.mul_base, Sd.mul_cc, hd0bcc, one_mul]
  have hd0sqf : (M.d0 ^ 2).fib = q tS.x₀.v := by
    rw [pow_two, CentExt.mul_fib, kappa0_cc_one dat hdat _ _ hd0bcc, hd0bv, hdat.f_diag,
      CharTwo.add_self_eq_zero, zero_add]
  have hP4v : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).base.v = 0 := by
    rw [CentExt.mul_base, Sd.mul_v, hP3v, hP3cc, one_smul, hd0sqv, add_zero]
  have hP4cc : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).base.cc = 1 := by
    rw [CentExt.mul_base, Sd.mul_cc, hP3cc, hd0sqcc, one_mul]
  have hP4f : (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2).fib
      = dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
        + (M.d0.fib + dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v)
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v + tS.x₀.v)
            ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v)
        + M.d0.fib + q tS.x₀.v + q tS.x₀.v := by
    rw [CentExt.mul_fib, hP3f, hd0sqf, kappa0_cc_one dat hdat _ _ hP3cc, hP3v,
      hdat.f_zero_left, add_zero]
  have hh0bv : M.h0.base.v = 0 := by
    show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).base.v = 0
    rw [CentExt.mul_base, Sd.mul_v, hP4v, hP4cc, one_smul, hhcbase, Sd.one_v, add_zero]
  have hh0bcc : M.h0.base.cc = 1 := by
    show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).base.cc = 1
    rw [CentExt.mul_base, Sd.mul_cc, hP4cc, hhcbase, Sd.one_cc, one_mul]
  have hh0f : M.h0.fib
      = dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
        + (M.d0.fib + dat.m (Marking.g0 (sdBaseMarking tS))⁻¹ tS.x₀.v)
        + dat.f ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v + tS.x₀.v)
            ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v)
        + M.d0.fib + q tS.x₀.v + q tS.x₀.v
        + polar q ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v := by
    show (conjP M.x₀ M.g0 * M.x₀ * M.dg * M.d0 * M.d0 ^ 2 * M.hc).fib = _
    rw [CentExt.mul_fib, hP4f, hhcf, kappa0_cc_one dat hdat _ _ hP4cc, hP4v,
      hdat.f_zero_left, add_zero]
  -- assemble the wild word
  show (M.h0 * M.u1⁻¹ * conjP M.x₁ M.σ * M.c0).fib
      = q tS.x₀.v + polar q tS.x₀.v ((Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₀.v)
  rw [hu1, hx1s, inv_one, mul_one, mul_one, CentExt.mul_fib, hh0f, hc0f,
    kappa0_cc_one dat hdat _ _ hh0bcc, hh0bv, hdat.f_zero_left, add_zero]
  -- the `ZMod 2` finale: two cocycle instances + the polar identity + `q`-invariance
  have hcoc1 := hdat.f_cocycle ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
    ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v)
  have hcoc2 := hdat.f_cocycle ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v)
    ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
  rw [hV₂ ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v), hdat.f_zero_left, hdat.f_diag,
    add_comm ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v] at hcoc2
  have hpol := hdat.f_polar ((Marking.g0 (sdBaseMarking tS))⁻¹ • tS.x₀.v) tS.x₀.v
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]; try ring_nf))
    hcoc1 + hcoc2 + hpol + hqg0

end Kappa0Ledger

/-! ## A-4.5 bricks: the `V`-indexed signed count and the `qDouble` orientation bridge

En-free pieces of the seam assembly: the `finsum_sign_eq` extraction re-indexed by a plain
finite type (the `x₀`-supported section makes the Gauss domain literally `V`), its two
pinned-count finales (`∓2^m`), and the `U⁻¹`/`U` orientation identification that matches
A-4.4b's Wall double to `qDouble`. -/

section CountBricks

/-- The signed-sum extraction over a plain finite type: with `zeroCount q` and `#V` known,
`∑ᶠ sign(q v) = 2·zeroCount − #V` (the `GaussZLocal.finsum_sign_eq` shape, En-free). -/
theorem finsum_sign_eq_count {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2)
    (zc : ℕ) (hzc : zeroCount q = zc) {n : ℕ} (hn : Nat.card V = n) :
    ∑ᶠ v : V, sign (q v) = 2 * (zc : ℤ) - n := by
  classical
  haveI : Fintype V := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  have hsign : ∀ s : ZMod 2, sign s = QuadraticFp2.sign s := by decide
  calc (∑ v : V, sign (q v))
      = ∑ v : V, QuadraticFp2.sign (q v) := Finset.sum_congr rfl fun v _ => hsign _
    _ = 2 * (zc : ℤ) - n := by
        have hge := gaussSum_eq (V := V) q
        unfold QuadraticFp2.gaussSum at hge
        rw [hge, hzc, ← Nat.card_eq_fintype_card, hn]

/-- **The minus finale**: `∑ᶠ sign = −2^m` from the unramified zero count
`2^{2m−1} − 2^{m−1}` (`prop_6_9_unramified` / `zeroCount_of_arf_one`'s value). -/
theorem finsum_sign_eq_neg_of_zeroCount {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2)
    (m : ℕ) (hm : 1 ≤ m) (hzc : zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1))
    (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (q v) = -(2 ^ m : ℤ) := by
  rw [finsum_sign_eq_count q _ hzc hcard]
  have hle : (2 : ℕ) ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast [Nat.cast_sub hle]
  linarith [e1, e2]

/-- **The plus finale**: `∑ᶠ sign = +2^m` from the ramified zero count
`2^{2m−1} + 2^{m−1}` (`prop_6_9_ramified` / `zeroCount_of_arf_zero`'s value). -/
theorem finsum_sign_eq_pos_of_zeroCount {V : Type*} [AddCommGroup V] [Finite V] (q : V → ZMod 2)
    (m : ℕ) (hm : 1 ≤ m) (hzc : zeroCount q = 2 ^ (2 * m - 1) + 2 ^ (m - 1))
    (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (q v) = (2 ^ m : ℤ) := by
  rw [finsum_sign_eq_count q _ hzc hcard]
  have e1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast
  linarith [e1, e2]

/-- **The `qDouble` orientation bridge**: for `q` invariant under `U`, the Wall-double twist
reads the same with `U⁻¹` as with `U` — `B(x, U⁻¹•x) = B(x, U•x)` — so A-4.4b's value
`q(v) + B(v, σ₂⁻¹•v)` IS `qDouble q (σ₂ • ·)` at `v`. -/
theorem polar_smul_inv_eq {C : Type*} [Group C] {V : Type*} [AddCommGroup V]
    [DistribMulAction C V] (q : V → ZMod 2) (U : C) (hUq : ∀ v : V, q (U • v) = q v)
    (x : V) : polar q x (U⁻¹ • x) = polar q x (U • x) := by
  have h1 : q (U⁻¹ • x) = q x := by rw [← hUq (U⁻¹ • x), smul_inv_smul]
  have h2 : q (x + U⁻¹ • x) = q (x + U • x) := by
    calc q (x + U⁻¹ • x) = q (U • (x + U⁻¹ • x)) := (hUq _).symm
      _ = q (U • x + x) := by rw [smul_add, smul_inv_smul]
      _ = q (x + U • x) := by rw [add_comm]
  show q (x + U⁻¹ • x) + q x + q (U⁻¹ • x) = q (x + U • x) + q x + q (U • x)
  rw [h2, h1, hUq x]

end CountBricks

/-! ## The even-dimension fact: nonsingular ⟹ `#V = 2^{2m}`

The c3-G0 package needs `#V = 2^{2m}` — the classical symplectic fact that a nonsingular
alternating pairing forces even dimension, in counting form: split off a hyperbolic pair
`(v, w)` through the surjective pairing hom `u ↦ (B(u,v), B(u,w))` onto `𝔽₂²`; the kernel
is the perpendicular complement, of index exactly `4`, and stays nonsingular. -/

section EvenCard

universe u

theorem card_eq_two_pow_two_mul_of_nonsingular {V : Type u} [AddCommGroup V] [Finite V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hV₂ : ∀ v : V, v + v = 0) :
    ∃ m : ℕ, Nat.card V = 2 ^ (2 * m) := by
  suffices h : ∀ n : ℕ, ∀ (V : Type u) (_ : AddCommGroup V) (_ : Finite V),
      ∀ q : V → ZMod 2, IsQuadraticFp2 q → Nonsingular q → (∀ v : V, v + v = 0) →
      Nat.card V = n → ∃ m : ℕ, Nat.card V = 2 ^ (2 * m) by
    exact h (Nat.card V) V ‹_› ‹_› q hq hns hV₂ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V instG instF q hq hns hV₂ hn
    by_cases hV : ∃ v : V, v ≠ 0
    case neg =>
      push Not at hV
      haveI : Subsingleton V := ⟨fun a b => by rw [hV a, hV b]⟩
      haveI : Inhabited V := ⟨0⟩
      exact ⟨0, by rw [Nat.card_unique]; decide⟩
    case pos =>
      obtain ⟨v, hv⟩ := hV
      obtain ⟨w, hw⟩ := hns v hv
      have hBvw : polar q v w = 1 :=
        ((show ∀ x : ZMod 2, x = 0 ∨ x = 1 by decide) (polar q v w)).resolve_left hw
      have hpz : ∀ x : V, polar q 0 x = 0 := fun x => by
        have h := hq.polar_add_left 0 0 x
        rwa [add_zero, CharTwo.add_self_eq_zero] at h
      -- the pairing hom onto `𝔽₂²`
      set φ : V →+ ZMod 2 × ZMod 2 :=
        { toFun := fun u => (polar q u v, polar q u w)
          map_zero' := by rw [hpz v, hpz w]; rfl
          map_add' := fun a b => by
            show (polar q (a + b) v, polar q (a + b) w) = _
            rw [hq.polar_add_left a b v, hq.polar_add_left a b w]
            rfl } with hφdef
      have hφv : φ v = ((0 : ZMod 2), (1 : ZMod 2)) := by
        show (polar q v v, polar q v w) = _
        rw [polar_self q hq hV₂ v, hBvw]
      have hφw : φ w = ((1 : ZMod 2), (0 : ZMod 2)) := by
        show (polar q w v, polar q w w) = _
        rw [polar_comm q w v, hBvw, polar_self q hq hV₂ w]
      have hφsurj : Function.Surjective ⇑φ := by
        intro p
        rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) p.1 with h1 | h1 <;>
          rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) p.2 with h2 | h2
        · refine ⟨0, ?_⟩
          rw [map_zero]
          exact (Prod.ext h1 h2).symm
        · refine ⟨v, ?_⟩
          rw [hφv]
          exact (Prod.ext h1 h2).symm
        · refine ⟨w, ?_⟩
          rw [hφw]
          exact (Prod.ext h1 h2).symm
        · refine ⟨v + w, ?_⟩
          rw [map_add, hφv, hφw,
            show ((0 : ZMod 2), (1 : ZMod 2)) + ((1 : ZMod 2), (0 : ZMod 2))
              = ((1 : ZMod 2), (1 : ZMod 2)) from by decide]
          exact (Prod.ext h1 h2).symm
      set K := φ.ker with hKdef
      -- the index-4 count
      have hcardV : Nat.card V = 4 * Nat.card ↥K := by
        have h1 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (s := K)
        have h2 : Nat.card (V ⧸ K) = 4 := by
          rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv,
            Nat.card_eq_fintype_card]
          decide
        rw [h1, h2]
      -- the kernel inherits the structure
      have hV₂K : ∀ u : ↥K, u + u = 0 := fun u => Subtype.ext (hV₂ u.1)
      have hqK : IsQuadraticFp2 (fun u : ↥K => q u.1) := by
        refine ⟨hq.map_zero, ?_, ?_⟩
        · intro a b c
          exact hq.polar_add_left a.1 b.1 c.1
        · intro a b c
          exact hq.polar_add_right a.1 b.1 c.1
      -- the correction into the perpendicular complement
      have hcorr : ∀ x : V, ∃ x' : V, polar q x' v = 0 ∧ polar q x' w = 0 ∧
          ∀ u : V, polar q u v = 0 → polar q u w = 0 →
            polar q u x' = polar q u x := by
        intro x
        rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (polar q x v) with h1 | h1 <;>
          rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide) (polar q x w) with h2 | h2
        · exact ⟨x, h1, h2, fun u _ _ => rfl⟩
        · -- `(B(x,v), B(x,w)) = (0,1)`: correct by `v`
          refine ⟨x + v, ?_, ?_, ?_⟩
          · rw [hq.polar_add_left, h1, polar_self q hq hV₂, add_zero]
          · rw [hq.polar_add_left, h2, hBvw]
            decide
          · intro u hu1 hu2
            rw [hq.polar_add_right, hu1, add_zero]
        · -- `(1,0)`: correct by `w`
          refine ⟨x + w, ?_, ?_, ?_⟩
          · rw [hq.polar_add_left, h1, polar_comm q w v, hBvw]
            decide
          · rw [hq.polar_add_left, h2, polar_self q hq hV₂ w, add_zero]
          · intro u hu1 hu2
            rw [hq.polar_add_right, hu2, add_zero]
        · -- `(1,1)`: correct by `v + w`
          refine ⟨x + (v + w), ?_, ?_, ?_⟩
          · rw [hq.polar_add_left, h1, hq.polar_add_left, polar_self q hq hV₂,
              polar_comm q w v, hBvw]
            decide
          · rw [hq.polar_add_left, h2, hq.polar_add_left, hBvw, polar_self q hq hV₂]
            decide
          · intro u hu1 hu2
            rw [hq.polar_add_right, hq.polar_add_right, hu1, hu2, add_zero, add_zero]
      -- the kernel stays nonsingular
      have hnsK : Nonsingular (fun u : ↥K => q u.1) := by
        intro u hu
        have hu1 : (u : V) ≠ 0 := fun h => hu (Subtype.ext h)
        obtain ⟨x, hx⟩ := hns u.1 hu1
        obtain ⟨x', hx'v, hx'w, hx'pair⟩ := hcorr x
        have hker : φ u.1 = 0 := AddMonoidHom.mem_ker.mp u.2
        have huv : polar q u.1 v = 0 := congrArg Prod.fst hker
        have huw : polar q u.1 w = 0 := congrArg Prod.snd hker
        have hx'mem : x' ∈ K := AddMonoidHom.mem_ker.mpr (by
          show (polar q x' v, polar q x' w) = 0
          rw [hx'v, hx'w]
          rfl)
        refine ⟨⟨x', hx'mem⟩, ?_⟩
        show polar q u.1 x' ≠ 0
        rw [hx'pair u.1 huv huw]
        exact hx
      -- recurse on the kernel
      have hKpos : 0 < Nat.card ↥K := Nat.card_pos
      have hKlt : Nat.card ↥K < n := by
        rw [hcardV] at hn
        omega
      obtain ⟨m, hm⟩ := ih (Nat.card ↥K) hKlt ↥K inferInstance inferInstance
        (fun u : ↥K => q u.1) hqK hnsK hV₂K rfl
      refine ⟨m + 1, ?_⟩
      rw [hcardV, hm, show 2 * (m + 1) = 2 * m + 2 from by ring, pow_add]
      ring

/-- The consumer form: with a nonzero vector, `#V = 2^{2m}` with `m ≥ 1` — the c3-G0
package's cardinality field, derived from the enrichment's nonsingular form. -/
theorem exists_one_le_card_eq_two_pow_of_nonsingular {V : Type*} [AddCommGroup V]
    [Finite V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hV₂ : ∀ v : V, v + v = 0) (hVne : ∃ v : V, v ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card V = 2 ^ (2 * m) := by
  obtain ⟨m, hm⟩ := card_eq_two_pow_two_mul_of_nonsingular q hq hns hV₂
  refine ⟨m, ?_, hm⟩
  rcases Nat.eq_zero_or_pos m with rfl | h
  · exfalso
    obtain ⟨v, hv⟩ := hVne
    have h1 : Nat.card V = 1 := by simpa using hm
    haveI : Subsingleton V := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hv (Subsingleton.elim v 0)
  · exact h

end EvenCard

/-! ## A-4.5b: the actionization — counts at the faithful quotient

The SectionSix count pins (`prop_6_9_*`) take faithfulness and the ELEMENT-level tame
dichotomy, neither of which the seam has (`hfaith` is not block-derivable — the e6/e7
amendment).  The resolution: quotient the acting group by the action kernel.  The induced
action of `C ⧸ K` has the same orbit values (so `hsimple`/`hinv` transport verbatim), is
faithful BY CONSTRUCTION (`kerLift_injective`-shaped), and converts the action-level
dichotomy into the element-level one (`c' τ = 1 ⟺ c τ acts trivially`). -/

section Actionization

/-- **The unramified zero count from action-level hypotheses** (`prop_6_9_unramified`
through the faithful quotient): no `hfaith`, and `hunram` in the action form the seam
carries. -/
theorem zeroCount_unramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  classical
  -- the action kernel, directly as the acts-trivially subgroup
  set K : Subgroup C :=
    { carrier := {g : C | ∀ v : V, g • v = v}
      one_mem' := fun v => one_smul C v
      mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
      inv_mem' := fun {a} ha v => inv_smul_eq_iff.mpr (ha v).symm } with hK
  haveI hKn : K.Normal :=
    ⟨fun a ha g v => by rw [mul_smul, mul_smul, ha (g⁻¹ • v), smul_inv_smul]⟩
  letI instTQ : TopologicalSpace (C ⧸ K) := ⊥
  haveI instDQ : DiscreteTopology (C ⧸ K) := ⟨rfl⟩
  -- the descended action of the faithful quotient (same values on every class)
  letI instAQ : DistribMulAction (C ⧸ K) V :=
    { smul := fun x v => Quotient.liftOn' x (fun g => g • v) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab
        show a • v = b • v
        have hb : b = a * (a⁻¹ * b) := by group
        rw [hb, mul_smul, hab v])
      one_smul := fun v => one_smul C v
      mul_smul := fun x y v => Quotient.inductionOn₂' x y fun a b => mul_smul a b v
      smul_zero := fun x => Quotient.inductionOn' x fun a => smul_zero a
      smul_add := fun x v w => Quotient.inductionOn' x fun a => smul_add a v w }
  have hval : ∀ (g : C) (v : V), (QuotientGroup.mk g : C ⧸ K) • v = g • v :=
    fun g v => rfl
  -- the induced tame marking (continuity is free from the discrete source)
  set c' : ContinuousMonoidHom Ttame (C ⧸ K) :=
    ⟨(QuotientGroup.mk' K).comp c.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑(QuotientGroup.mk' K))).comp
        c.continuous_toFun⟩ with hc'
  have hc'surj : Function.Surjective ⇑c' := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨t, ht⟩ := hc x
    exact ⟨t, by show QuotientGroup.mk' K (c t) = _; rw [ht]⟩
  -- faithfulness by construction
  have hfaith' : ∀ g : C ⧸ K, (∀ v : V, g • v = v) → g = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [QuotientGroup.eq_one_iff]
    exact fun v => (hval x v).symm.trans (hg v)
  -- the ledger hypotheses transport verbatim (same action values)
  have hsimple' : ∀ W : AddSubgroup V,
      (∀ (g : C ⧸ K), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hsimple W (fun g w hw => by
      have h := hW (QuotientGroup.mk g) w hw
      rwa [hval] at h)
  have hinv' : IsInvariant (C ⧸ K) q := by
    intro g v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hval]
    exact hinv x v
  -- the action-level dichotomy becomes the element-level one
  have hunram' : c' tameTau = 1 := by
    show QuotientGroup.mk' K (c tameTau) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hunram
  exact SectionSix.prop_6_9_unramified c' hc'surj hfaith' hsimple' hV hunram'
    q hq hns hinv' m hm hcard

/-- **The unramified `V`-sum**: `∑ᶠ sign(q̄ v) = −2^m` from action-level hypotheses — the
value the unramified seam consumes after the `x₀`-supported section reindex. -/
theorem finsum_sign_unramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (q v) = -(2 ^ m : ℤ) :=
  finsum_sign_eq_neg_of_zeroCount q m hm
    (zeroCount_unramified_of_action c hc hsimple hV hunram q hq hns hinv m hm hcard) hcard

/-- **THE RAMIFIED PACK, DISCHARGED** (P-16d6e4aA-P3): `prop_6_9_ramified`'s isotypic pack
`(s r a Wt e he hVU hrank)` derived from the faithful simple ramified hypotheses via
`GQ2/RamifiedPack.lean` — the single isotype `P ∣ X^d − 1` (`exists_single_isotype`), the free
`D = AdjoinRoot P`-structure `V ≃+ D^{sV}` (`exists_isotypic_equiv`), `f = deg P` even by the
polar-adjoint involution (`even_natDegree_of_aeval_inv_eq_zero`), the `⟨cτ⟩`-module `Wt := D`
(`rootAction`/`adjoinRoot_add_self`/`isSimpleModTwo_rootAction`/`equiv_zpowers_smul`), the
σ-semilinear descent count `#V^U = 2^{r·sV}` (`card_fixed_powOmega2`), and the rank parity from
the first isomorphism theorem. -/
theorem zeroCount_qDouble_ramified_of_faithful {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : c tameTau ≠ 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 (c tameSigma) • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  -- the standing tame facts
  have hgen : Subgroup.closure ({c tameSigma, c tameTau} : Set C) = ⊤ :=
    SectionThree.gen_ttame_quotient c.toMonoidHom c.continuous_toFun hc
  have hrelC : (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 := by
    have hrel := congrArg (⇑c) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using hrel
  have hoddC : Odd (orderOf (c tameTau)) := LocalKummer.odd_orderOf_tameInertia c
  have hposT : 0 < orderOf (c tameTau) := orderOf_pos _
  have hV2 : ∀ v : V, v + v = 0 := by
    -- the 2-torsion subgroup is `C`-stable and nonzero (additive Cauchy), hence `⊤`
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set T : AddSubgroup V :=
      { carrier := {v : V | v + v = 0}
        zero_mem' := by
          show (0 : V) + 0 = 0
          rw [add_zero]
        add_mem' := fun {u₁ u₂} h1 h2 => by
          show (u₁ + u₂) + (u₁ + u₂) = 0
          calc (u₁ + u₂) + (u₁ + u₂) = (u₁ + u₁) + (u₂ + u₂) := by abel
            _ = 0 := by rw [show u₁ + u₁ = 0 from h1, show u₂ + u₂ = 0 from h2, add_zero]
        neg_mem' := fun {u} h => by
          show -u + -u = 0
          calc -u + -u = -(u + u) := by abel
            _ = 0 := by rw [show u + u = 0 from h, neg_zero] } with hT
    have hstab : ∀ g : C, ∀ w ∈ T, g • w ∈ T := by
      intro g w hw
      show g • w + g • w = 0
      rw [← smul_add, show w + w = 0 from hw, smul_zero]
    have h2card : (2 : ℕ) ∣ Nat.card V := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨v₀, hv₀⟩ := exists_prime_addOrderOf_dvd_card' 2 h2card
    have hv₀mem : v₀ ∈ T := by
      show v₀ + v₀ = 0
      have := addOrderOf_nsmul_eq_zero v₀
      rwa [hv₀, two_nsmul] at this
    have hv₀ne : v₀ ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at hv₀
      omega
    rcases hsimple T hstab with hbot | htop
    · exact absurd (hbot ▸ hv₀mem) (fun hm' => hv₀ne (AddSubgroup.mem_bot.mp hm'))
    · exact fun v => htop.ge (AddSubgroup.mem_top v)
  have hVne : ∃ v : V, v ≠ 0 := by
    have h1 : 1 < Nat.card V := by
      rw [hcard]
      exact Nat.one_lt_two_pow_iff.mpr (by omega)
    haveI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne 0
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV2 v)
  -- the single isotype and the free `D`-structure
  obtain ⟨P, hmon, hirr, hdvdP, hkill⟩ := RamifiedPack.exists_single_isotype
    (c tameSigma) (c tameTau) hgen hrelC hoddC hposT hsimple hVne
  haveI := Fact.mk hirr
  obtain ⟨sV, e, hs1, he⟩ := RamifiedPack.exists_isotypic_equiv (c tameTau) P hirr hkill hVne
  -- root facts
  have hroot0 : AdjoinRoot.root P ≠ 0 := RamifiedPack.root_ne_zero (c tameTau) P hposT hdvdP
  have hroot1 : AdjoinRoot.root P ≠ 1 := by
    intro h1
    refine hram ?_
    have hx : AdjoinRoot.root P ^ 1 = AdjoinRoot.root P ^ 0 := by
      rw [pow_one, pow_zero, h1]
    have ht := RamifiedPack.t_pow_eq_of_root_pow_eq (c tameTau) P hfaith hx e he
    rwa [pow_one, pow_zero] at ht
  -- `f = deg P` is even, `f = 2^a·r`
  have hqt : ∀ v : V, q (c tameTau • v) = q v := fun v => hinv (c tameTau) v
  have hkill' := RamifiedPack.aeval_actEnd_inv_eq_zero (c tameTau) q hq hns hqt hkill
  have h0 := RamifiedPack.aeval_root_inv_eq_zero (c tameTau) P hroot0 hs1 e he hkill'
  have heven := RamifiedPack.even_natDegree_of_aeval_inv_eq_zero P hmon hroot0 hroot1 h0
  have hdeg0 : P.natDegree ≠ 0 := by
    haveI := RamifiedPack.finite_adjoinRoot P hmon
    have h2 : 1 < Nat.card (AdjoinRoot P) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [RamifiedPack.card_adjoinRoot P hmon] at h2
    exact Nat.one_lt_two_pow_iff.mp h2
  obtain ⟨a, r, ha, hr, hfar⟩ := RamifiedPack.exists_two_pow_mul_odd hdeg0 heven
  -- the pack fields at `Wt := AdjoinRoot P`
  letI := RamifiedPack.rootAction (c tameTau) P hposT hdvdP
  have hWt2 := RamifiedPack.adjoinRoot_add_self P
  have hWtsimple := RamifiedPack.isSimpleModTwo_rootAction (c tameTau) P hposT hdvdP
  have hWcard : Nat.card (AdjoinRoot P) = 2 ^ (2 ^ a * r) := by
    rw [RamifiedPack.card_adjoinRoot P hmon, hfar]
  have hepack := RamifiedPack.equiv_zpowers_smul (c tameTau) P hposT hdvdP e he
  have hVU := RamifiedPack.card_fixed_powOmega2 (c tameTau) P (c tameSigma) hgen hrelC hfaith
    hsimple hmon hdvdP hr ha hfar hs1 e he
  -- §6: the rank parity from the first isomorphism theorem
  have hrank : ∀ k : ℕ,
      Nat.card (SectionSix.onePlusU
          (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))).range = 2 ^ k
        → (k : ZMod 2) = (sV : ZMod 2) := by
    intro k hk
    set N := SectionSix.onePlusU (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))
      with hN
    have h1 : Nat.card V = Nat.card ↥N.range * Nat.card ↥N.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.ker]
      congr 1
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange N).toEquiv
    have h2 : Nat.card ↥N.ker = 2 ^ (r * sV) := by
      rw [← hVU]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      rw [AddMonoidHom.mem_ker]
      show v + powOmega2 (c tameSigma) • v = 0 ↔ powOmega2 (c tameSigma) • v = v
      constructor
      · intro hv
        calc powOmega2 (c tameSigma) • v
            = v + (v + powOmega2 (c tameSigma) • v) := by rw [← add_assoc, hV2 v, zero_add]
          _ = v := by rw [hv, add_zero]
      · intro hv
        rw [hv]
        exact hV2 v
    rw [hcard, hk, h2, ← pow_add] at h1
    have h3 : 2 * m = k + r * sV := Nat.pow_right_injective (by norm_num) h1
    have h4 : k ≡ sV [MOD 2] := by
      rcases hr with ⟨j, hj⟩
      have hrs : r * sV = 2 * (j * sV) + sV := by rw [hj]; ring
      unfold Nat.ModEq
      omega
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4
  -- close with the pack
  exact SectionSix.prop_6_9_ramified c hc hfaith hsimple hram q hq hns hinv hV2
    sV r a hr ha hs1 (AdjoinRoot P) hWt2 hWtsimple hWcard e hepack hVU hrank m hm hcard

/-- **The ramified zero count from action-level hypotheses**: the A-4.5b actionization
pushed through `qDouble` — the faithful quotient has the same `σ₂`-action values
(`powOmega2_map` along `mk'`), the action-level `hram` element-izes, and the proved
faithful-level count applies verbatim. -/
theorem zeroCount_qDouble_ramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 (c tameSigma) • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  -- the faithful quotient (the A-4.5b actionization, verbatim)
  set K : Subgroup C :=
    { carrier := {g : C | ∀ v : V, g • v = v}
      one_mem' := fun v => one_smul C v
      mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
      inv_mem' := fun {a} ha v => inv_smul_eq_iff.mpr (ha v).symm } with hK
  haveI hKn : K.Normal :=
    ⟨fun a ha g v => by rw [mul_smul, mul_smul, ha (g⁻¹ • v), smul_inv_smul]⟩
  letI instTQ : TopologicalSpace (C ⧸ K) := ⊥
  haveI instDQ : DiscreteTopology (C ⧸ K) := ⟨rfl⟩
  letI instAQ : DistribMulAction (C ⧸ K) V :=
    { smul := fun x v => Quotient.liftOn' x (fun g => g • v) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab
        show a • v = b • v
        have hb : b = a * (a⁻¹ * b) := by group
        rw [hb, mul_smul, hab v])
      one_smul := fun v => one_smul C v
      mul_smul := fun x y v => Quotient.inductionOn₂' x y fun a b => mul_smul a b v
      smul_zero := fun x => Quotient.inductionOn' x fun a => smul_zero a
      smul_add := fun x v w => Quotient.inductionOn' x fun a => smul_add a v w }
  have hval : ∀ (g : C) (v : V), (QuotientGroup.mk g : C ⧸ K) • v = g • v :=
    fun g v => rfl
  set c' : ContinuousMonoidHom Ttame (C ⧸ K) :=
    ⟨(QuotientGroup.mk' K).comp c.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑(QuotientGroup.mk' K))).comp
        c.continuous_toFun⟩ with hc'
  have hc'surj : Function.Surjective ⇑c' := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨t, ht⟩ := hc x
    exact ⟨t, by show QuotientGroup.mk' K (c t) = _; rw [ht]⟩
  have hfaith' : ∀ g : C ⧸ K, (∀ v : V, g • v = v) → g = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [QuotientGroup.eq_one_iff]
    exact fun v => (hval x v).symm.trans (hg v)
  have hsimple' : ∀ W : AddSubgroup V,
      (∀ (g : C ⧸ K), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hsimple W (fun g w hw => by
      have h := hW (QuotientGroup.mk g) w hw
      rwa [hval] at h)
  have hinv' : IsInvariant (C ⧸ K) q := by
    intro g v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hval]
    exact hinv x v
  -- the action-level ramification element-izes at the faithful quotient
  have hram' : c' tameTau ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ := hram
    refine hv ?_
    have hmem : c tameTau ∈ K := by
      rw [show c' tameTau = QuotientGroup.mk' K (c tameTau) from rfl,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exact hmem v
  -- the `σ₂`-action is unchanged (`powOmega2` commutes with `mk'`)
  have hfun : qDouble q (powOmega2 (c' tameSigma) • ·)
      = qDouble q (powOmega2 (c tameSigma) • ·) := by
    funext x
    show q x + polar q x (powOmega2 (c' tameSigma) • x)
      = q x + polar q x (powOmega2 (c tameSigma) • x)
    have hσ₂ : powOmega2 (c' tameSigma) • x = powOmega2 (c tameSigma) • x := by
      have h := powOmega2_map (QuotientGroup.mk' K) (c tameSigma)
      rw [show c' tameSigma = QuotientGroup.mk' K (c tameSigma) from rfl, ← h]
      exact hval (powOmega2 (c tameSigma)) x
    rw [hσ₂]
  rw [← hfun]
  exact zeroCount_qDouble_ramified_of_faithful c' hc'surj hfaith' hsimple' hram'
    q hq hns hinv' m hm hcard

/-- **The ramified `V`-sum**: `∑ᶠ sign(qDouble) = +2^m` — the plus finale on the proved
ramified count. -/
theorem finsum_sign_ramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (qDouble q (powOmega2 (c tameSigma) • ·) v) = (2 ^ m : ℤ) :=
  finsum_sign_eq_pos_of_zeroCount _ m hm
    (zeroCount_qDouble_ramified_of_action c hc hsimple hram q hq hns hinv m hm hcard) hcard

end Actionization

/-! ## A-4.5c: the split hypothesis pack — `V^σ = 0` and the trivial `σ₂`-action

Unramified structure: with the acting group generated by `{s, t}` (`gen_ttame_quotient`
at the tame package) and inertia `t` acting trivially, every element acts as an integer
power of `s` — the action image is cyclic.  Fixed spaces of powers of `s` are therefore
invariant submodules, and simplicity forces the dichotomy: `V^s = 0` (else the whole
action is trivial, contradicting `hnt`), while the fixed space of the 2-primary part
`σ₂ = powOmega2 s` is NONZERO (a 2-group acting on a finite 2-group) hence everything.
These are the `hVS`/`hU` inputs of `lemma_5_13_split` / `x0Section_bijective_split` /
`liftMark_kappa0_wildValue_fib_split`. -/

section SplitPack

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- With `C = ⟨s, t⟩` and `t` acting trivially, every element acts as an integer power
of `s`. -/
theorem exists_zpow_smul_of_gen (s t : C) (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (htriv : ∀ v : V, t • v = v) (g : C) : ∃ n : ℤ, ∀ v : V, g • v = s ^ n • v := by
  have hg : g ∈ Subgroup.closure ({s, t} : Set C) := by rw [hgen]; trivial
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases Set.mem_insert_iff.mp hx with rfl | hx'
    · exact ⟨1, fun v => by rw [zpow_one]⟩
    · rw [Set.mem_singleton_iff] at hx'
      subst hx'
      exact ⟨0, fun v => by rw [zpow_zero, one_smul]; exact htriv v⟩
  | one => exact ⟨0, fun v => by rw [zpow_zero, one_smul]⟩
  | mul x y hx hy ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    exact ⟨n + k, fun v => by
      rw [mul_smul, hk v, hn (s ^ k • v), ← mul_smul, ← zpow_add]⟩
  | inv x hx ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨-n, fun v => ?_⟩
    rw [inv_smul_eq_iff, hn, ← mul_smul, ← zpow_add, add_neg_cancel, zpow_zero, one_smul]

/-- The cyclic-image commutation: every element's action commutes with powers of `s`. -/
theorem smul_pow_comm_of_gen (s t : C) (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (htriv : ∀ v : V, t • v = v) (g : C) (e : ℕ) (v : V) :
    g • (s ^ e • v) = s ^ e • (g • v) := by
  obtain ⟨n, hn⟩ := exists_zpow_smul_of_gen s t hgen htriv g
  rw [hn (s ^ e • v), hn v, ← mul_smul, ← mul_smul]
  congr 1
  exact ((Commute.refl s).zpow_left n).pow_right e |>.eq

/-- **The split Frobenius-freeness (`hVS`)**: `V^s = 0` — the `s`-fixed space is an
invariant submodule (cyclic image), and `= ⊤` would make the whole action trivial,
contradicting `hnt`. -/
theorem sigma_fixed_eq_zero_of_gen (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (htriv : ∀ v : V, t • v = v)
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hnt : ∃ (g : C) (v : V), g • v ≠ v) :
    ∀ v : V, s • v = v → v = 0 := by
  set W : AddSubgroup V :=
    { carrier := {v : V | s • v = v}
      zero_mem' := smul_zero s
      add_mem' := fun {a b} ha hb => by
        show s • (a + b) = a + b
        rw [smul_add]
        exact congrArg₂ (· + ·) ha hb
      neg_mem' := fun {a} ha => by
        show s • (-a) = -a
        rw [smul_neg]
        exact congrArg Neg.neg ha } with hW
  have hstab : ∀ g : C, ∀ w ∈ W, g • w ∈ W := fun g w hw => by
    show s • (g • w) = g • w
    have hcomm := smul_pow_comm_of_gen s t hgen htriv g 1 w
    rw [pow_one] at hcomm
    rw [← hcomm]
    exact congrArg (g • ·) hw
  rcases hsimple W hstab with hbot | htop
  · exact fun v hv => AddSubgroup.mem_bot.mp (hbot ▸ (hv : v ∈ W))
  · exfalso
    obtain ⟨g, v, hgv⟩ := hnt
    obtain ⟨n, hn⟩ := exists_zpow_smul_of_gen s t hgen htriv g
    have hs : ∀ w : V, s • w = w := fun w => htop.ge (AddSubgroup.mem_top w)
    refine hgv ?_
    rw [hn v]
    exact Subgroup.zpow_mem _ (show s ∈ MulAction.stabilizer C v from hs v) n

/-- **The split `σ₂`-triviality (`hU`)**: the 2-primary part `powOmega2 s` acts trivially —
its fixed space is an invariant submodule (cyclic image), NONZERO because a 2-group acting
on a finite even-order module has even fixed count and fixes `0`, hence `⊤` by simplicity. -/
theorem powOmega2_smul_eq_of_gen [Finite C] [Finite V] (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (htriv : ∀ v : V, t • v = v)
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (heven : 2 ∣ Nat.card V) :
    ∀ v : V, powOmega2 s • v = v := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  -- the fixed space of `σ₂` as a submodule (`powOmega2 s` is literally a power of `s`)
  have hcm : ∀ (g : C) (v : V), g • (powOmega2 s • v) = powOmega2 s • (g • v) :=
    fun g v => smul_pow_comm_of_gen s t hgen htriv g (omega2Exp (orderOf s)) v
  set W : AddSubgroup V :=
    { carrier := {v : V | powOmega2 s • v = v}
      zero_mem' := smul_zero _
      add_mem' := fun {a b} ha hb => by
        show powOmega2 s • (a + b) = a + b
        rw [smul_add]
        exact congrArg₂ (· + ·) ha hb
      neg_mem' := fun {a} ha => by
        show powOmega2 s • (-a) = -a
        rw [smul_neg]
        exact congrArg Neg.neg ha } with hW
  have hstab : ∀ g : C, ∀ w ∈ W, g • w ∈ W := fun g w hw => by
    show powOmega2 s • (g • w) = g • w
    rw [← hcm g w]
    exact congrArg (g • ·) hw
  -- the 2-group `⟨σ₂⟩` and its fixed-point count
  letI : DistribMulAction ↥(Subgroup.zpowers (powOmega2 s)) V :=
    DistribMulAction.compHom V (Subgroup.zpowers (powOmega2 s)).subtype
  haveI : Fintype ↥(Subgroup.zpowers (powOmega2 s)) := Fintype.ofFinite _
  have hp2 : IsPGroup 2 ↥(Subgroup.zpowers (powOmega2 s)) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_powOmega2_dvd_two_pow s)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  haveI : Fintype ↥(MulAction.fixedPoints ↥(Subgroup.zpowers (powOmega2 s)) V) :=
    Fintype.ofFinite _
  have hmod := hp2.card_modEq_card_fixedPoints V
  have h0mem : (0 : V) ∈ MulAction.fixedPoints ↥(Subgroup.zpowers (powOmega2 s)) V :=
    fun g => smul_zero g
  have hge1 : 1 ≤ Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers (powOmega2 s)) V) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨⟨0, h0mem⟩⟩, inferInstance⟩)
  have h2dvd : 2 ∣ Nat.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers (powOmega2 s)) V) := by
    have hV2 : Nat.card V ≡ 0 [MOD 2] := (Nat.modEq_zero_iff_dvd).mpr heven
    exact (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans hV2)
  have hgt : 1 < Fintype.card ↥(MulAction.fixedPoints ↥(Subgroup.zpowers (powOmega2 s)) V) := by
    rw [← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := h2dvd
    omega
  -- a NONZERO fixed vector
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card hgt ⟨0, h0mem⟩
  have hwfix : powOmega2 s • (x : V) = (x : V) :=
    x.2 ⟨powOmega2 s, Subgroup.mem_zpowers _⟩
  have hwne : (x : V) ≠ 0 := fun h => hx (Subtype.ext h)
  -- the dichotomy: `W ≠ ⊥`, so `W = ⊤`
  rcases hsimple W hstab with hbot | htop
  · exact absurd (AddSubgroup.mem_bot.mp (hbot ▸ (hwfix : (x : V) ∈ W))) hwne
  · exact fun v => htop.ge (AddSubgroup.mem_top v)

/-- **The ramified inertia-freeness (`htauf`)**: with `C = ⟨s, t⟩`, the tame relation
`s⁻¹ts = t²`, and `t` of odd order, every conjugate of `t` is a power of `t`
(`⟨t⟩` is normal: `s`-conjugation squares, and the reverse conjugate is the square ROOT
`t^{(d+1)/2}` — odd order makes squaring invertible on `⟨t⟩`), so the `t`-fixed space is
an invariant submodule; if `t` moves anything, simplicity forces it to `⊥` — `V^t = 0`. -/
theorem tau_fixed_eq_zero_of_gen (s t : C)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2)
    (hodd : Odd (orderOf t))
    (hsimple : ∀ W : AddSubgroup V, (∀ g : C, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hmoved : ∃ v : V, t • v ≠ v) :
    ∀ v : V, t • v = v → v = 0 := by
  classical
  -- every element conjugates `t` into `⟨t⟩` (both directions), by closure induction
  have hconj : ∀ g : C, g⁻¹ * t * g ∈ Subgroup.zpowers t
      ∧ g * t * g⁻¹ ∈ Subgroup.zpowers t := by
    intro g
    have hg : g ∈ Subgroup.closure ({s, t} : Set C) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases Set.mem_insert_iff.mp hx with rfl | hx'
      · refine ⟨?_, ?_⟩
        · rw [hrel]
          exact pow_mem (Subgroup.mem_zpowers t) 2
        · -- `x t x⁻¹` is the square root `t^{(d+1)/2}` of `t` (odd order `d`)
          have hsc : SemiconjBy x t (x * t * x⁻¹) := by
            show x * t = x * t * x⁻¹ * x
            group
          have hx2 : (x * t * x⁻¹) ^ 2 = t := by
            have h2 : (x * t * x⁻¹) ^ 2 = x * t ^ 2 * x⁻¹ := by
              rw [pow_two, pow_two]
              group
            rw [h2, ← hrel]
            group
          have horder : orderOf (x * t * x⁻¹) = orderOf t := hsc.orderOf_eq.symm
          obtain ⟨j, hj⟩ := hodd
          have hpow : x * t * x⁻¹ = t ^ (j + 1) := by
            have h1 : (x * t * x⁻¹) ^ (orderOf t + 1) = x * t * x⁻¹ := by
              rw [pow_succ, ← horder, pow_orderOf_eq_one, one_mul]
            calc x * t * x⁻¹ = (x * t * x⁻¹) ^ (orderOf t + 1) := h1.symm
              _ = ((x * t * x⁻¹) ^ 2) ^ (j + 1) := by
                  rw [← pow_mul]
                  congr 1
                  omega
              _ = t ^ (j + 1) := by rw [hx2]
          rw [hpow]
          exact pow_mem (Subgroup.mem_zpowers t) (j + 1)
      · rw [Set.mem_singleton_iff] at hx'
        subst hx'
        refine ⟨?_, ?_⟩
        · rw [show x⁻¹ * x * x = x from by group]
          exact Subgroup.mem_zpowers x
        · rw [show x * x * x⁻¹ = x from by group]
          exact Subgroup.mem_zpowers x
    | one =>
      refine ⟨?_, ?_⟩
      · rw [show (1 : C)⁻¹ * t * 1 = t from by group]
        exact Subgroup.mem_zpowers t
      · rw [show (1 : C) * t * 1⁻¹ = t from by group]
        exact Subgroup.mem_zpowers t
    | mul x y hx hy ihx ihy =>
      refine ⟨?_, ?_⟩
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ihx.1
        rw [show (x * y)⁻¹ * t * (x * y) = y⁻¹ * (x⁻¹ * t * x) * y from by group, ← hk,
          show y⁻¹ * t ^ k * y = (y⁻¹ * t * y) ^ k from by
            have h := map_zpow (MulAut.conj y⁻¹) t k
            simpa [MulAut.conj_apply, mul_assoc] using h]
        exact Subgroup.zpowers_le.mpr ihy.1 (zpow_mem (Subgroup.mem_zpowers _) k)
      · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ihy.2
        rw [show (x * y) * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ from by group, ← hk,
          show x * t ^ k * x⁻¹ = (x * t * x⁻¹) ^ k from by
            have h := map_zpow (MulAut.conj x) t k
            simpa [MulAut.conj_apply, mul_assoc] using h]
        exact Subgroup.zpowers_le.mpr ihx.2 (zpow_mem (Subgroup.mem_zpowers _) k)
    | inv x hx ih =>
      exact ⟨by rw [inv_inv]; exact ih.2, by rw [inv_inv]; exact ih.1⟩
  -- the `t`-fixed space is an invariant submodule; the dichotomy
  set W : AddSubgroup V :=
    { carrier := {v : V | t • v = v}
      zero_mem' := smul_zero t
      add_mem' := fun {a b} ha hb => by
        show t • (a + b) = a + b
        rw [smul_add]
        exact congrArg₂ (· + ·) ha hb
      neg_mem' := fun {a} ha => by
        show t • (-a) = -a
        rw [smul_neg]
        exact congrArg Neg.neg ha } with hW
  have hstab : ∀ g : C, ∀ w ∈ W, g • w ∈ W := fun g w hw => by
    show t • (g • w) = g • w
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hconj g).1
    have hfix : (g⁻¹ * t * g) • w = w := by
      rw [← hk]
      have htw : t ∈ MulAction.stabilizer C w := hw
      exact Subgroup.zpow_mem _ htw k
    calc t • (g • w) = (t * g) • w := (mul_smul t g w).symm
      _ = (g * (g⁻¹ * t * g)) • w := by
          rw [show t * g = g * (g⁻¹ * t * g) from by group]
      _ = g • ((g⁻¹ * t * g) • w) := mul_smul _ _ _
      _ = g • w := by rw [hfix]
  rcases hsimple W hstab with hbot | htop
  · exact fun v hv => AddSubgroup.mem_bot.mp (hbot ▸ (hv : v ∈ W))
  · exfalso
    obtain ⟨v, hv⟩ := hmoved
    exact hv (htop.ge (AddSubgroup.mem_top v))

end SplitPack

section Assembly

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (B : BoundaryMaps) (F : BoundaryFrame H E) (En : RF.Enrichment)


/-! ## A-4.6: the G0-obtain discharge against the c3-G0 tame package

The ThmFourTwo `⟨G0, hGaussZA, hGaussZF⟩`-obtain, decomposed: everything except the
per-block tame-structure package is proved.  The package fields mirror the residue
theorems' `hpack` shapes VERBATIM (per-lift factorizations with the dichotomy clause);
`hfaith` is carried for the LOCAL twins only (the `Γ_A` twins run hfaith-free), and the
ramified flavor carries the orientation (provable only at the concrete
`boundaryMapsWitness` — `tameUnitOrientation_witness`). -/

/-- **The c3-G0 tame package, unramified flavor**: per-lift tame factorizations for both
sources with trivially-acting inertia, plus the form-level constants and the local-side
faithfulness. -/
structure TamePackageUnram (B : BoundaryMaps) (F : BoundaryFrame H E)
    (En : RF.Enrichment) where
  m : ℕ
  hm : 1 ≤ m
  hcard : Nat.card En.Vmod = 2 ^ (2 * m)
  hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1
  packA : ∀ ρ : BoundaryLifts B.bA F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
    Function.Surjective ⇑c ∧ (∀ g : GammaA, ρ.1.1 g = c (B.tameA g)) ∧
      ∀ v : En.Vmod, c tameTau • v = v
  packF : ∀ ρ : BoundaryLifts B.bF F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
    Function.Surjective ⇑c ∧ (∀ g : AbsGalQ2, ρ.1.1 g = c (B.tameF g)) ∧
      ∀ v : En.Vmod, c tameTau • v = v

/-- **The c3-G0 tame package, ramified flavor**: inertia moves the module; the local
side additionally needs the tame-unit orientation (at `R := localReciprocity`). -/
structure TamePackageRam (B : BoundaryMaps) (F : BoundaryFrame H E)
    (En : RF.Enrichment) where
  m : ℕ
  hm : 1 ≤ m
  hcard : Nat.card En.Vmod = 2 ^ (2 * m)
  hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1
  horient : TameUnitOrientation localReciprocity B.tameF
  packA : ∀ ρ : BoundaryLifts B.bA F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
    Function.Surjective ⇑c ∧ (∀ g : GammaA, ρ.1.1 g = c (B.tameA g)) ∧
      ∃ v : En.Vmod, c tameTau • v ≠ v
  packF : ∀ ρ : BoundaryLifts B.bF F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
    Function.Surjective ⇑c ∧ (∀ g : AbsGalQ2, ρ.1.1 g = c (B.tameF g)) ∧
      ∃ v : En.Vmod, c tameTau • v ≠ v


end Assembly

end AffineTLift

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 6.5 = ⟦prop-wordquadratic⟧
-/
