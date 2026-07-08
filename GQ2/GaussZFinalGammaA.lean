import GQ2.GaussZCoordGammaA
import GQ2.GaussZRelatorGammaA

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
    x0Supported v ∈ Z1w (A := V) t := by
  rw [((lemma_5_13_split t ht hw hV₂ hsimple hcore htau hU hVS).1 (x0Supported v))]
  exact ⟨rfl, rfl⟩

/-- The `H¹_w`-class equality criterion in `h1wMk` vocabulary (`H1w` is a semireducible
`def`, so the quotient lemmas do not elaborate against it directly — the
`GaussZLocal.H1mk_eq_iff` idiom). -/
theorem h1wMk_eq_iff {t : Marking C} [Finite V] (x y : ↥(Z1w (A := V) t)) :
    h1wMk t x = h1wMk t y
      ↔ (x - y : ↥(Z1w (A := V) t)).1 ∈ B1w (A := V) t := by
  show (QuotientAddGroup.mk x
      : ↥(Z1w (A := V) t) ⧸ (B1w (A := V) t).addSubgroupOf (Z1w (A := V) t))
    = QuotientAddGroup.mk y ↔ _
  rw [QuotientAddGroup.eq_iff_sub_mem]
  exact Iff.rfl

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
    have h0 : v - v' = (0 : V) := by
      simpa [x0Supported] using h2
    exact sub_eq_zero.mp h0
  · -- surjective: normalize the `σ`-row away
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨h1, h3⟩ := (hshape.1 z.1).mp z.2
      have hsurj : Function.Surjective (fun w : V => t.σ • w - w) :=
        Finite.injective_iff_surjective.mp (fun a b hab => by
          have hfix : t.σ • (a - b) = a - b := by
            rw [smul_sub, sub_eq_sub_iff_sub_eq_sub]
            exact hab
          exact sub_eq_zero.mp (hVS (a - b) hfix))
      obtain ⟨w, hw'⟩ := hsurj (z.1 0)
      refine ⟨z.1 2, ?_⟩
      show h1wMk t ⟨x0Supported (z.1 2), _⟩ = QuotientAddGroup.mk z
      rw [show (QuotientAddGroup.mk z
          : ↥(Z1w (A := V) t) ⧸ (B1w (A := V) t).addSubgroupOf (Z1w (A := V) t))
        = h1wMk t z from rfl]
      rw [h1wMk_eq_iff]
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

/-- **The `x₀`-supported tuples are word cocycles** (ramified regime): both `d¹`-rows
vanish on the section by the closed forms (`d1Fun_tame` involves only the `σ`/`τ`-slots;
the ramified wild row `liftMarking_wildValue_u_ramified` is `σ⁻¹ • x₃`). -/
theorem x0Supported_mem_Z1w_ramified (t : Marking C) (ht : t.TameRel)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) :
    x0Supported v ∈ Z1w (A := V) t := by
  rw [Z1w, AddMonoidHom.mem_ker,
    show d1 t (x0Supported v) = d1Fun t (x0Supported v) from rfl]
  refine Prod.ext ?_ ?_
  · rw [d1Fun_tame t ht (x0Supported v)]
    show t.σ⁻¹ • (t.τ • (0 : V)) - t.σ⁻¹ • (0 : V) + t.σ⁻¹ • (0 : V)
      - ((0 : V) + t.τ • (0 : V)) = (0 : V × V).1
    simp
  · rw [show (d1Fun t (x0Supported v)).2 = (liftMarking t (x0Supported v)).wildValue.u
        from rfl,
      liftMarking_wildValue_u_ramified t (x0Supported v) hV₂ hx0 hx1 htau hTodd]
    show t.σ⁻¹ • (0 : V) = (0 : V × V).2
    simp

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

@[simp] theorem sdSec_base (cc : C) : (sdSec dat hdat cc).base = Sd.mk (0 : V) cc := rfl

@[simp] theorem sdSec_fib (cc : C) : (sdSec dat hdat cc).fib = 0 := rfl

/-- **The tame κ⁰-value is base-slice**: at any lifted marking whose `σ`/`τ`-slots have
zero `V`-part, the tame relator value is the `sdSec`-image of the `C`-level tame value —
its fibre vanishes (no `TameRel` needed). -/
theorem liftMark_kappa0_tameValue_fib (t : Marking (Sd C V))
    (hσ : t.σ.v = 0) (hτ : t.τ.v = 0) :
    (liftMark t (kappa0Cocycle dat hdat)).tameValue.fib = 0 := by
  have hσ' : (liftMark t (kappa0Cocycle dat hdat)).σ = sdSec dat hdat t.σ.cc := by
    refine CentExt.ext (Sd.ext hσ rfl) rfl
  have hτ' : (liftMark t (kappa0Cocycle dat hdat)).τ = sdSec dat hdat t.τ.cc := by
    refine CentExt.ext (Sd.ext hτ rfl) rfl
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

@[simp] theorem sdToWL_u (p : Sd C V) : (sdToWL p).u = p.v := rfl

@[simp] theorem sdToWL_g (p : Sd C V) : (sdToWL p).g = p.cc := rfl

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

/-- `z₀`'s `V`-part transports to the banked `WordLift` ledger. -/
theorem sd_z0_v (tS : Marking (Sd C V)) :
    tS.z0.v = (liftMarking (sdBaseMarking tS) (sdOffsets tS)).z0.u := by
  have h := Marking.map_z0 (f := sdToWL) (t := tS)
  rw [sdToWL_marking] at h
  exact (congrArg WordLift.u h).symm

/-- `u₁`'s `V`-part transports to the banked `WordLift` ledger. -/
theorem sd_u1_v (tS : Marking (Sd C V)) :
    tS.u1.v = (liftMarking (sdBaseMarking tS) (sdOffsets tS)).u1.u := by
  have h := Marking.map_u1 (f := sdToWL) (t := tS)
  rw [sdToWL_marking] at h
  exact (congrArg WordLift.u h).symm

/-- `c₀`'s `V`-part transports to the banked `WordLift` ledger. -/
theorem sd_c0_v (tS : Marking (Sd C V)) :
    tS.c0.v = (liftMarking (sdBaseMarking tS) (sdOffsets tS)).c0.u := by
  have h := Marking.map_c0 (f := sdToWL) (t := tS)
  rw [sdToWL_marking] at h
  exact (congrArg WordLift.u h).symm

/-- `h₀`'s `V`-part transports to the banked `WordLift` ledger. -/
theorem sd_h0_v (tS : Marking (Sd C V)) :
    tS.h0.v = (liftMarking (sdBaseMarking tS) (sdOffsets tS)).h0.u := by
  have h := Marking.map_h0 (f := sdToWL) (t := tS)
  rw [sdToWL_marking] at h
  exact (congrArg WordLift.u h).symm

/-- The `CentExt κ⁰`-level factors project to the `Sd`-level factors (`d₀` case; the
projection is `liftMark_map_proj` + word functoriality). -/
theorem liftMark_d0_base (tS : Marking (Sd C V)) :
    ((liftMark tS (kappa0Cocycle dat hdat)).d0).base = tS.d0 := by
  have h := Marking.map_d0 (f := CentExt.proj (kappa0Cocycle dat hdat))
    (t := liftMark tS (kappa0Cocycle dat hdat))
  rw [liftMark_map_proj] at h
  exact (congrArg (fun p => p) h).symm ▸ rfl

end FactorTransport

/-- **The `x₀`-square cell** — the quadratically decisive fibre value: when the `x₀`-base
acts trivially on `V` (`hx0`, the split wild-triviality), the square of the lifted
`x₀`-slot has fibre `q(v) + m_{P}(v)` (`f_diag` turns the `f`-term into the quadratic
form; the `m`-term is the paper's "starred entry", cancelled later in the `h₀`-ledger). -/
theorem liftMark_x0_sq_fib (tS : Marking (Sd C V))
    (hx0 : ∀ w : V, tS.x₀.cc • w = w) :
    ((liftMark tS (kappa0Cocycle dat hdat)).x₀ ^ 2).fib
      = q tS.x₀.v + dat.m tS.x₀.cc tS.x₀.v := by
  rw [pow_two, CentExt.mul_fib]
  show (0 : ZMod 2) + 0 + (kappa0Cocycle dat hdat).κ tS.x₀ tS.x₀ = _
  rw [kappa0Cocycle_κ, hx0 tS.x₀.v, hdat.f_diag, zero_add, zero_add]

/-! ### A-4.3b: conjugation and base-slice fibre cells + the `m`-calculus

The κ⁰-peel's step lemmas: on `V`-part-zero prefixes the fibre accumulates only
`m`-corrections (`f` dies on a zero slot); conjugation by an `sdSec`-image shifts the
fibre by one `m`-value; `m` at squares/inverses of `V`-fixing elements vanishes/reflects
(`m_mul` + char 2).  These are the `CentExt κ⁰`-analogs of the `HeisLift.mul_z_of_trivial`
family. -/

theorem sdSec_inv (w : C) : (sdSec dat hdat w)⁻¹ = sdSec dat hdat w⁻¹ :=
  (map_inv (sdSec dat hdat) w).symm

/-- `powOmega2` of an `sdSec`-image has zero fibre. -/
theorem powOmega2_sdSec_fib (w : C) : (powOmega2 (sdSec dat hdat w)).fib = 0 := by
  rw [powOmega2, ← map_pow]
  rfl

/-- `powOmega2` of an `sdSec`-image has zero `V`-part. -/
theorem powOmega2_sdSec_base_v (w : C) : (powOmega2 (sdSec dat hdat w)).base.v = 0 := by
  rw [powOmega2, ← map_pow]
  rfl

/-- **The fibre step on a `V`-part-zero left factor**: only the `m`-correction survives. -/
theorem mul_fib_of_v_zero (p r : CentExt (kappa0Cocycle dat hdat))
    (hp : p.base.v = 0) :
    (p * r).fib = p.fib + r.fib + dat.m p.base.cc r.base.v := by
  rw [CentExt.mul_fib, kappa0Cocycle_κ, hp, hdat.f_zero_left, zero_add]

/-- **The fibre step when both `V`-parts vanish**: plain additivity. -/
theorem mul_fib_of_v_zero' (p r : CentExt (kappa0Cocycle dat hdat))
    (hp : p.base.v = 0) (hr : r.base.v = 0) :
    (p * r).fib = p.fib + r.fib := by
  rw [mul_fib_of_v_zero dat hdat p r hp, hr, hdat.m_zero, add_zero]

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
  -- `0 = m_{w⁻¹}(v) + m_w(v)` in `ZMod 2`
  have hchar : ∀ a b : ZMod 2, 0 = a + b → a = b := by decide
  exact hchar _ _ h

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

set_option maxHeartbeats 800000 in
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
  constructor
  · show p.base⁻¹ = p.base
    refine Sd.ext ?_ ?_
    · show -(p.base.cc⁻¹ • p.base.v) = p.base.v
      rw [hp, inv_one, one_smul]
      exact neg_eq_of_add_eq_zero_left (hV₂ _)
    · show p.base.cc⁻¹ = p.base.cc
      rw [hp, inv_one]
  · show p.fib + (kappa0Cocycle dat hdat).κ p.base p.base⁻¹ = p.fib + q p.base.v
    rw [kappa0_cc_one dat hdat _ _ hp]
    congr 1
    have hbv : p.base⁻¹.v = p.base.v := by
      show -(p.base.cc⁻¹ • p.base.v) = p.base.v
      rw [hp, inv_one, one_smul]
      exact neg_eq_of_add_eq_zero_left (hV₂ _)
    rw [hbv, hdat.f_diag]

set_option maxHeartbeats 1600000 in
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

set_option maxHeartbeats 1600000 in
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

/-- **THE RAMIFIED PACK GAP** (board §(4)) — SORRIED: the ramified `qDouble` zero count
`2^{2m−1} + 2^{m−1}`.  The mathematical content is `prop_6_9_ramified` at the faithful
quotient (the A-4.5b actionization element-izes `hram`), whose isotypic pack
`(s r a Wt e he hVU hrank)` — the Clifford decomposition `V|_⟨cτ⟩ ≅ W^{⊕s}` of the
faithful simple ramified tame module with `#W = 2^{2^a·r}`, the `#V^U = 2^{rs}` count and
the rank parity — is underived in-repo (the local source dodged it via the Tate route
`prop_6_18_ramified`, unavailable over `Γ_A`).  Discharge = derive the pack, or find a
pack-free `arf(qDouble) = 0` route. -/
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
  sorry

/-- **The ramified `V`-sum**: `∑ᶠ sign(qDouble) = +2^m` — the plus finale on the (sorried)
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
    have h1 : s ^ n • (x⁻¹ • v) = v := by rw [← hn (x⁻¹ • v), smul_inv_smul]
    calc x⁻¹ • v = (s ^ (-n) * s ^ n) • (x⁻¹ • v) := by
          rw [← zpow_add, neg_add_cancel, zpow_zero, one_smul]
      _ = s ^ (-n) • (s ^ n • (x⁻¹ • v)) := mul_smul _ _ _
      _ = s ^ (-n) • v := by rw [h1]

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
  · intro v hv
    have hmem : v ∈ W := hv
    rw [hbot] at hmem
    exact AddSubgroup.mem_bot.mp hmem
  · exfalso
    obtain ⟨g, v, hgv⟩ := hnt
    obtain ⟨n, hn⟩ := exists_zpow_smul_of_gen s t hgen htriv g
    have hs : ∀ w : V, s • w = w := fun w => by
      have hmem : w ∈ W := by rw [htop]; exact AddSubgroup.mem_top w
      exact hmem
    refine hgv ?_
    rw [hn v]
    have hmem : s ∈ MulAction.stabilizer C v := hs v
    exact Subgroup.zpow_mem _ hmem n

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
  · exact absurd (show (x : V) ∈ W from hwfix)
      (by rw [hbot]; exact fun hmem => hwne (AddSubgroup.mem_bot.mp hmem))
  · intro v
    have hmem : v ∈ W := by rw [htop]; exact AddSubgroup.mem_top v
    exact hmem

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
  · intro v hv
    have hmem : v ∈ W := hv
    rw [hbot] at hmem
    exact AddSubgroup.mem_bot.mp hmem
  · exfalso
    obtain ⟨v, hv⟩ := hmoved
    refine hv ?_
    have hmem : v ∈ W := by rw [htop]; exact AddSubgroup.mem_top v
    exact hmem

end SplitPack

section Assembly

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
variable {RF : RecursionFrame T Blk}
variable (B : BoundaryMaps) (F : BoundaryFrame H E) (En : RF.Enrichment)

/-- **The unramified pinned value over `Γ_A`** (the A-4 seam, paper Prop 6.9/(91) minus case):
with the tame package acting trivially on `V` (`T = 1`), the descended base determinant form
sums to `−2^m` over `Z¹⧸B¹`.  SORRIED (skeleton-first; the κ⁰-ledger increments fill it). -/
theorem sum_sign_QZeroBar_gammaA_unramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLifts B.bA F RF.TC)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective ⇑c)
    (hfacρ : ∀ g : GammaA, ρ.1.1 g = c (B.tameA g))
    (hunram : ∀ v : En.Vmod, c tameTau • v = v) :
    ∑ᶠ x : VCocycle (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        ⧸ vCobRange (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ),
      sign (QZeroBar (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        htriv_gammaA x)
      = -(2 ^ m : ℤ) := by
  classical
  -- ===== stage 0: GA-instances and the letI pack (the local `GaussZFinal` idiom) =====
  letI : DistribMulAction GA (ZMod 2) :=
    inferInstanceAs (DistribMulAction GammaA (ZMod 2))
  haveI : ContinuousSMul GA (ZMod 2) := inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
  haveI : IsTopologicalGroup GA := inferInstanceAs (IsTopologicalGroup (GammaA : Type))
  letI instT : TopologicalSpace En.Vmod := ⊥
  haveI instD : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction GA En.Vmod :=
    DistribMulAction.compHom _ (thetaGA B.bA F ρ).toMonoidHom
  haveI instC : ContinuousSMul GA En.Vmod := ⟨by
    show Continuous fun p : GA × En.Vmod => (thetaGA B.bA F ρ) p.1 • p.2
    exact (continuous_of_discreteTopology
      (f := fun q : RF.YC × En.Vmod => q.1 • q.2)).comp
      (((thetaGA B.bA F ρ).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace (En.descData l h).Vmod := instT
  haveI : DiscreteTopology (En.descData l h).Vmod := instD
  letI : DistribMulAction GA (En.descData l h).Vmod := instA
  haveI : ContinuousSMul GA (En.descData l h).Vmod := instC
  letI : DistribMulAction RF.YC (En.descData l h).Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  haveI : Finite (En.descData l h).Vmod := (inferInstance : Finite En.Vmod)
  letI : TopologicalSpace (En.descData l h).C0 := (inferInstance : TopologicalSpace RF.YC)
  haveI : DiscreteTopology (En.descData l h).C0 := (inferInstance : DiscreteTopology RF.YC)
  haveI : Finite (En.descData l h).C0 := (inferInstance : Finite RF.YC)
  -- re-spell the goal at the `GA`-typed `rhoPrimeGA` (defeq)
  show ∑ᶠ x : VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)
      ⧸ vCobRange (En.descData l h) (rhoPrimeGA B.bA F En l h ρ),
    sign (QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA x)
    = -(2 ^ m : ℤ)
  -- ===== stage 1: θ-facts and the bridge hypotheses =====
  have hθsurj : Function.Surjective ⇑(thetaGA B.bA F ρ) := thetaGA_surjective B.bA F ρ
  have hcompat : ∀ (γ : GA) (v : (En.descData l h).Vmod),
      γ • v = thetaGA B.bA F ρ γ • v := fun _ _ => rfl
  have hround : ∀ γ : GA,
      rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) γ = thetaGA B.bA F ρ γ :=
    roundtripGA B.bA F En l h ρ
  have hcomp : ∀ (γ : GA) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) γ • v := fun γ v =>
    (congrArg (fun cc : (En.descData l h).C0 => cc • v) (hround γ)).symm
  letI : DistribMulAction AbsGalQ2 En.Vmod :=
    DistribMulAction.compHom _ (1 : AbsGalQ2 →* RF.YC)
  letI : DistribMulAction AbsGalQ2 (En.descData l h).Vmod :=
    (inferInstance : DistribMulAction AbsGalQ2 En.Vmod)
  haveI : ContinuousSMul AbsGalQ2 En.Vmod := ⟨by
    show Continuous fun p : AbsGalQ2 × En.Vmod => ((1 : AbsGalQ2 →* RF.YC) p.1) • p.2
    simp only [MonoidHom.one_apply, one_smul]
    exact continuous_snd⟩
  haveI : ContinuousSMul AbsGalQ2 (En.descData l h).Vmod :=
    (inferInstance : ContinuousSMul AbsGalQ2 En.Vmod)
  have hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0 :=
    DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  have hcardDD : Nat.card (En.descData l h).Vmod = 2 ^ (2 * m) := hcard
  -- ===== stage 2: generator slot values of `markC θ` =====
  have hσslot : (markC (thetaGA B.bA F ρ)).σ = c tameSigma := by
    rw [congrArg Marking.σ (markC_map (thetaGA B.bA F ρ))]
    calc thetaGA B.bA F ρ gammaGen.σ
        = c (B.tameA (quotientMk NA univMarking.σ)) := hfacρ _
      _ = c tameSigma := by rw [B.tameA_sigma]
  have hτslot : (markC (thetaGA B.bA F ρ)).τ = c tameTau := by
    rw [congrArg Marking.τ (markC_map (thetaGA B.bA F ρ))]
    calc thetaGA B.bA F ρ gammaGen.τ
        = c (B.tameA (quotientMk NA univMarking.τ)) := hfacρ _
      _ = c tameTau := by rw [B.tameA_tau]
  have hadm := markC_admissible (thetaGA B.bA F ρ) hθsurj
  -- ===== stage 3: the split hypothesis pack at `markC θ` =====
  haveI : ContinuousMul RF.YC := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousInv RF.YC := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalGroup RF.YC := { }
  have hgen : Subgroup.closure ({c tameSigma, c tameTau} : Set RF.YC) = ⊤ :=
    SectionThree.gen_ttame_quotient c.toMonoidHom c.continuous_toFun hc
  have hsimpleM : IsSimpleModTwo RF.YC (En.descData l h).Vmod := by
    constructor
    · obtain ⟨v, hv⟩ := hVne
      exact ⟨v, 0, hv⟩
    · intro W hW
      exact hsimple W fun g w hw => hW g w hw
  have htauM : ∀ v : (En.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).τ • v = v := fun v => by
    rw [hτslot]
    exact hunram v
  have hUM : ∀ v : (En.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).sigma2 • v = v := fun v => by
    show powOmega2 (markC (thetaGA B.bA F ρ)).σ • v = v
    rw [hσslot]
    exact powOmega2_smul_eq_of_gen (c tameSigma) (c tameTau) hgen hunram hsimple
      (by rw [hcard]; exact dvd_pow_self 2 (by omega)) v
  have hVSM : ∀ v : (En.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).σ • v = v → v = 0 := fun v hv =>
    sigma_fixed_eq_zero_of_gen (c tameSigma) (c tameTau) hgen hunram hsimple hnt v
      (by rwa [hσslot] at hv)
  have hmem : ∀ v : (En.descData l h).Vmod,
      x0Supported v ∈ Z1w (A := (En.descData l h).Vmod) (markC (thetaGA B.bA F ρ)) :=
    fun v => x0Supported_mem_Z1w_split (markC (thetaGA B.bA F ρ)) hadm.2.1 hadm.2.2.1 hA₂
      hsimpleM hadm.2.2.2 htauM hUM hVSM v
  have hsec := x0Section_bijective_split (markC (thetaGA B.bA F ρ)) hadm.2.1 hadm.2.2.1 hA₂
    hsimpleM hadm.2.2.2 htauM hUM hVSM
  -- ===== stage 4: the section cocycles and the reindex map ψ =====
  set secC : (En.descData l h).Vmod →
      VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) := fun v =>
    ofZ1 hcomp (ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
    with hsecCdef
  set ψ : (En.descData l h).Vmod →
      (VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)
        ⧸ vCobRange (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)) := fun v =>
    QuotientAddGroup.mk (secC v) with hψdef
  -- ===== stage 5: ψ hits the x₀-supported section classes; bijectivity =====
  have hcoordψ : ∀ v, h1CoordGammaA B.bA F En l h ρ hcomp hcompat hA₂ (ψ v)
      = h1wMk (markC (thetaGA B.bA F ρ)) ⟨x0Supported v, hmem v⟩ := fun v => by
    show h1wMk (markC (thetaGA B.bA F ρ))
        (toZ1wHom (thetaGA B.bA F ρ) hcompat (toZ1 hcomp (secC v))) = _
    rw [show toZ1 hcomp (secC v)
        = ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩ from
        toZ1_ofZ1 hcomp _]
    rw [toZ1wHom_ofZ1w]
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro v v' hvv'
      have h1 := congrArg (h1CoordGammaA B.bA F En l h ρ hcomp hcompat hA₂) hvv'
      rw [hcoordψ v, hcoordψ v'] at h1
      exact hsec.1 h1
    · intro x
      obtain ⟨v, hv⟩ := hsec.2 (h1CoordGammaA B.bA F En l h ρ hcomp hcompat hA₂ x)
      exact ⟨v, (h1CoordGammaA_bijective B.bA F En l h ρ hcomp hcompat hA₂).1
        ((hcoordψ v).trans hv)⟩
  -- ===== stage 6: the value on section classes is `q̄` =====
  have hdat : IsEquivariantFactorSet ((En.descData l h).qbar) (En.descData l h).dat :=
    En.hdat l h
  have hevalx : ∀ v : (En.descData l h).Vmod,
      eval (ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
        = x0Supported v := fun v => by
    have h2 := congrArg Subtype.val
      (toZ1wHom_ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
    rwa [toZ1wHom_coe] at h2
  have hσv : ∀ v, (gammaGen.map (graphSdHom (secC v))).σ.v = 0 := fun v => by
    show (secC v).c gammaGen.σ = 0
    exact congrFun (hevalx v) 0
  have hτv : ∀ v, (gammaGen.map (graphSdHom (secC v))).τ.v = 0 := fun v => by
    show (secC v).c gammaGen.τ = 0
    exact congrFun (hevalx v) 1
  have hx1v : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₁.v = 0 := fun v => by
    show (secC v).c gammaGen.x₁ = 0
    exact congrFun (hevalx v) 3
  have hx0v : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₀.v = v := fun v => by
    show (secC v).c gammaGen.x₀ = v
    exact congrFun (hevalx v) 2
  have hccσ : ∀ v, (gammaGen.map (graphSdHom (secC v))).σ.cc = c tameSigma := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.σ = c tameSigma
    rw [hround gammaGen.σ]
    calc thetaGA B.bA F ρ gammaGen.σ
        = c (B.tameA (quotientMk NA univMarking.σ)) := hfacρ _
      _ = c tameSigma := by rw [B.tameA_sigma]
  have hccτ : ∀ v, (gammaGen.map (graphSdHom (secC v))).τ.cc = c tameTau := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.τ = c tameTau
    rw [hround gammaGen.τ]
    calc thetaGA B.bA F ρ gammaGen.τ
        = c (B.tameA (quotientMk NA univMarking.τ)) := hfacρ _
      _ = c tameTau := by rw [B.tameA_tau]
  have hccx0 : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₀.cc = 1 := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.x₀ = 1
    rw [hround gammaGen.x₀]
    calc thetaGA B.bA F ρ gammaGen.x₀
        = c (B.tameA (quotientMk NA univMarking.x₀)) := hfacρ _
      _ = 1 := by rw [B.tameA_x0, map_one]
  have hccx1 : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₁.cc = 1 := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.x₁ = 1
    rw [hround gammaGen.x₁]
    calc thetaGA B.bA F ρ gammaGen.x₁
        = c (B.tameA (quotientMk NA univMarking.x₁)) := hfacρ _
      _ = 1 := by rw [B.tameA_x1, map_one]
  have hwild : ∀ v, (liftMark (gammaGen.map (graphSdHom (secC v)))
      (kappa0Cocycle (En.descData l h).dat hdat)).wildValue.fib
      = (En.descData l h).qbar v := fun v => by
    have htauS : ∀ w : (En.descData l h).Vmod,
        (gammaGen.map (graphSdHom (secC v))).τ.cc • w = w := fun w => by
      rw [hccτ v]
      exact hunram w
    have hτoddS : Odd (orderOf (gammaGen.map (graphSdHom (secC v))).τ.cc) := by
      rw [hccτ v]
      exact LocalKummer.odd_orderOf_tameInertia c
    have hUS : ∀ w : (En.descData l h).Vmod,
        Marking.sigma2 (sdBaseMarking (gammaGen.map (graphSdHom (secC v)))) • w = w :=
      fun w => by
      show powOmega2 (gammaGen.map (graphSdHom (secC v))).σ.cc • w = w
      rw [hccσ v]
      exact powOmega2_smul_eq_of_gen (c tameSigma) (c tameTau) hgen hunram hsimple
        (by rw [hcard]; exact dvd_pow_self 2 (by omega)) w
    rw [liftMark_kappa0_wildValue_fib_split (En.descData l h).dat hdat
      (gammaGen.map (graphSdHom (secC v))) (hσv v) (hτv v) (hx1v v) (hccx0 v) (hccx1 v)
      hA₂ htauS hUS hτoddS, hx0v v]
  have hval : ∀ v, QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA (ψ v)
      = En.qbar l h v := fun v => by
    show QZero (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) (secC v) = En.qbar l h v
    haveI : ContinuousSMul GA (ZMod 2) :=
      inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
    rw [QZero_eq_relZPair_kappa0 (fun x m => rfl) hdat (secC v),
      relZPair_kappa0_fst_eq_zero (En.descData l h).dat hdat _ (hσv v) (hτv v), zero_add]
    exact hwild v
  -- ===== stage 7: reindex and count =====
  calc ∑ᶠ x : VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)
        ⧸ vCobRange (En.descData l h) (rhoPrimeGA B.bA F En l h ρ),
      sign (QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA x)
      = ∑ᶠ v : (En.descData l h).Vmod, sign (En.qbar l h v) := by
        refine (finsum_eq_of_bijective ψ hψbij fun v => ?_).symm
        show sign (En.qbar l h v)
          = sign (QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA (ψ v))
        rw [hval v]
    _ = -(2 ^ m : ℤ) :=
      finsum_sign_unramified_of_action c hc hsimple hVne hunram (En.qbar l h)
        (En.hquad l h) (En.hns l h) (En.hinv l h) m hm hcard

/-- **The ramified pinned value over `Γ_A`** (the A-4 seam, paper Prop 6.9/(91) plus case):
with the tame package moving `V` (`V^T = 0` regime), the sum is `+2^m`.  SORRIED
(skeleton-first). -/
theorem sum_sign_QZeroBar_gammaA_ramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (ρ : BoundaryLifts B.bA F RF.TC)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective ⇑c)
    (hfacρ : ∀ g : GammaA, ρ.1.1 g = c (B.tameA g))
    (hram : ∃ v : En.Vmod, c tameTau • v ≠ v) :
    ∑ᶠ x : VCocycle (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        ⧸ vCobRange (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ),
      sign (QZeroBar (En.descData l h) (RF.rhoPrime B.bA F (En.radData l h) rfl ρ)
        htriv_gammaA x)
      = (2 ^ m : ℤ) := by
  classical
  -- ===== stage 0: GA-instances and the letI pack (mirrors the unramified seam) =====
  letI : DistribMulAction GA (ZMod 2) :=
    inferInstanceAs (DistribMulAction GammaA (ZMod 2))
  haveI : ContinuousSMul GA (ZMod 2) := inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
  haveI : IsTopologicalGroup GA := inferInstanceAs (IsTopologicalGroup (GammaA : Type))
  letI instT : TopologicalSpace En.Vmod := ⊥
  haveI instD : DiscreteTopology En.Vmod := ⟨rfl⟩
  letI instA : DistribMulAction GA En.Vmod :=
    DistribMulAction.compHom _ (thetaGA B.bA F ρ).toMonoidHom
  haveI instC : ContinuousSMul GA En.Vmod := ⟨by
    show Continuous fun p : GA × En.Vmod => (thetaGA B.bA F ρ) p.1 • p.2
    exact (continuous_of_discreteTopology
      (f := fun q : RF.YC × En.Vmod => q.1 • q.2)).comp
      (((thetaGA B.bA F ρ).continuous.comp continuous_fst).prodMk continuous_snd)⟩
  letI : TopologicalSpace (En.descData l h).Vmod := instT
  haveI : DiscreteTopology (En.descData l h).Vmod := instD
  letI : DistribMulAction GA (En.descData l h).Vmod := instA
  haveI : ContinuousSMul GA (En.descData l h).Vmod := instC
  letI : DistribMulAction RF.YC (En.descData l h).Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  haveI : Finite (En.descData l h).Vmod := (inferInstance : Finite En.Vmod)
  letI : TopologicalSpace (En.descData l h).C0 := (inferInstance : TopologicalSpace RF.YC)
  haveI : DiscreteTopology (En.descData l h).C0 := (inferInstance : DiscreteTopology RF.YC)
  haveI : Finite (En.descData l h).C0 := (inferInstance : Finite RF.YC)
  show ∑ᶠ x : VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)
      ⧸ vCobRange (En.descData l h) (rhoPrimeGA B.bA F En l h ρ),
    sign (QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA x)
    = (2 ^ m : ℤ)
  -- ===== stage 1: θ-facts and the bridge hypotheses =====
  have hθsurj : Function.Surjective ⇑(thetaGA B.bA F ρ) := thetaGA_surjective B.bA F ρ
  have hcompat : ∀ (γ : GA) (v : (En.descData l h).Vmod),
      γ • v = thetaGA B.bA F ρ γ • v := fun _ _ => rfl
  have hround : ∀ γ : GA,
      rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) γ = thetaGA B.bA F ρ γ :=
    roundtripGA B.bA F En l h ρ
  have hcomp : ∀ (γ : GA) (v : (En.descData l h).Vmod),
      γ • v = rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) γ • v := fun γ v =>
    (congrArg (fun cc : (En.descData l h).C0 => cc • v) (hround γ)).symm
  letI : DistribMulAction AbsGalQ2 En.Vmod :=
    DistribMulAction.compHom _ (1 : AbsGalQ2 →* RF.YC)
  letI : DistribMulAction AbsGalQ2 (En.descData l h).Vmod :=
    (inferInstance : DistribMulAction AbsGalQ2 En.Vmod)
  haveI : ContinuousSMul AbsGalQ2 En.Vmod := ⟨by
    show Continuous fun p : AbsGalQ2 × En.Vmod => ((1 : AbsGalQ2 →* RF.YC) p.1) • p.2
    simp only [MonoidHom.one_apply, one_smul]
    exact continuous_snd⟩
  haveI : ContinuousSMul AbsGalQ2 (En.descData l h).Vmod :=
    (inferInstance : ContinuousSMul AbsGalQ2 En.Vmod)
  have hA₂ : ∀ v : (En.descData l h).Vmod, v + v = 0 :=
    DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  -- ===== stage 2: generator slot values of `markC θ` =====
  have hτslot : (markC (thetaGA B.bA F ρ)).τ = c tameTau := by
    rw [congrArg Marking.τ (markC_map (thetaGA B.bA F ρ))]
    calc thetaGA B.bA F ρ gammaGen.τ
        = c (B.tameA (quotientMk NA univMarking.τ)) := hfacρ _
      _ = c tameTau := by rw [B.tameA_tau]
  have hx0slot : (markC (thetaGA B.bA F ρ)).x₀ = 1 := by
    rw [congrArg Marking.x₀ (markC_map (thetaGA B.bA F ρ))]
    calc thetaGA B.bA F ρ gammaGen.x₀
        = c (B.tameA (quotientMk NA univMarking.x₀)) := hfacρ _
      _ = 1 := by rw [B.tameA_x0, map_one]
  have hx1slot : (markC (thetaGA B.bA F ρ)).x₁ = 1 := by
    rw [congrArg Marking.x₁ (markC_map (thetaGA B.bA F ρ))]
    calc thetaGA B.bA F ρ gammaGen.x₁
        = c (B.tameA (quotientMk NA univMarking.x₁)) := hfacρ _
      _ = 1 := by rw [B.tameA_x1, map_one]
  have hadm := markC_admissible (thetaGA B.bA F ρ) hθsurj
  -- ===== stage 3: the ramified hypothesis pack at `markC θ` =====
  haveI : ContinuousMul RF.YC := ⟨continuous_of_discreteTopology⟩
  haveI : ContinuousInv RF.YC := ⟨continuous_of_discreteTopology⟩
  haveI : IsTopologicalGroup RF.YC := { }
  have hgen : Subgroup.closure ({c tameSigma, c tameTau} : Set RF.YC) = ⊤ :=
    SectionThree.gen_ttame_quotient c.toMonoidHom c.continuous_toFun hc
  have hrelC : (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 := by
    have hrel := congrArg (⇑c) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using hrel
  have hoddC : Odd (orderOf (c tameTau)) := LocalKummer.odd_orderOf_tameInertia c
  have hx0M : ∀ v : (En.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).x₀ • v = v := fun v => by
    rw [hx0slot, one_smul]
  have hx1M : ∀ v : (En.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).x₁ • v = v := fun v => by
    rw [hx1slot, one_smul]
  have htauM : ∀ v : (En.descData l h).Vmod,
      (markC (thetaGA B.bA F ρ)).τ • v = v → v = 0 := fun v hv =>
    tau_fixed_eq_zero_of_gen (c tameSigma) (c tameTau) hgen hrelC hoddC hsimple hram v
      (by rwa [hτslot] at hv)
  have hToddM : ∀ v : (En.descData l h).Vmod,
      powOmega2 (markC (thetaGA B.bA F ρ)).τ • v = v := fun v => by
    rw [hτslot, powOmega2_eq_one_of_odd hoddC, one_smul]
  have hmem : ∀ v : (En.descData l h).Vmod,
      x0Supported v ∈ Z1w (A := (En.descData l h).Vmod) (markC (thetaGA B.bA F ρ)) :=
    fun v => x0Supported_mem_Z1w_ramified (markC (thetaGA B.bA F ρ)) hadm.2.1 hA₂
      hx0M hx1M htauM hToddM v
  have hsec := x0Section_bijective_ramified (markC (thetaGA B.bA F ρ)) hadm.2.1 hadm.2.2.1
    hA₂ hx0M hx1M htauM hToddM
  -- ===== stage 4: the section cocycles and the reindex map ψ =====
  set secC : (En.descData l h).Vmod →
      VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) := fun v =>
    ofZ1 hcomp (ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
    with hsecCdef
  set ψ : (En.descData l h).Vmod →
      (VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)
        ⧸ vCobRange (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)) := fun v =>
    QuotientAddGroup.mk (secC v) with hψdef
  -- ===== stage 5: ψ hits the x₀-supported section classes; bijectivity =====
  have hcoordψ : ∀ v, h1CoordGammaA B.bA F En l h ρ hcomp hcompat hA₂ (ψ v)
      = h1wMk (markC (thetaGA B.bA F ρ)) ⟨x0Supported v, hmem v⟩ := fun v => by
    show h1wMk (markC (thetaGA B.bA F ρ))
        (toZ1wHom (thetaGA B.bA F ρ) hcompat (toZ1 hcomp (secC v))) = _
    rw [show toZ1 hcomp (secC v)
        = ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩ from
        toZ1_ofZ1 hcomp _]
    rw [toZ1wHom_ofZ1w]
  have hψbij : Function.Bijective ψ := by
    constructor
    · intro v v' hvv'
      have h1 := congrArg (h1CoordGammaA B.bA F En l h ρ hcomp hcompat hA₂) hvv'
      rw [hcoordψ v, hcoordψ v'] at h1
      exact hsec.1 h1
    · intro x
      obtain ⟨v, hv⟩ := hsec.2 (h1CoordGammaA B.bA F En l h ρ hcomp hcompat hA₂ x)
      exact ⟨v, (h1CoordGammaA_bijective B.bA F En l h ρ hcomp hcompat hA₂).1
        ((hcoordψ v).trans hv)⟩
  -- ===== stage 6: the value on section classes is the Wall double =====
  have hdat : IsEquivariantFactorSet ((En.descData l h).qbar) (En.descData l h).dat :=
    En.hdat l h
  have hevalx : ∀ v : (En.descData l h).Vmod,
      eval (ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
        = x0Supported v := fun v => by
    have h2 := congrArg Subtype.val
      (toZ1wHom_ofZ1w (thetaGA B.bA F ρ) hcompat hθsurj hA₂ ⟨x0Supported v, hmem v⟩)
    rwa [toZ1wHom_coe] at h2
  have hσv : ∀ v, (gammaGen.map (graphSdHom (secC v))).σ.v = 0 := fun v => by
    show (secC v).c gammaGen.σ = 0
    exact congrFun (hevalx v) 0
  have hτv : ∀ v, (gammaGen.map (graphSdHom (secC v))).τ.v = 0 := fun v => by
    show (secC v).c gammaGen.τ = 0
    exact congrFun (hevalx v) 1
  have hx1v : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₁.v = 0 := fun v => by
    show (secC v).c gammaGen.x₁ = 0
    exact congrFun (hevalx v) 3
  have hx0v : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₀.v = v := fun v => by
    show (secC v).c gammaGen.x₀ = v
    exact congrFun (hevalx v) 2
  have hccσ : ∀ v, (gammaGen.map (graphSdHom (secC v))).σ.cc = c tameSigma := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.σ = c tameSigma
    rw [hround gammaGen.σ]
    calc thetaGA B.bA F ρ gammaGen.σ
        = c (B.tameA (quotientMk NA univMarking.σ)) := hfacρ _
      _ = c tameSigma := by rw [B.tameA_sigma]
  have hccτ : ∀ v, (gammaGen.map (graphSdHom (secC v))).τ.cc = c tameTau := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.τ = c tameTau
    rw [hround gammaGen.τ]
    calc thetaGA B.bA F ρ gammaGen.τ
        = c (B.tameA (quotientMk NA univMarking.τ)) := hfacρ _
      _ = c tameTau := by rw [B.tameA_tau]
  have hccx0 : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₀.cc = 1 := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.x₀ = 1
    rw [hround gammaGen.x₀]
    calc thetaGA B.bA F ρ gammaGen.x₀
        = c (B.tameA (quotientMk NA univMarking.x₀)) := hfacρ _
      _ = 1 := by rw [B.tameA_x0, map_one]
  have hccx1 : ∀ v, (gammaGen.map (graphSdHom (secC v))).x₁.cc = 1 := fun v => by
    show rho0 (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) gammaGen.x₁ = 1
    rw [hround gammaGen.x₁]
    calc thetaGA B.bA F ρ gammaGen.x₁
        = c (B.tameA (quotientMk NA univMarking.x₁)) := hfacρ _
      _ = 1 := by rw [B.tameA_x1, map_one]
  have hwild : ∀ v, (liftMark (gammaGen.map (graphSdHom (secC v)))
      (kappa0Cocycle (En.descData l h).dat hdat)).wildValue.fib
      = (En.descData l h).qbar v
        + polar (En.descData l h).qbar v (powOmega2 (c tameSigma) • v) := fun v => by
    have htaufS : ∀ w : (En.descData l h).Vmod,
        (gammaGen.map (graphSdHom (secC v))).τ.cc • w = w → w = 0 := fun w hw =>
      tau_fixed_eq_zero_of_gen (c tameSigma) (c tameTau) hgen hrelC hoddC hsimple hram w
        (by rwa [hccτ v] at hw)
    have hτoddS : Odd (orderOf (gammaGen.map (graphSdHom (secC v))).τ.cc) := by
      rw [hccτ v]
      exact hoddC
    have hqg0S : (En.descData l h).qbar
        ((Marking.g0 (sdBaseMarking (gammaGen.map (graphSdHom (secC v)))))⁻¹
          • (gammaGen.map (graphSdHom (secC v))).x₀.v)
        = (En.descData l h).qbar (gammaGen.map (graphSdHom (secC v))).x₀.v :=
      En.hinv l h _ _
    rw [liftMark_kappa0_wildValue_fib_ramified (En.descData l h).dat hdat
      (gammaGen.map (graphSdHom (secC v))) (hσv v) (hτv v) (hx1v v) (hccx0 v) (hccx1 v)
      hA₂ htaufS hτoddS hqg0S, hx0v v,
      show Marking.sigma2 (sdBaseMarking (gammaGen.map (graphSdHom (secC v))))
          = powOmega2 (c tameSigma) from congrArg powOmega2 (hccσ v)]
    exact congrArg (fun z => (En.descData l h).qbar v + z)
      (polar_smul_inv_eq (C := (En.descData l h).C0) (En.descData l h).qbar
        (powOmega2 (c tameSigma)) (fun w => En.hinv l h _ w) v)
  have hval : ∀ v, QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA (ψ v)
      = qDouble (En.qbar l h) (powOmega2 (c tameSigma) • ·) v := fun v => by
    show QZero (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) (secC v)
      = qDouble (En.qbar l h) (powOmega2 (c tameSigma) • ·) v
    haveI : ContinuousSMul GA (ZMod 2) :=
      inferInstanceAs (ContinuousSMul GammaA (ZMod 2))
    rw [QZero_eq_relZPair_kappa0 (fun x m => rfl) hdat (secC v),
      relZPair_kappa0_fst_eq_zero (En.descData l h).dat hdat _ (hσv v) (hτv v), zero_add]
    exact hwild v
  -- ===== stage 7: reindex and count =====
  calc ∑ᶠ x : VCocycle (En.descData l h) (rhoPrimeGA B.bA F En l h ρ)
        ⧸ vCobRange (En.descData l h) (rhoPrimeGA B.bA F En l h ρ),
      sign (QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA x)
      = ∑ᶠ v : (En.descData l h).Vmod,
          sign (qDouble (En.qbar l h) (powOmega2 (c tameSigma) • ·) v) := by
        refine (finsum_eq_of_bijective ψ hψbij fun v => ?_).symm
        show sign (qDouble (En.qbar l h) (powOmega2 (c tameSigma) • ·) v)
          = sign (QZeroBar (En.descData l h) (rhoPrimeGA B.bA F En l h ρ) htriv_gammaA (ψ v))
        rw [hval v]
    _ = (2 ^ m : ℤ) :=
      finsum_sign_ramified_of_action c hc hsimple hram (En.qbar l h)
        (En.hquad l h) (En.hns l h) (En.hinv l h) m hm hcard

/-- **`hGaussZA`, unramified case** (P-16d6e4aA A-4): with a per-lift tame package whose
inertia acts trivially on `V`, `GaussZResidue B.bA F En l h (−2^m)` — the `prop_8_9` ledger
hypothesis at the pinned unramified value, over the candidate source.  The
`gaussZResidue_local_unramified` twin: `gaussZ_reduction` at `Γ := GammaA` + the pinned seam;
`hfaith` is NOT taken (the `V^{C₀} = 0` freeness runs on `hfix_of_simple_nt`). -/
theorem gaussZResidue_gammaA_unramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hpack : ∀ ρ : BoundaryLifts B.bA F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
      Function.Surjective ⇑c ∧ (∀ g : GammaA, ρ.1.1 g = c (B.tameA g)) ∧
        ∀ v : En.Vmod, c tameTau • v = v) :
    GaussZResidue B.bA F En l h (-(2 ^ m : ℤ)) := by
  intro ρ
  classical
  obtain ⟨c, hc, hfacρ, hunram⟩ := hpack ρ
  set ρM := RF.rhoPrime B.bA F (En.radData l h) rfl ρ with hρMdef
  haveI hfinZ : Finite (VCocycle (En.descData l h) ρM) :=
    finite_vcocycle_gammaA B.bA F En l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective (fun γ : GammaA => rho0 (En.descData l h) ρM γ) := by
    intro y
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime B.bA F En l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (En.descData l h).Vmod,
      (∀ γ : GammaA, rho0 (En.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  calc ∑ᶠ cc : VCocycle (En.descData l h) ρM, sign (QZero (En.descData l h) ρM cc)
      = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ x, sign (QZeroBar (En.descData l h) ρM htriv_gammaA x) :=
        gaussZ_reduction htriv_gammaA hfix
    _ = (Nat.card En.Vmod : ℤ) * (-(2 ^ m : ℤ)) := by
        rw [sum_sign_QZeroBar_gammaA_unramified B F En hsimple hVne hnt m hm hcard l h
          ρ c hc hfacρ hunram]

/-- **`hGaussZA`, ramified case** (P-16d6e4aA A-4): with a per-lift tame package whose
inertia moves `V`, `GaussZResidue B.bA F En l h (+2^m)`. -/
theorem gaussZResidue_gammaA_ramified
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR)
    (hpack : ∀ ρ : BoundaryLifts B.bA F RF.TC, ∃ c : ContinuousMonoidHom Ttame RF.YC,
      Function.Surjective ⇑c ∧ (∀ g : GammaA, ρ.1.1 g = c (B.tameA g)) ∧
        ∃ v : En.Vmod, c tameTau • v ≠ v) :
    GaussZResidue B.bA F En l h (2 ^ m : ℤ) := by
  intro ρ
  classical
  obtain ⟨c, hc, hfacρ, hram⟩ := hpack ρ
  set ρM := RF.rhoPrime B.bA F (En.radData l h) rfl ρ with hρMdef
  haveI hfinZ : Finite (VCocycle (En.descData l h) ρM) :=
    finite_vcocycle_gammaA B.bA F En l h ρ hsimple hVne hnt
  have hsurjρ' : Function.Surjective (fun γ : GammaA => rho0 (En.descData l h) ρM γ) := by
    intro y
    obtain ⟨γ, hγ⟩ := ρ.1.2 y
    exact ⟨γ, (rho0_descData_rhoPrime B.bA F En l h ρ γ).trans hγ⟩
  have hfix : ∀ v : (En.descData l h).Vmod,
      (∀ γ : GammaA, rho0 (En.descData l h) ρM γ • v = v) → v = 0 :=
    fun v hv => hfix_of_simple_nt hsurjρ' hsimple hnt v hv
  calc ∑ᶠ cc : VCocycle (En.descData l h) ρM, sign (QZero (En.descData l h) ρM cc)
      = (Nat.card En.Vmod : ℤ)
          * ∑ᶠ x, sign (QZeroBar (En.descData l h) ρM htriv_gammaA x) :=
        gaussZ_reduction htriv_gammaA hfix
    _ = (Nat.card En.Vmod : ℤ) * (2 ^ m : ℤ) := by
        rw [sum_sign_QZeroBar_gammaA_ramified B F En hsimple hVne hnt m hm hcard l h
          ρ c hc hfacρ hram]

end Assembly

end AffineTLift

end SectionEight

end GQ2
