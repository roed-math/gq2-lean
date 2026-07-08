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

end Kappa0Ledger

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
  sorry

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
  sorry

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
