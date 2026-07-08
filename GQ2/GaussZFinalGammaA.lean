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

open CentralObstruction ContCoh WordCohBridge FoxH RStageGammaA WordCoh2

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
