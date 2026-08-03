/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModule

/-!
# Reflection for the module-valued degree-two word obstruction

This file supplies the splitting half left open by `Count.HTwoModule`.  At a finite
action-compatible factor of a continuous cocycle, a relator-fibre vector in the image of
the word differential can be killed by shifting the chosen generator lifts.  The shifted
marking remains admissible when the coefficient module has exponent two, so the marked
presentation extends it to a section of the twisted semidirect extension.  Reading the
fibre coordinate of that section exhibits the original cocycle as a continuous
coboundary.

The final theorem packages this argument behind a factor-local callback.  It is designed
to become `ModuleH2WordData.reflects_coboundary` once the global, choice-independent
obstruction map supplies that callback; it does not assume a splitting or add an axiom.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

/-! ## 1. Exponent-two fibres and admissible shifted markings -/

namespace ModuleExt

variable {L A : Type*} [Group L] [AddCommGroup A] [DistribMulAction L A]
  {z : ModuleTwoCocycle L A}

/-- An element of the identity fibre of a module extension squares to one when the
coefficient module has exponent two. -/
theorem sq_eq_one_of_g_eq_one (hA₂ : ∀ a : A, a + a = 0) {p : ModuleExt z}
    (hp : p.g = 1) : p ^ 2 = 1 := by
  rw [pow_two, (base_eq_one_iff p).mp hp, ← incl_add, hA₂, incl_zero]

end ModuleExt

section WildShift

variable {X : Type*} {L A : Type} [Group L] [AddCommGroup A] [DistribMulAction L A]

/-- Shifting a finite marking into a twisted module extension preserves admissibility when
the fibre is elementary `2`-torsion. -/
theorem isWildTwo_moduleLift {J : Set X} {m : X → L} (hwild : IsWildTwo J m)
    (z : ModuleTwoCocycle L A) (hA₂ : ∀ a : A, a + a = 0) (a : X → A) :
    IsWildTwo J (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) := by
  refine @isWildTwo_corrected X (ModuleExt z) L _ _ A
    (ModuleExt.baseProj z) (ModuleExt.incl z) (fun _ => rfl)
    m (ModuleExt.lift z m) (fun _ => rfl) J hwild ?_ a
  intro p hp
  rw [← pow_two]
  exact ModuleExt.sq_eq_one_of_g_eq_one hA₂ hp

end WildShift

/-! ## 2. A section extracts a module coboundary -/

section SectionCoboundary

variable {G L A : Type*} [Group G] [TopologicalSpace G]
  [Group L] [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [DistribMulAction L A]

/-- A continuous section of a twisted module extension exhibits its pulled-back cocycle as
a coboundary.  The splitting cochain is the negative of the fibre coordinate; using the
negative makes this statement valid without an exponent-two assumption. -/
theorem moduleCocycle_mem_B2 {z : ModuleTwoCocycle L A}
    (sect : ContinuousMonoidHom G (ModuleExt z))
    (hact : ∀ (g : G) (a : A), g • a = (sect g).g • a) :
    (fun p : G × G => z.κ (sect p.1).g (sect p.2).g) ∈ B2 G A := by
  refine ⟨fun g => -(sect g).u, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_C1_iff]
    exact (continuous_of_discreteTopology (f := fun p : ModuleExt z => -p.u)).comp
      sect.continuous_toFun
  · funext p
    obtain ⟨g, h⟩ := p
    show g • (-(sect h).u) - (-(sect (g * h)).u) + (-(sect g).u) =
      z.κ (sect g).g (sect h).g
    rw [hact, map_mul sect]
    simp only [ModuleExt.mul_u, smul_neg]
    abel

end SectionCoboundary

/-! ## 3. Reflection at one finite action-compatible factor -/

section FiniteReflection

variable {iota rel : Type*} {Gamma L A : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [Finite A]
  [DistribMulAction Gamma A] [DistribMulAction L A]
  {gen : iota → Gamma} {W : rel → PWord iota} {w : rel → FreeGroup iota} {J : Set iota}

/-- **Finite-level module reflection.**  Suppose the normalized cocycle `f` factors through
`z : ModuleTwoCocycle L A`.  If the intrinsic relator-fibre vector of `z` lies in the range
of the word differential at the induced marking, then `f` is a continuous coboundary.

The proof shifts the zero-fibre generator lifts by the negative of a preimage of the
relator vector, uses `moduleWord_eval_shift` to kill the relators, and applies the
admissible extension clause.  The resulting section supplies the splitting cochain.
No section is assumed. -/
theorem mem_B2_of_moduleRelFam_mem_range_at_factor
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (pi : ContinuousMonoidHom Gamma L)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = pi g • a)
    (hres : ResolvesAt W w (WordLift A L))
    (hwild : IsWildTwo J (fun i => pi (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (z : ModuleTwoCocycle L A) (f : Z2 Gamma A)
    (hfactor : ∀ x y : Gamma, moduleNormalize f.1 (x, y) = z.κ (pi x) (pi y))
    (hobs : (fun k => moduleRel (W k) (fun i => pi (gen i)) z) ∈
      (heisD1 (A := A) (fun i => pi (gen i)) w).range) :
    f.1 ∈ B2 Gamma A := by
  obtain ⟨a, ha⟩ := hobs
  let m₀ : iota → ModuleExt z := fun i =>
    ModuleExt.incl z (-a i) * ModuleExt.lift z (fun j => pi (gen j)) i
  have hrelBase : ∀ k, PWord.eval (fun i => pi (gen i)) (W k) = 1 :=
    fun k => hpres.rel pi k
  have hrel : ∀ k, PWord.eval m₀ (W k) = 1 := by
    intro k
    rw [show m₀ = (fun i => ModuleExt.incl z ((-a) i) *
        ModuleExt.lift z (fun j => pi (gen j)) i) from rfl]
    rw [moduleWord_eval_shift W w (fun i => pi (gen i)) z hres (-a) k,
      moduleWord_eval_lift_eq_incl (W k) (fun i => pi (gen i)) z (hrelBase k),
      ← ModuleExt.incl_add]
    have hk := congrFun ha k
    rw [map_neg]
    simp only [Pi.neg_apply]
    rw [hk, neg_add_cancel, ModuleExt.incl_zero]
  have hwild' : IsWildTwo J m₀ := by
    rw [show m₀ = (fun i => ModuleExt.incl z ((-a) i) *
        ModuleExt.lift z (fun j => pi (gen j)) i) from rfl]
    exact isWildTwo_moduleLift hwild z hA₂ (-a)
  obtain ⟨sect, hsect⟩ := hpres.extend m₀ hrel hwild'
  have hbase : ∀ g : Gamma, (sect g).g = pi g := by
    let proj : ContinuousMonoidHom (ModuleExt z) L :=
      ⟨ModuleExt.baseProj z, continuous_of_discreteTopology⟩
    have hcomp : proj.comp sect = pi := by
      refine eq_of_eqOn_gen hpres.gen_top fun i => ?_
      show (sect (gen i)).g = pi (gen i)
      rw [hsect i]
      simp [m₀]
    exact fun g => DFunLike.congr_fun hcomp g
  have hnB2 : moduleNormalize f.1 ∈ B2 Gamma A := by
    have heq : moduleNormalize f.1 =
        fun p : Gamma × Gamma => z.κ (sect p.1).g (sect p.2).g := by
      funext p
      rw [hbase, hbase]
      exact hfactor p.1 p.2
    rw [heq]
    apply moduleCocycle_mem_B2 sect
    intro g b
    rw [hbase]
    exact hcompat g b
  have hcorr : f.1 - moduleNormalize f.1 ∈ B2 Gamma A :=
    sub_moduleNormalize_mem_B2 f.1
  rw [show f.1 = (f.1 - moduleNormalize f.1) + moduleNormalize f.1 by abel]
  exact AddSubgroup.add_mem _ hcorr hnB2

end FiniteReflection

/-! ## 4. Reflection through the canonical finite-factor supply -/

section FactorReflection

variable {iota rel : Type*} {Gamma A C : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [Group C] [TopologicalSpace C] [DiscreteTopology C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A] [DistribMulAction C A]
  {gen : iota → Gamma} {W : rel → PWord iota} {w : rel → FreeGroup iota} {J : Set iota}

/-- **Callback-shaped global reflection theorem.**  The action-compatible factorization theorem
chooses a finite quotient `Gamma/V` and a normalized module cocycle `z` on it.  The callback
must provide exactly the two source-dependent facts at that chosen factor:

* the selected free word resolves the profinite relator in `WordLift A (Gamma/V)`;
* the resulting intrinsic relator-fibre vector lies in `range heisD1`.

Everything after those facts is canonical and is discharged by
`mem_B2_of_moduleRelFam_mem_range_at_factor`.  Thus a choice-independent global obstruction
map can instantiate `ModuleH2WordData.reflects_coboundary` by proving this callback, without
repeating any splitting argument. -/
theorem mem_B2_of_moduleFactor_rel_mem_range
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0) (f : Z2 Gamma A)
    (hlocal : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
      ∀ z : ModuleTwoCocycle (Gamma ⧸ V.toSubgroup) A,
        (∀ x y : Gamma, moduleNormalize f.1 (x, y) =
          z.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y)) →
        ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)) ∧
        (fun k => moduleRel (W k)
          (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) z) ∈
          (heisD1 (A := A) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) w).range) :
    f.1 ∈ B2 Gamma A := by
  obtain ⟨V, hV, z, hfactor⟩ := exists_moduleTwoCocycle_factor rho hcompat f
  let rhoV : (Gamma ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
  obtain ⟨hres, hobs⟩ := hlocal V hV z hfactor
  let piV : ContinuousMonoidHom Gamma (Gamma ⧸ V.toSubgroup) :=
    GQ2.quotientMk V.toSubgroup
  have hcompatV : ∀ (g : Gamma) (a : A), g • a = piV g • a := by
    intro g a
    change g • a = rhoV (QuotientGroup.mk' V.toSubgroup g) • a
    rw [quotientActionHom_mk rho V hV g]
    exact hcompat g a
  exact mem_B2_of_moduleRelFam_mem_range_at_factor hpres piV hcompatV hres
    (hwildLevel V) hA₂ z f hfactor hobs

/-- **Ready-to-install reflection field.**  Let `obstruction` be a global additive
relator-vector map.  If it reads, at every action-compatible finite factor supplied by
`exists_moduleTwoCocycle_factor`, as that factor's intrinsic `moduleRel` vector, and the
word family resolves at those factor targets, then membership of `obstruction f` in the
fixed word differential forces `f` to be a coboundary.

The conclusion is definitionally the type of `ModuleH2WordData.reflects_coboundary` for
the fixed marking `i ↦ rho (gen i)`.  The `heisD1_map_base` step below is the precise bridge
from the quotient marking chosen by finite factorization back to that fixed marking. -/
theorem reflects_coboundary_of_moduleFactor_read
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i => QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (obstruction : Z2 Gamma A →+ (rel → A))
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)))
    (hread : ∀ (f : Z2 Gamma A) (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
      ∀ z : ModuleTwoCocycle (Gamma ⧸ V.toSubgroup) A,
        (∀ x y : Gamma, moduleNormalize f.1 (x, y) =
          z.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y)) →
        obstruction f = fun k => moduleRel (W k)
          (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) z) :
    ∀ f : Z2 Gamma A,
      obstruction f ∈ (heisD1 (A := A) (fun i => rho (gen i)) w).range →
      f.1 ∈ B2 Gamma A := by
  intro f hf
  apply mem_B2_of_moduleFactor_rel_mem_range hpres rho hcompat hwildLevel hA₂ f
  intro V hV
  dsimp only
  let rhoV : (Gamma ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
  intro z hfactor
  refine ⟨hresolve V hV, ?_⟩
  rw [← hread f V hV z hfactor]
  obtain ⟨a, ha⟩ := hf
  refine ⟨a, ?_⟩
  have hd1 :
      heisD1 (A := A) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) w =
        heisD1 (A := A) (fun i => rho (gen i)) w := by
    calc
      _ = heisD1 (A := A)
          (fun i => rhoV (QuotientGroup.mk' V.toSubgroup (gen i))) w :=
        heisD1_map_base rhoV (fun _ _ => rfl)
          (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) w
      _ = _ := by
        congr 2
  calc
    heisD1 (A := A) (fun i => QuotientGroup.mk' V.toSubgroup (gen i)) w a =
        heisD1 (A := A) (fun i => rho (gen i)) w a := DFunLike.congr_fun hd1 a
    _ = obstruction f := ha

end FactorReflection

end GQ2.Dyadic.Count
