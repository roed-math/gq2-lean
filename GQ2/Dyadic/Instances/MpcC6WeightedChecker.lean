/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.MpcMarkedSixCertificate

/-!
A bounded prototype of a reflected collector for the one remaining Mpc class-six equality.
The syntax has only the four marked generators, multiplication, inverse, squaring, and the
paper commutator.  `depth` is the guaranteed two-central-series depth; the checker may erase
any subword of depth at least six.
-/

namespace GQ2.Dyadic.Instances.MpcC6WeightedChecker

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.Instances.MpcOrb
open GQ2.Dyadic.SqCore
open GQ2.Roe.Labute
open scoped commutatorElement

inductive Gen4 where
  | A | B | C | D
  deriving DecidableEq, Repr

inductive CWord where
  | one
  | gen (g : Gen4)
  | mul (x y : CWord)
  | inv (x : CWord)
  | sq (x : CWord)
  | comm (x y : CWord)
  deriving DecidableEq, Repr

namespace CWord

/-- The lower bound on two-central depth represented by a word.  `one` is assigned depth six
because this checker is intentionally specialized to `Q₆`; all other clauses are the exact
power/commutator filtration rules. -/
def depth : CWord → Nat
  | .one => 6
  | .gen _ => 1
  | .mul x y => min x.depth y.depth
  | .inv x => x.depth
  | .sq x => x.depth + 1
  | .comm x y => x.depth + y.depth

def eval {G : Type*} [Group G] (val : Gen4 → G) : CWord → G
  | .one => 1
  | .gen g => val g
  | .mul x y => eval val x * eval val y
  | .inv x => (eval val x)⁻¹
  | .sq x => eval val x ^ 2
  | .comm x y => commP (eval val x) (eval val y)

/-- The fixed `M₂` relation on `A,B,C,D`, reflected in the small syntax. -/
def mRel : CWord :=
  .mul (.mul (.mul (.sq (.gen .A)) (.comm (.gen .A) (.gen .B)))
    (.sq (.sq (.gen .C)))) (.comm (.gen .C) (.gen .D))

theorem eval_mRel {G : Type*} [Group G] (val : Gen4 → G) :
    eval val mRel = mWord 2 (val .A) (val .B) (val .C) (val .D) := by
  simp only [mRel, eval, mWord, show (2 : Nat) ^ 2 = 4 from rfl]
  rw [show (val .C ^ 2) ^ 2 = val .C ^ 4 by norm_num [← pow_mul]]

/-- Every reflected word evaluates at the filtration depth computed by `depth`.  This is the
kernel-facing fact that makes the deep-term rule trustworthy. -/
theorem eval_mem_twoCentralSeries
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (val : Gen4 → G) : ∀ w : CWord, eval val w ∈ twoCentralSeries G w.depth := by
  intro w
  induction w with
  | one => exact Subgroup.one_mem _
  | gen g => exact Subgroup.mem_top _
  | mul x y hx hy =>
      exact Subgroup.mul_mem _
        (twoCentralSeries_antitone (G := G) (Nat.min_le_left _ _) hx)
        (twoCentralSeries_antitone (G := G) (Nat.min_le_right _ _) hy)
  | inv x hx => exact Subgroup.inv_mem _ hx
  | sq x hx => exact sq_mem_twoCentralSeries_succ G hx
  | comm x y hx hy =>
      change commP (eval val x) (eval val y) ∈
        twoCentralSeries G (x.depth + y.depth)
      rw [show commP (eval val x) (eval val y) =
          ⁅(eval val x)⁻¹, (eval val y)⁻¹⁆ by
        simp only [commP, commutatorElement_def, inv_inv]]
      exact commutator_mem_twoCentralSeries_add (G := G)
        (Subgroup.inv_mem _ hx) (Subgroup.inv_mem _ hy)

/-- Evaluation commutes with a group homomorphism. -/
theorem eval_map
    {G H : Type*} [Group G] [Group H] (f : G →* H) (val : Gen4 → G) :
    ∀ w : CWord, eval (fun g ↦ f (val g)) w = f (eval val w) := by
  intro w
  induction w with
  | one => exact (map_one f).symm
  | gen g => rfl
  | mul x y hx hy => simp only [eval, hx, hy, map_mul]
  | inv x hx => simp only [eval, hx, map_inv]
  | sq x hx => simp only [eval, hx, map_pow]
  | comm x y hx hy => simp only [eval, hx, hy, commP, map_mul, map_inv]

/-- The semantic interface used by the checker.  It exposes exactly the two quotient facts it
needs: the marked `M₂` relation and vanishing beyond class five. -/
structure Model (Q : Type*) [Group Q] where
  val : Gen4 → Q
  rel : eval val mRel = 1
  deep : ∀ w, 6 ≤ w.depth → eval val w = 1

/-- The relation-free part of a class-six model.  This is the exact interface needed by
derivations which never invoke `Deriv.rel`. -/
structure DeepModel (Q : Type*) [Group Q] where
  val : Gen4 → Q
  deep : ∀ w, 6 ≤ w.depth → eval val w = 1

def Model.toDeepModel {Q : Type*} [Group Q] (M : Model Q) : DeepModel Q where
  val := M.val
  deep := M.deep

/-- Any topological group, mapped to its sixth level quotient, supplies the deep-term rule.
Only the fixed relation remains as an input. -/
noncomputable def towerModel
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (val : Gen4 → G) (hrel : levelMk G 6 (eval val mRel) = 1) :
    Model (levelQuot G 6) where
  val := fun g ↦ levelMk G 6 (val g)
  rel := by
    rw [eval_map (levelMk G 6) val mRel]
    exact hrel
  deep := by
    intro w hw
    rw [eval_map (levelMk G 6) val w]
    apply (lim_mem_twoCentralSeries_iff_levelMk (G := G) 6 (eval val w)).mp
    exact twoCentralSeries_antitone (G := G) hw (eval_mem_twoCentralSeries val w)

/-- The concrete class-six model on the marked generators of `D_M(2,0)`. -/
noncomputable def dmModel : Model (levelQuot (DM 2 0 : Type) 6) :=
  towerModel (G := (DM 2 0 : Type))
    (fun | .A => dmA 2 0 | .B => dmB 2 0 | .C => dmC 2 0 | .D => dmD 2 0) (by
      rw [eval_mRel, mpcOrb_relation, map_one])

private theorem commute_of_commP_eq_one {Q : Type*} [Group Q] {a b : Q}
    (h : commP a b = 1) : Commute a b := by
  change a * b = b * a
  simp only [commP] at h
  have hc : b⁻¹ * a * b = a := by
    calc
      b⁻¹ * a * b = a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = a := by rw [h, mul_one]
  calc
    a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [hc]

private theorem deep_commute {Q : Type*} [Group Q] (M : DeepModel Q)
    (x y : CWord) (h : 6 ≤ x.depth + y.depth) :
    Commute (eval M.val x) (eval M.val y) := by
  apply commute_of_commP_eq_one
  simpa only [eval] using M.deep (.comm x y) (by simpa only [depth] using h)

private theorem deep_inv_self {Q : Type*} [Group Q] (M : DeepModel Q)
    (x : CWord) (h : 5 ≤ x.depth) : (eval M.val x)⁻¹ = eval M.val x := by
  have hs : eval M.val x ^ 2 = 1 := by
    simpa only [eval] using M.deep (.sq x) (by simpa only [depth] using Nat.succ_le_succ h)
  calc
    (eval M.val x)⁻¹ = (eval M.val x)⁻¹ * 1 := by group
    _ = (eval M.val x)⁻¹ * eval M.val x ^ 2 := by rw [hs]
    _ = eval M.val x := by group

private theorem depth_pos (x : CWord) : 1 ≤ x.depth := by
  induction x <;> simp only [depth] at * <;> omega

private theorem conj_eq_self_of_commute {Q : Type*} [Group Q] {a b : Q}
    (h : Commute a b) : b⁻¹ * a * b = a := by
  calc
    b⁻¹ * a * b = b⁻¹ * (a * b) := by group
    _ = b⁻¹ * (b * a) := by rw [h.eq]
    _ = a := by group

private theorem comm_inv_snd_sound {Q : Type*} [Group Q] (M : DeepModel Q)
    (x y z : CWord) (h : 5 ≤ x.depth + y.depth + z.depth) :
    commP (commP (eval M.val x) (eval M.val y)⁻¹) (eval M.val z) =
      commP (commP (eval M.val x) (eval M.val y)) (eval M.val z) := by
  let a := eval M.val x
  let b := eval M.val y
  let c := eval M.val z
  let w := commP a b
  let u := commP w c
  let ζ := commP b⁻¹ w
  have hypos := depth_pos y
  have hxy : 2 ≤ x.depth + y.depth := by
    have := depth_pos x
    omega
  have huInv : u⁻¹ = u := by
    simpa only [eval] using deep_inv_self M (.comm (.comm x y) z) (by
      simpa only [depth, add_assoc] using h)
  have hζz : commP ζ c = 1 := by
    simpa only [eval] using M.deep (.comm (.comm (.inv y) (.comm x y)) z) (by
      simp only [depth]
      omega)
  have hcor : commP u⁻¹ w⁻¹ = 1 := by
    simpa only [eval] using
      M.deep (.comm (.inv (.comm (.comm x y) z)) (.inv (.comm x y))) (by
        simp only [depth]
        omega)
  have hA : commP a b⁻¹ = ζ * w⁻¹ := by
    simp only [a, b, w, ζ, commP]
    group
  have hmul : commP (ζ * w⁻¹) c =
      (commP ζ c * commP (commP ζ c) w⁻¹) * commP w⁻¹ c := by
    simp only [commP]
    group
  have hinv : commP w⁻¹ c = u⁻¹ * commP u⁻¹ w⁻¹ := by
    simp only [u, commP]
    group
  have hone : commP (1 : Q) w⁻¹ = 1 := by
    simp only [commP]
    group
  change commP (commP a b⁻¹) c = u
  rw [hA, hmul, hζz, hone, one_mul, hinv, hcor, mul_one, huInv]
  exact one_mul u

private theorem hallWitt {Q : Type*} [Group Q] (a b c : Q) :
    b⁻¹ * commP (commP a b⁻¹) c * b *
        (c⁻¹ * commP (commP b c⁻¹) a * c) *
      (a⁻¹ * commP (commP c a⁻¹) b * a) = 1 := by
  simp only [commP]
  group

private theorem jacobi_sound {Q : Type*} [Group Q] (M : DeepModel Q)
    (x y z : CWord) (h : 5 ≤ x.depth + y.depth + z.depth) :
    eval M.val (.mul (.mul (.comm (.comm x y) z) (.comm (.comm y z) x))
      (.comm (.comm z x) y)) = 1 := by
  let a := eval M.val x
  let b := eval M.val y
  let c := eval M.val z
  let u := commP (commP a b) c
  let v := commP (commP b c) a
  let w := commP (commP c a) b
  have hxpos := depth_pos x
  have hypos := depth_pos y
  have hzpos := depth_pos z
  have h1 : commP (commP a b⁻¹) c = u := comm_inv_snd_sound M x y z h
  have h2 : commP (commP b c⁻¹) a = v := comm_inv_snd_sound M y z x (by omega)
  have h3 : commP (commP c a⁻¹) b = w := comm_inv_snd_sound M z x y (by omega)
  have huComm : Commute u b := by
    simpa only [eval] using deep_commute M (.comm (.comm x y) z) y (by
      simp only [depth]
      omega)
  have hvComm : Commute v c := by
    simpa only [eval] using deep_commute M (.comm (.comm y z) x) z (by
      simp only [depth]
      omega)
  have hwComm : Commute w a := by
    simpa only [eval] using deep_commute M (.comm (.comm z x) y) x (by
      simp only [depth]
      omega)
  have hHW := hallWitt a b c
  rw [h1, h2, h3, conj_eq_self_of_commute huComm,
    conj_eq_self_of_commute hvComm, conj_eq_self_of_commute hwComm] at hHW
  simpa only [eval, a, b, c, u, v, w] using hHW

/-! A tiny proof-producing checker.  Congruence is recursive; `swap`, the exact free collection
identities, and the inverse/cleanup identities used by the generated trace are proved from group
laws.  `deep` deletes a term only after the Boolean depth check. -/

inductive Deriv where
  | refl (w : CWord)
  | deep (w : CWord)
  | rel
  | symm (d : Deriv)
  | trans (d e : Deriv)
  | mul (d e : Deriv)
  | inv (d : Deriv)
  | sq (d : Deriv)
  | comm (d e : Deriv)
  | assoc (x y z : CWord)
  | one_mul (x : CWord)
  | mul_one (x : CWord)
  | inv_mul (x : CWord)
  | mul_inv (x : CWord)
  | swap (x y : CWord)
  | comm_mul_left (x z y : CWord)
  | comm_mul_right (x y z : CWord)
  | sq_mul (x y : CWord)
  | comm_inv_left (x y : CWord)
  | comm_inv_right (x y : CWord)
  | comm_self (x : CWord)
  | inv_sq (x : CWord)
  | inv_comm (x y : CWord)
  | mul_self (x : CWord)
  | one_comm (x : CWord)
  | comm_one (x : CWord)
  | sq_one
  | inv_one
  | jacobi (x y z : CWord)
  deriving Repr

namespace Deriv

mutual
  def lhs : Deriv → CWord
    | .refl w | .deep w => w
    | .rel => mRel
    | .symm d => d.rhs
    | .trans d _ => d.lhs
    | .mul d e => .mul d.lhs e.lhs
    | .inv d => .inv d.lhs
    | .sq d => .sq d.lhs
    | .comm d e => .comm d.lhs e.lhs
    | .assoc x y z => .mul (.mul x y) z
    | .one_mul x => .mul .one x
    | .mul_one x => .mul x .one
    | .inv_mul x => .mul (.inv x) x
    | .mul_inv x => .mul x (.inv x)
    | .swap x y => .mul x y
    | .comm_mul_left x z y => .comm (.mul x z) y
    | .comm_mul_right x y z => .comm x (.mul y z)
    | .sq_mul x y => .sq (.mul x y)
    | .comm_inv_left x y => .comm (.inv x) y
    | .comm_inv_right x y => .comm x (.inv y)
    | .comm_self x => .comm x x
    | .inv_sq x => .inv (.sq x)
    | .inv_comm x y => .inv (.comm x y)
    | .mul_self x => .mul x x
    | .one_comm x => .comm .one x
    | .comm_one x => .comm x .one
    | .sq_one => .sq .one
    | .inv_one => .inv .one
    | .jacobi x y z =>
        .mul (.mul (.comm (.comm x y) z) (.comm (.comm y z) x)) (.comm (.comm z x) y)

  def rhs : Deriv → CWord
    | .refl w => w
    | .deep _ | .rel => .one
    | .symm d => d.lhs
    | .trans _ e => e.rhs
    | .mul d e => .mul d.rhs e.rhs
    | .inv d => .inv d.rhs
    | .sq d => .sq d.rhs
    | .comm d e => .comm d.rhs e.rhs
    | .assoc x y z => .mul x (.mul y z)
    | .one_mul x | .mul_one x => x
    | .inv_mul _ | .mul_inv _ => .one
    | .swap x y => .mul (.mul y x) (.comm x y)
    | .comm_mul_left x z y =>
        .mul (.mul (.comm x y) (.comm (.comm x y) z)) (.comm z y)
    | .comm_mul_right x y z =>
        .mul (.mul (.comm x z) (.comm x y)) (.comm (.comm x y) z)
    | .sq_mul x y =>
        .mul (.mul (.mul (.sq x) (.sq y)) (.comm y x)) (.comm (.comm y x) y)
    | .comm_inv_left x y =>
        .mul (.inv (.comm x y)) (.comm (.inv (.comm x y)) (.inv x))
    | .comm_inv_right x y =>
        .mul (.inv (.comm x y)) (.comm (.inv (.comm x y)) (.inv y))
    | .comm_self _ => .one
    | .inv_sq x => .sq (.inv x)
    | .inv_comm x y => .comm y x
    | .mul_self x => .sq x
    | .one_comm _ | .comm_one _ | .sq_one | .inv_one => .one
    | .jacobi _ _ _ => .one
end

def check : Deriv → Bool
  | .refl _ | .rel | .assoc _ _ _ | .one_mul _ | .mul_one _ | .inv_mul _ |
      .mul_inv _ | .swap _ _ | .comm_mul_left _ _ _ | .comm_mul_right _ _ _ |
      .sq_mul _ _ | .comm_inv_left _ _ | .comm_inv_right _ _ | .comm_self _ |
      .inv_sq _ | .inv_comm _ _ | .mul_self _ | .one_comm _ | .comm_one _ |
      .sq_one | .inv_one => true
  | .jacobi x y z => decide (5 ≤ x.depth + y.depth + z.depth)
  | .deep w => decide (6 ≤ w.depth)
  | .symm d | .inv d | .sq d => d.check
  | .trans d e => d.check && e.check && decide (d.rhs = e.lhs)
  | .mul d e | .comm d e => d.check && e.check

/-- Whether a derivation avoids the presentation-relation rule. -/
def noRel : Deriv → Bool
  | .rel => false
  | .symm d | .inv d | .sq d => d.noRel
  | .trans d e | .mul d e | .comm d e => d.noRel && e.noRel
  | _ => true

/-- Compose a nonempty generated trace into one reflected derivation. -/
def chain : List Deriv → Deriv
  | [] => .refl .one
  | [d] => d
  | d :: ds => .trans d (chain ds)

/-- Soundness for relation-free derivations in an arbitrary class-six deep model. -/
theorem soundNoRel {Q : Type*} [Group Q] (M : DeepModel Q) :
    ∀ d : Deriv, d.check = true → d.noRel = true →
      eval M.val d.lhs = eval M.val d.rhs := by
  intro d hd hn
  induction d with
  | refl w => rfl
  | deep w => exact M.deep w (of_decide_eq_true hd)
  | rel => simp [noRel] at hn
  | symm d ih => exact (ih hd hn).symm
  | trans d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      have hs' := Bool.and_eq_true_iff.mp hs.1
      have hnr := Bool.and_eq_true_iff.mp hn
      have hmid : d.rhs = e.lhs := of_decide_eq_true hs.2
      exact (ihd hs'.1 hnr.1).trans
        ((congrArg (eval M.val) hmid).trans (ihe hs'.2 hnr.2))
  | mul d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      have hnr := Bool.and_eq_true_iff.mp hn
      simp only [lhs, rhs, eval]
      rw [ihd hs.1 hnr.1, ihe hs.2 hnr.2]
  | inv d ih =>
      simp only [lhs, rhs, eval]
      rw [ih hd hn]
  | sq d ih =>
      simp only [lhs, rhs, eval]
      rw [ih hd hn]
  | comm d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      have hnr := Bool.and_eq_true_iff.mp hn
      simp only [lhs, rhs, eval]
      rw [ihd hs.1 hnr.1, ihe hs.2 hnr.2]
  | assoc x y z => simp only [lhs, rhs, eval, mul_assoc]
  | one_mul x => exact _root_.one_mul (eval M.val x)
  | mul_one x => exact _root_.mul_one (eval M.val x)
  | inv_mul x => simp only [lhs, rhs, eval, inv_mul_cancel]
  | mul_inv x => simp only [lhs, rhs, eval, mul_inv_cancel]
  | swap x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_mul_left x z y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_mul_right x y z =>
      simp only [lhs, rhs, eval, commP]
      group
  | sq_mul x y =>
      simp only [lhs, rhs, eval, commP, pow_two]
      group
  | comm_inv_left x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_inv_right x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_self x =>
      simp only [lhs, rhs, eval, commP]
      group
  | inv_sq x =>
      simp only [lhs, rhs, eval, pow_two]
      group
  | inv_comm x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | mul_self x => simp only [lhs, rhs, eval, pow_two]
  | one_comm x =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_one x =>
      simp only [lhs, rhs, eval, commP]
      group
  | sq_one => simp only [lhs, rhs, eval, one_pow]
  | inv_one =>
      simp only [lhs, rhs, eval]
      group
  | jacobi x y z => exact jacobi_sound M x y z (of_decide_eq_true hd)

/-- Soundness of the reflected derivation checker.  In particular, no result of an external
collector is trusted: it must be replayed as a `Deriv` whose Boolean check reduces to `true`. -/
theorem sound {Q : Type*} [Group Q] (M : Model Q) :
    ∀ d : Deriv, d.check = true → eval M.val d.lhs = eval M.val d.rhs := by
  intro d hd
  induction d with
  | refl w => rfl
  | deep w =>
      exact M.deep w (of_decide_eq_true hd)
  | rel => exact M.rel
  | symm d ih => exact (ih hd).symm
  | trans d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      have hs' := Bool.and_eq_true_iff.mp hs.1
      have hmid : d.rhs = e.lhs := of_decide_eq_true hs.2
      exact (ihd hs'.1).trans ((congrArg (eval M.val) hmid).trans (ihe hs'.2))
  | mul d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      simp only [lhs, rhs, eval]
      rw [ihd hs.1, ihe hs.2]
  | inv d ih =>
      simp only [lhs, rhs, eval]
      rw [ih hd]
  | sq d ih =>
      simp only [lhs, rhs, eval]
      rw [ih hd]
  | comm d e ihd ihe =>
      have hs := Bool.and_eq_true_iff.mp hd
      simp only [lhs, rhs, eval]
      rw [ihd hs.1, ihe hs.2]
  | assoc x y z => simp only [lhs, rhs, eval, mul_assoc]
  | one_mul x => exact _root_.one_mul (eval M.val x)
  | mul_one x => exact _root_.mul_one (eval M.val x)
  | inv_mul x => simp only [lhs, rhs, eval, inv_mul_cancel]
  | mul_inv x => simp only [lhs, rhs, eval, mul_inv_cancel]
  | swap x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_mul_left x z y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_mul_right x y z =>
      simp only [lhs, rhs, eval, commP]
      group
  | sq_mul x y =>
      simp only [lhs, rhs, eval, commP, pow_two]
      group
  | comm_inv_left x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_inv_right x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_self x =>
      simp only [lhs, rhs, eval, commP]
      group
  | inv_sq x =>
      simp only [lhs, rhs, eval, pow_two]
      group
  | inv_comm x y =>
      simp only [lhs, rhs, eval, commP]
      group
  | mul_self x =>
      simp only [lhs, rhs, eval, pow_two]
  | one_comm x =>
      simp only [lhs, rhs, eval, commP]
      group
  | comm_one x =>
      simp only [lhs, rhs, eval, commP]
      group
  | sq_one => simp only [lhs, rhs, eval, one_pow]
  | inv_one =>
      simp only [lhs, rhs, eval]
      group
  | jacobi x y z => exact jacobi_sound M.toDeepModel x y z (of_decide_eq_true hd)

/-! One nontrivial checked derivation: a weight-five term commuted with a generator is erased
in `Q₆`, and the deletion is valid inside a surrounding product. -/

def weightFive : CWord := .comm (.sq (.sq (.comm (.gen .B) (.gen .D)))) (.gen .A)

def checkedExample : Deriv :=
  .mul (.refl (.gen .C)) (.deep (.comm weightFive (.gen .D)))

example : checkedExample.check = true := by decide

theorem checkedExample_sound :
    eval dmModel.val checkedExample.lhs = eval dmModel.val checkedExample.rhs :=
  sound dmModel checkedExample (by decide)

#print axioms eval_mem_twoCentralSeries
#print axioms sound
#print axioms checkedExample_sound

end Deriv
end CWord

end GQ2.Dyadic.Instances.MpcC6WeightedChecker
