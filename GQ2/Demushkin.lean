import Mathlib
import GQ2.CupProduct
import GQ2.MaxProP

/-!
# `IsDemushkin`: Demushkin pro-`p` groups  (ticket T-09, plan item B3a)

A profinite pro-`p` group `G` is **Demushkin** (Serre, *Galois Cohomology* I §4.5; NSW
Def. 3.9.9; Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967)) if, for
`𝔽_p`-coefficients with the trivial action,

1. `H¹(G, 𝔽_p)` is finite (equivalently `G` is topologically finitely generated — Burnside
   basis, NSW 3.9.1; we do not carry the redundant generation clause),
2. `dim_{𝔽_p} H²(G, 𝔽_p) = 1`, and
3. the cup product `H¹ × H¹ → H²` is a non-degenerate bilinear form.

This is the definition behind the paper's B3/B4 leaves: `G_{ℚ₂}(2) = maxProPQuotient 2 AbsGalQ2`
is Demushkin of rank 3 with `q = 2` (NSW Thm 7.5.11(ii); to be stated at T-08/T-10).

## Encoding

* Cohomology is `GQ2.ContCoh` (T-02) with coefficients the *literal* `ZMod p`; following the
  T-02 note, dimension conditions are phrased via `Nat.card` — `H¹`/`H²` are `p`-torsion, so
  finiteness forces `Nat.card = p ^ dim` (`IsDemushkin.card_H1_eq_pow`), and clause 2 becomes
  `Nat.card (H2 G (ZMod p)) = p`.  The **rank** is recovered as
  `demushkinRank p G := padicValNat p (Nat.card (H1 G (ZMod p)))`.
* The cup form is T-04's `cup11` relative to the multiplication pairing
  `AddMonoidHom.mul : ZMod p →+ ZMod p →+ ZMod p` (`trivialCupPairing`); non-degeneracy is
  stated **two-sidedly** (`nondegen_left`/`nondegen_right`) since graded-commutativity of
  `cup11` is not formalized — for `p = 2` the form is symmetric and the clauses coincide, and
  in the literature each implies the other by finite-dimensional linear algebra.
* The trivial action enters as in T-02/T-13: the ambient `[DistribMulAction G (ZMod p)]`
  instance is *constrained* by the structure field `smul_trivial`.  (For `p = 2` every action
  is trivial — `Aut(ℤ/2) = 1` — so this is no restriction there.)  By proof irrelevance,
  `trivialCupPairing p G h₁` and `trivialCupPairing p G h₂` are definitionally equal, so the
  non-degeneracy clauses can be consumed with any proof of triviality
  (`IsDemushkin.nondegen_left'`).
* `isProP` is T-05's predicate; profiniteness of `G` is ambient, entering only through the
  instances a caller supplies.

## Stress tests

* **Positive** (`isDemushkin_cyclicTwo`): `ℤ/2` is Demushkin of rank 1 — the unique *finite*
  Demushkin group (Serre GC I §4.5).  `H¹` and `H²` are computed explicitly (both
  `≃+ ZMod 2`), and the generator's cup square is the class of the 4-point cocycle
  `(g,h) ↦ c₀(g)·c₀(h)` — the extension class of `ℤ/4` — detected non-zero by the evaluation
  functional `f ↦ f(1,1) + f(σ,σ)`.  This exercises every field of the structure.
  `ℤ/2` is realized as `DihedralGroup 1` (as in the App. B tests), **not**
  `Multiplicative (ZMod 2)`: Mathlib's `Multiplicative.smul` transfer instance would make
  `g • m` mean multiplication in `ZMod 2`, clashing with the trivial coefficient action.
* **Negative** (`not_isDemushkin_punit`): the trivial group — the rank-0 *free* pro-`p` group —
  has `H² = 0`, so clause 2 fails (`Nat.card H² = 1 ≠ p`); free pro-`p` groups are the
  archetypal non-Demushkin groups (plan B3a: "`H² = 0`, pick cheap ones").
* The plan's `H¹(G,𝔽₂) ≃ ContinuousMonoidHom G 𝔽₂` sanity check is delivered wrapper-free, as
  in T-02: `ContCoh.H1equivZ1OfTrivial` composed with the explicit evaluation equivalence
  `z1CyclicTwoEquiv` (avoiding `Multiplicative`-wrapped hom-types).

Consumers: T-08 (`IsDemushkin (maxProPQuotient 2 AbsGalQ2)` strengthening), T-10 (rank-3
`q = 2` classification; use `demushkinRank_eq_of_card`), T-11 (the orientation character pairs
against `trivialCupPairing`).
-/

namespace GQ2

open ContCoh

/-! ## The cup form and the definition -/

section Defs

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

/-- The cup-product form `H¹(G,𝔽_p) × H¹(G,𝔽_p) → H²(G,𝔽_p)` relative to the multiplication
pairing on `ZMod p`, available once the coefficient action is trivial.  By proof irrelevance
the value does not depend on the proof `htriv`. -/
noncomputable def trivialCupPairing (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    H1 G (ZMod p) →+ H1 G (ZMod p) →+ H2 G (ZMod p) :=
  cup11 (AddMonoidHom.mul) (fun g m n => by rw [htriv, htriv, htriv])

/-- **Demushkin pro-`p` group** (Serre GC I §4.5, NSW Def. 3.9.9), with the dimension clauses
in `Nat.card` form (see module docstring).  The ambient action on `ZMod p` is constrained to
be trivial by the field `smul_trivial`. -/
structure IsDemushkin : Prop where
  /-- The coefficient action is the trivial one (the literature's `𝔽_p`). -/
  smul_trivial : ∀ (g : G) (m : ZMod p), g • m = m
  /-- `G` is pro-`p` (T-05's `IsProP`). -/
  isProP : IsProP p G
  /-- Clause 1: `dim H¹ < ∞`. -/
  finiteH1 : Finite (H1 G (ZMod p))
  /-- Clause 2: `dim H² = 1`, i.e. `#H² = p`. -/
  cardH2 : Nat.card (H2 G (ZMod p)) = p
  /-- Clause 3, left: every non-zero `H¹`-class cups non-trivially with something. -/
  nondegen_left : ∀ x : H1 G (ZMod p), x ≠ 0 →
      ∃ y, trivialCupPairing p G smul_trivial x y ≠ 0
  /-- Clause 3, right: the symmetric clause (graded-commutativity is not formalized). -/
  nondegen_right : ∀ y : H1 G (ZMod p), y ≠ 0 →
      ∃ x, trivialCupPairing p G smul_trivial x y ≠ 0

/-- **The rank of a Demushkin group**: `n = dim_{𝔽_p} H¹(G,𝔽_p)`, recovered from the
cardinality (see `IsDemushkin.card_H1_eq_pow`).  Junk value when `G` is not Demushkin. -/
noncomputable def demushkinRank : ℕ := padicValNat p (Nat.card (H1 G (ZMod p)))

end Defs

/-! ## Basic API -/

section Api

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod p)] [ContinuousSMul G (ZMod p)]

/-- The left non-degeneracy clause, consumable with *any* proof of action-triviality (the
pairing does not depend on the proof). -/
theorem IsDemushkin.nondegen_left' (hD : IsDemushkin p G)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) (x : H1 G (ZMod p)) (hx : x ≠ 0) :
    ∃ y, trivialCupPairing p G htriv x y ≠ 0 :=
  hD.nondegen_left x hx

/-- Right-slot variant of `IsDemushkin.nondegen_left'`. -/
theorem IsDemushkin.nondegen_right' (hD : IsDemushkin p G)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) (y : H1 G (ZMod p)) (hy : y ≠ 0) :
    ∃ x, trivialCupPairing p G htriv x y ≠ 0 :=
  hD.nondegen_right y hy

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod p)] in
/-- `H¹(G, 𝔽_p)` is `p`-torsion (the coefficients are). -/
theorem nsmul_H1_eq_zero (x : H1 G (ZMod p)) : p • x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H φ =>
    have hφ : p • φ = 0 := by
      apply Subtype.ext
      show p • (φ : G → ZMod p) = 0
      funext g
      show p • (φ.1 g) = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    calc p • (H1mk G (ZMod p) φ) = H1mk G (ZMod p) (p • φ) := (map_nsmul _ _ _).symm
    _ = 0 := by rw [hφ, map_zero]

/-- For a Demushkin group, `#H¹ = p ^ rank` — the `Nat.card` clause really encodes an
`𝔽_p`-dimension. -/
theorem IsDemushkin.card_H1_eq_pow [Fact p.Prime] (hD : IsDemushkin p G) :
    Nat.card (H1 G (ZMod p)) = p ^ demushkinRank p G := by
  haveI : Finite (H1 G (ZMod p)) := hD.finiteH1
  have hpg : IsPGroup p (Multiplicative (H1 G (ZMod p))) := fun x => ⟨1, by
    rw [pow_one]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one]
    exact nsmul_H1_eq_zero x.toAdd⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hpg
  have hcard : Nat.card (H1 G (ZMod p)) = p ^ n := by
    rw [← Nat.card_congr Multiplicative.toAdd, hn]
  rw [hcard, demushkinRank, hcard, padicValNat.prime_pow]

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod p)] in
/-- Computation rule for the rank: exhibit the cardinality as a `p`-power. -/
theorem demushkinRank_eq_of_card [Fact p.Prime] {n : ℕ}
    (h : Nat.card (H1 G (ZMod p)) = p ^ n) : demushkinRank p G = n := by
  rw [demushkinRank, h, padicValNat.prime_pow]

end Api

/-! ## The `q`-invariant  (ticket T-10, B3b)

Labute's second invariant: for a Demushkin group, `G^{ab} ≅ ℤ_p^{n−1} × ℤ/q` with `q = p^s`
(or `q = 0`, torsion-free), and the classification (his Théorème 8) is by `(n, q)` — plus, in
the exceptional `q = 2` case, the image of the canonical orientation character.  We take
`G^{ab}` to be the **topological** abelianization (quotient by the *closed* commutator — the
right notion for profinite `G`) and read `q` off as the number of torsion elements
(`#(ℤ/q) = q` when the torsion is finite cyclic; junk value otherwise, in particular the
sensible reading of "`q = 0`" is not encoded — documented deviation).

**B3b is deliberately *not* an axiom** (`docs/formalization-plan.md` §B3): stating the abstract
rank-3 `q = 2` classification honestly requires Labute's *canonical* character (his Prop. 6
dualizing characterization — route (i) of T-11, deferred); quantifying over an arbitrary
continuous character with the right image would be a different (and possibly false) statement.
At the field level the classification instance the paper uses **is** axiom B4
(`G_{ℚ₂}(2) ≅ D₀`), whose orientation normalization is axiom B3c (`dyadicOrientation`,
route (ii)).  This section supplies the invariant so that the classification *data*
`(rank, q) = (3, 2)` is at least expressible; `demushkinQ D₀ = 2` itself is Labute-content and
is not attempted. -/

section QInvariant

/-- The **topological abelianization** `G^{ab} = G ⧸ closure ⁅G,G⁆` (for profinite `G` this is
the profinite abelianization; cf. `AbsGalQ2ab` in `GQ2/Reciprocity.lean`). -/
def topAbelianization (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Type _ :=
  G ⧸ (commutator G).topologicalClosure

noncomputable instance (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Group (topAbelianization G) :=
  inferInstanceAs (Group (G ⧸ (commutator G).topologicalClosure))

/-- **The `q`-invariant** (Labute): the number of torsion elements of the topological
abelianization — `= q` when `G^{ab} ≅ ℤ_p^{n−1} × ℤ/q` with `q ≠ 0`.  Junk value otherwise
(see the section docstring). -/
noncomputable def demushkinQ (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : ℕ :=
  Nat.card {x : topAbelianization G // IsOfFinOrder x}

end QInvariant

/-! ## Positive stress test: `ℤ/2` is Demushkin of rank 1

`ℤ/2` (as `DihedralGroup 1`, discrete) is the unique finite Demushkin group.  We compute
`H¹ ≃+ ZMod 2` (evaluation at the generator `σ`), `H² ≃+ ZMod 2` (the functional
`f ↦ f(1,1) + f(σ,σ)`, which kills coboundaries), and the cup square of the generator —
the class of `(g,h) ↦ c₀(g)·c₀(h)`, the extension class of `ℤ/4` — evaluates to `1 ≠ 0`. -/

section CyclicTwo

/-- The trivial action of `ℤ/2 = DihedralGroup 1` on `𝔽₂`.  Safe to register globally:
`Aut(ℤ/2) = 1`, so *every* distributive action on `ZMod 2` is trivial (same convention as
`GQ2/Kummer.lean`). -/
instance : DistribMulAction (DihedralGroup 1) (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

local instance instTopologicalSpaceD1 : TopologicalSpace (DihedralGroup 1) := ⊥
local instance instDiscreteTopologyD1 : DiscreteTopology (DihedralGroup 1) := ⟨rfl⟩

local instance instContinuousSMulD1 : ContinuousSMul (DihedralGroup 1) (ZMod 2) :=
  ⟨continuous_of_discreteTopology⟩

/-- The generator of `ℤ/2`. -/
private abbrev σ : DihedralGroup 1 := DihedralGroup.sr 0

private lemma htrivC2 : ∀ (g : DihedralGroup 1) (m : ZMod 2), g • m = m :=
  fun _ _ => rfl

private lemma cases_c2 : ∀ g : DihedralGroup 1, g = 1 ∨ g = σ := by decide

/-- The generating 1-cocycle `c₀` (the nontrivial character `ℤ/2 → 𝔽₂`). -/
def cCyclicTwo : Z1 (DihedralGroup 1) (ZMod 2) :=
  ⟨fun g => if g = 1 then 0 else 1, by
    refine mem_Z1_iff.mpr ⟨continuous_of_discreteTopology, ?_⟩
    intro g h
    show (if g * h = 1 then (0 : ZMod 2) else 1)
        = (if g = 1 then 0 else 1) + g • (if h = 1 then (0 : ZMod 2) else 1)
    revert g h
    decide⟩

/-- Evaluation at the generator: `Z¹(ℤ/2, 𝔽₂) ≃+ 𝔽₂` (1-cocycles are homs, determined by the
value at `σ`). -/
noncomputable def z1CyclicTwoEquiv : Z1 (DihedralGroup 1) (ZMod 2) ≃+ ZMod 2 where
  toFun φ := φ.1 σ
  invFun t := ⟨fun g => (if g = 1 then 0 else 1) * t, by
    refine mem_Z1_iff.mpr ⟨continuous_of_discreteTopology, ?_⟩
    intro g h
    show (if g * h = 1 then (0 : ZMod 2) else 1) * t
        = (if g = 1 then (0 : ZMod 2) else 1) * t
          + g • ((if h = 1 then (0 : ZMod 2) else 1) * t)
    revert g h t
    decide⟩
  left_inv φ := by
    apply Subtype.ext
    funext g
    rcases cases_c2 g with rfl | rfl
    · show (if (1 : DihedralGroup 1) = 1 then (0 : ZMod 2) else 1) * φ.1 σ = φ.1 1
      rw [if_pos rfl, zero_mul, Z1_apply_one]
    · show (if σ = 1 then (0 : ZMod 2) else 1) * φ.1 σ = φ.1 σ
      rw [if_neg (by decide), one_mul]
  right_inv t := by
    show (if σ = 1 then (0 : ZMod 2) else 1) * t = t
    rw [if_neg (by decide), one_mul]
  map_add' φ ψ := rfl

/-- `H¹(ℤ/2, 𝔽₂) ≃+ 𝔽₂` (the plan's "`H¹ ≃` continuous homs" check, in the wrapper-free
T-02 form). -/
noncomputable def h1CyclicTwoEquiv : H1 (DihedralGroup 1) (ZMod 2) ≃+ ZMod 2 :=
  (H1equivZ1OfTrivial htrivC2).trans z1CyclicTwoEquiv

theorem card_H1_cyclicTwo : Nat.card (H1 (DihedralGroup 1) (ZMod 2)) = 2 := by
  rw [Nat.card_congr h1CyclicTwoEquiv.toEquiv, Nat.card_zmod]

/-- The evaluation functional `f ↦ f(1,1) + f(σ,σ)` on 2-cocycles. -/
def z2CyclicTwoEval : Z2 (DihedralGroup 1) (ZMod 2) →+ ZMod 2 where
  toFun φ := φ.1 (1, 1) + φ.1 (σ, σ)
  map_zero' := by simp
  map_add' φ ψ := by
    show (φ.1 (1, 1) + ψ.1 (1, 1)) + (φ.1 (σ, σ) + ψ.1 (σ, σ))
        = (φ.1 (1, 1) + φ.1 (σ, σ)) + (ψ.1 (1, 1) + ψ.1 (σ, σ))
    abel

/-- The value constraints of the cocycle identity on `ℤ/2`: `f(1,σ) = f(1,1)` and
`f(σ,1) = f(1,σ)`. -/
private lemma z2_value_relations (φ : Z2 (DihedralGroup 1) (ZMod 2)) :
    φ.1 (1, σ) = φ.1 (1, 1) ∧ φ.1 (σ, 1) = φ.1 (1, σ) := by
  have hc := (mem_Z2_iff.mp φ.2).2
  constructor
  · have h := hc 1 1 σ
    rw [htrivC2, one_mul, one_mul] at h
    -- h : φ.1 (1, σ) + φ.1 (1, σ) = φ.1 (1, σ) + φ.1 (1, 1)
    exact add_left_cancel h
  · have h := hc σ 1 σ
    rw [htrivC2, one_mul, mul_one] at h
    -- h : φ.1 (1, σ) + φ.1 (σ, σ) = φ.1 (σ, σ) + φ.1 (σ, 1)
    rw [add_comm (φ.1 (σ, σ))] at h
    exact (add_right_cancel h).symm

/-- The functional kills coboundaries (a coboundary is constant on the four points, and
`a + a = 0` in `𝔽₂`). -/
private lemma z2CyclicTwoEval_vanishes_on_B2 :
    (B2 (DihedralGroup 1) (ZMod 2)).addSubgroupOf
      (Z2 (DihedralGroup 1) (ZMod 2)) ≤ z2CyclicTwoEval.ker := by
  intro φ hφ
  rw [AddSubgroup.mem_addSubgroupOf] at hφ
  obtain ⟨ψ, hψc, hψ⟩ := hφ
  rw [AddMonoidHom.mem_ker]
  have h11 : φ.1 (1, 1) = (1 : DihedralGroup 1) • ψ 1 - ψ (1 * 1) + ψ 1 := by
    rw [← hψ]; rfl
  have hσσ : φ.1 (σ, σ) = σ • ψ σ - ψ (σ * σ) + ψ σ := by
    rw [← hψ]; rfl
  show φ.1 (1, 1) + φ.1 (σ, σ) = 0
  rw [h11, hσσ, htrivC2, htrivC2, one_mul, (by decide : σ * σ = (1 : DihedralGroup 1)),
    sub_self, zero_add, sub_add_eq_add_sub, CharTwo.add_self_eq_zero, zero_sub, CharTwo.neg_eq,
    CharTwo.add_self_eq_zero]

/-- The induced functional on `H²`. -/
noncomputable def h2CyclicTwoEval : H2 (DihedralGroup 1) (ZMod 2) →+ ZMod 2 :=
  QuotientAddGroup.lift _ z2CyclicTwoEval z2CyclicTwoEval_vanishes_on_B2

/-- The 4-point product cocycle `w(g,h) = c₀(g)·c₀(h)` — the generator of `H²` (the extension
class of `ℤ/4`, and the cup square of the generator of `H¹`). -/
def wCyclicTwo : Z2 (DihedralGroup 1) (ZMod 2) :=
  ⟨fun q => (if q.1 = 1 then 0 else 1) * (if q.2 = 1 then 0 else 1), by
    refine mem_Z2_iff.mpr ⟨continuous_of_discreteTopology, ?_⟩
    intro g h k
    revert g h k
    decide⟩

private lemma h2eval_w :
    h2CyclicTwoEval (H2mk (DihedralGroup 1) (ZMod 2) wCyclicTwo) = 1 := by decide

/-- **Injectivity of the `H²`-functional**: a cocycle with `f(1,1) + f(σ,σ) = 0` is constant
on the four points, hence the coboundary of a constant. -/
private lemma h2CyclicTwoEval_injective : Function.Injective h2CyclicTwoEval := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H φ =>
    have hev : φ.1 (1, 1) + φ.1 (σ, σ) = 0 := hx
    obtain ⟨h1σ, hσ1⟩ := z2_value_relations φ
    have hσσ : φ.1 (σ, σ) = φ.1 (1, 1) := by
      have hneg := neg_eq_of_add_eq_zero_right hev
      rw [← hneg, CharTwo.neg_eq]
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    rw [AddSubgroup.mem_addSubgroupOf]
    refine AddSubgroup.mem_map.mpr ⟨fun _ => φ.1 (1, 1), continuous_const, ?_⟩
    funext q
    have hd : dOne (DihedralGroup 1) (ZMod 2) (fun _ => φ.1 (1, 1)) q
        = q.1 • φ.1 (1, 1) - φ.1 (1, 1) + φ.1 (1, 1) := rfl
    have hval : dOne (DihedralGroup 1) (ZMod 2) (fun _ => φ.1 (1, 1)) q = φ.1 (1, 1) := by
      rw [hd, htrivC2, sub_self, zero_add]
    have hcases : ∀ q : DihedralGroup 1 × DihedralGroup 1,
        q = (1, 1) ∨ q = (1, σ) ∨ q = (σ, 1) ∨ q = (σ, σ) := by decide
    rcases hcases q with rfl | rfl | rfl | rfl
    · exact hval
    · exact hval.trans h1σ.symm
    · exact hval.trans (hσ1.trans h1σ).symm
    · exact hval.trans hσσ.symm

private lemma h2CyclicTwoEval_surjective : Function.Surjective h2CyclicTwoEval := by
  intro t
  rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
  · exact ⟨0, map_zero _⟩
  · exact ⟨H2mk _ _ wCyclicTwo, h2eval_w⟩

/-- `H²(ℤ/2, 𝔽₂) ≃+ 𝔽₂`. -/
noncomputable def h2CyclicTwoEquiv : H2 (DihedralGroup 1) (ZMod 2) ≃+ ZMod 2 :=
  AddEquiv.ofBijective h2CyclicTwoEval
    ⟨h2CyclicTwoEval_injective, h2CyclicTwoEval_surjective⟩

theorem card_H2_cyclicTwo : Nat.card (H2 (DihedralGroup 1) (ZMod 2)) = 2 := by
  rw [Nat.card_congr h2CyclicTwoEquiv.toEquiv, Nat.card_zmod]

/-- **The generator's cup square is the product cocycle** `w(g,h) = c₀(g)·c₀(h)`
(definitional: `cup11Fun` with the multiplication pairing and the `rfl`-trivial action
literally *is* `w`). -/
private lemma cup_generator :
    trivialCupPairing 2 (DihedralGroup 1) htrivC2
        (H1mk _ _ cCyclicTwo) (H1mk _ _ cCyclicTwo)
      = H2mk _ _ wCyclicTwo := rfl

private lemma cup_generator_ne_zero :
    trivialCupPairing 2 (DihedralGroup 1) htrivC2
        (H1mk _ _ cCyclicTwo) (H1mk _ _ cCyclicTwo) ≠ 0 := by
  rw [cup_generator]
  intro h0
  have h1 := congrArg h2CyclicTwoEval h0
  rw [h2eval_w, map_zero] at h1
  exact absurd h1 (by decide)

/-- The unique non-zero class of `H¹(ℤ/2, 𝔽₂)` is the class of `c₀`. -/
private lemma eq_c0_of_ne_zero (x : H1 (DihedralGroup 1) (ZMod 2)) (hx : x ≠ 0) :
    x = H1mk _ _ cCyclicTwo := by
  induction x using QuotientAddGroup.induction_on with
  | H φ =>
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) (φ.1 σ) with h | h
    · exfalso
      apply hx
      have hzero : φ = 0 := by
        apply Subtype.ext
        funext g
        rcases cases_c2 g with rfl | rfl
        · show φ.1 1 = 0
          exact Z1_apply_one φ
        · exact h
      rw [hzero]
      exact map_zero (H1mk _ _)
    · have hc0 : φ = cCyclicTwo := by
        apply Subtype.ext
        funext g
        rcases cases_c2 g with rfl | rfl
        · show φ.1 1 = if (1 : DihedralGroup 1) = 1 then 0 else 1
          rw [Z1_apply_one, if_pos rfl]
        · show φ.1 σ = if σ = 1 then 0 else 1
          rw [h, if_neg (by decide)]
      rw [hc0]
      rfl

/-- **`ℤ/2` is a Demushkin group** — the unique finite one (Serre GC I §4.5). -/
theorem isDemushkin_cyclicTwo : IsDemushkin 2 (DihedralGroup 1) where
  smul_trivial := htrivC2
  isProP := isProP_of_isPGroup (IsPGroup.of_card (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide))
  finiteH1 := Finite.of_equiv (ZMod 2) h1CyclicTwoEquiv.symm.toEquiv
  cardH2 := card_H2_cyclicTwo
  nondegen_left x hx := ⟨H1mk _ _ cCyclicTwo, by
    rw [eq_c0_of_ne_zero x hx]; exact cup_generator_ne_zero⟩
  nondegen_right y hy := ⟨H1mk _ _ cCyclicTwo, by
    rw [eq_c0_of_ne_zero y hy]; exact cup_generator_ne_zero⟩

/-- `ℤ/2` has Demushkin rank 1. -/
theorem demushkinRank_cyclicTwo : demushkinRank 2 (DihedralGroup 1) = 1 :=
  demushkinRank_eq_of_card (by rw [card_H1_cyclicTwo, pow_one])

/-- **`ℤ/2` has `q`-invariant 2** (T-10 stress): it is abelian and finite, so
`G^{ab} = G = ℤ/2` and every element is torsion — matching Labute's `q(⟨x | x²⟩) = 2`. -/
theorem demushkinQ_cyclicTwo : demushkinQ (DihedralGroup 1) = 2 := by
  -- the closed commutator is trivial (the group is abelian and discrete)
  have hcomm : (commutator (DihedralGroup 1)).topologicalClosure = ⊥ := by
    have h1 : commutator (DihedralGroup 1) = ⊥ := by
      rw [commutator_def, eq_bot_iff]
      refine Subgroup.commutator_le.mpr fun g _ h _ => ?_
      rw [Subgroup.mem_bot]
      show g * h * g⁻¹ * h⁻¹ = 1
      exact (by decide : ∀ g h : DihedralGroup 1, g * h * g⁻¹ * h⁻¹ = 1) g h
    rw [h1]
    exact Subgroup.ext fun x => by
      rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe,
        IsClosed.closure_eq (isClosed_discrete _)]
      rfl
  -- every element of the (finite) abelianization is torsion
  haveI : Finite (topAbelianization (DihedralGroup 1)) :=
    inferInstanceAs (Finite (DihedralGroup 1 ⧸ _))
  have htor : ∀ x : topAbelianization (DihedralGroup 1), IsOfFinOrder x :=
    fun x => isOfFinOrder_of_finite x
  rw [demushkinQ, Nat.card_congr (Equiv.subtypeUnivEquiv htor)]
  -- `G^{ab} ≃ G ⧸ ⊥ ≃ G`, of cardinality 2
  have e1 : topAbelianization (DihedralGroup 1) ≃* DihedralGroup 1 ⧸ (⊥ : Subgroup _) :=
    QuotientGroup.quotientMulEquivOfEq hcomm
  have e2 : DihedralGroup 1 ⧸ (⊥ : Subgroup (DihedralGroup 1)) ≃* DihedralGroup 1 :=
    QuotientGroup.quotientBot
  rw [Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, Nat.card_eq_fintype_card]
  decide

end CyclicTwo

/-! ## Negative stress test: the trivial group is not Demushkin

`PUnit` is the free pro-`p` group of rank 0: `H²(1, 𝔽_p) = 0`, so clause 2 fails.  (Free
pro-`p` groups all have `H² = 0` — Serre GC I §4.2 — and are the basic non-examples.) -/

section PUnitNot

variable (p : ℕ)

/-- The (unique) action of the trivial group.  Global for the same reason as the `ℤ/2`
instance: `one_smul` forces any action of `PUnit` to be trivial. -/
instance : DistribMulAction PUnit (ZMod p) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul PUnit (ZMod p) := ⟨continuous_of_discreteTopology⟩

private lemma htrivPUnit : ∀ (g : PUnit) (m : ZMod p), g • m = m := fun _ _ => rfl

/-- Over the trivial group every 2-cocycle is the coboundary of a constant. -/
private lemma b2_eq_top_punit :
    (B2 PUnit (ZMod p)).addSubgroupOf (Z2 PUnit (ZMod p)) = ⊤ := by
  rw [eq_top_iff]
  rintro φ -
  rw [AddSubgroup.mem_addSubgroupOf]
  refine AddSubgroup.mem_map.mpr ⟨fun _ => φ.1 (1, 1), continuous_const, ?_⟩
  funext q
  have hd : dOne PUnit (ZMod p) (fun _ => φ.1 (1, 1)) q
      = q.1 • φ.1 (1, 1) - φ.1 (1, 1) + φ.1 (1, 1) := rfl
  rw [hd, htrivPUnit, sub_self, zero_add]
  -- the residual goal `φ.1 (1,1) = φ.1 q` is closed by `rw`'s `rfl` check: `PUnit` eta makes
  -- `q` definitionally `(1,1)`

theorem subsingleton_H2_punit : Subsingleton (H2 PUnit (ZMod p)) := by
  show Subsingleton
    (Z2 PUnit (ZMod p) ⧸ (B2 PUnit (ZMod p)).addSubgroupOf (Z2 PUnit (ZMod p)))
  rw [b2_eq_top_punit]
  exact QuotientAddGroup.subsingleton_quotient_top

/-- **The trivial group is not Demushkin**: `H² = 0` (it is free pro-`p` of rank 0),
violating `#H² = p`. -/
theorem not_isDemushkin_punit [Fact p.Prime] : ¬ IsDemushkin p PUnit := by
  intro hD
  haveI := subsingleton_H2_punit p
  have h1 : Nat.card (H2 PUnit (ZMod p)) = 1 := Nat.card_of_subsingleton 0
  have hp1 : p = 1 := by rw [← hD.cardH2, h1]
  exact (Fact.out : p.Prime).ne_one hp1

end PUnitNot

end GQ2
