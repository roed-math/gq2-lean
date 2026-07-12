import GQ2.Cohomology

/-!
# Cup products in continuous cohomology (degrees ≤ 2)  (ticket T-04, unlock U2)

Cup products relative to a `G`-equivariant biadditive pairing `μ : M →+ N →+ P`, in the three
shapes needed by the literature axioms (B3 Demushkin, B6 local Tate duality):

* `cup11 : H¹(G,M) →+ H¹(G,N) →+ H²(G,P)` — the `(1,1)` cup, `(a ∪ b)(g,h) = μ (a g) (g • b h)`;
* `cup02 : H⁰(G,M) →+ H²(G,N) →+ H²(G,P)` — `(a ∪ b)(g,h) = μ a (b (g,h))`;
* `cup20 : H²(G,M) →+ H⁰(G,N) →+ H²(G,P)` — `(a ∪ b)(g,h) = μ (a (g,h)) ((g·h) • b)`.

**Design.** Coefficient modules `M, N` are taken **discrete** (the finite discrete setting of the
axioms), which makes every cup cochain continuous with no continuity hypothesis on `μ`.  The maps
are built by descending explicit cochain formulas through cohomology; the bundling into
`→+ →+` makes them **bilinear by construction** (acceptance criterion), and `∪ 0 = 0` / `0 ∪ = 0`
are then `map_zero`.  Coefficient naturality is `cup11_mapCoeff_right` etc.

The `(1,1)` cup is the one B3 needs (nondegeneracy of `H¹ × H¹ → H²`); `(0,2)`/`(2,0)` feed B6's
`H^i × H^{2-i} → H²` pairing.  Everything is proved from the explicit `mem_Z1_iff`/`mem_Z2_iff`
cocycle identities of `GQ2/Cohomology.lean`; `#print axioms` stays the standard three.
-/

namespace GQ2

namespace ContCoh

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DiscreteTopology N] [DistribMulAction G N] [ContinuousSMul G N]
variable {P : Type*} [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
  [DistribMulAction G P] [ContinuousSMul G P]
variable (μ : M →+ N →+ P) (hμ : ∀ (g : G) (m : M) (n : N), μ (g • m) (g • n) = g • μ m n)

/-! ## The `(1,1)` cup product -/

/-- The `(1,1)`-cup cochain `(a ∪ b)(g,h) = μ (a g) (g • b h)`. -/
def cup11Fun (a : G → M) (b : G → N) : G × G → P := fun p => μ (a p.1) (p.1 • b p.2)

lemma cup11Fun_add_left (a a' : G → M) (b : G → N) :
    cup11Fun μ (a + a') b = cup11Fun μ a b + cup11Fun μ a' b := by
  funext p; simp only [cup11Fun, Pi.add_apply, map_add, AddMonoidHom.add_apply]

lemma cup11Fun_add_right (a : G → M) (b b' : G → N) :
    cup11Fun μ a (b + b') = cup11Fun μ a b + cup11Fun μ a b' := by
  funext p; simp only [cup11Fun, Pi.add_apply, smul_add, map_add]

/-- A product-of-values map into `P` out of two continuous maps into the discrete modules
`M, N` is continuous (the pairing is automatically continuous since `M × N` is discrete). -/
lemma continuous_pairing {α : Type*} [TopologicalSpace α] {u : α → M} {v : α → N}
    (hu : Continuous u) (hv : Continuous v) : Continuous (fun x => μ (u x) (v x)) :=
  (continuous_of_discreteTopology (f := fun q : M × N => μ q.1 q.2)).comp (hu.prodMk hv)

lemma continuous_cup11Fun {a : G → M} {b : G → N} (ha : Continuous a) (hb : Continuous b) :
    Continuous (cup11Fun μ a b) :=
  continuous_pairing μ (ha.comp continuous_fst)
    (Continuous.smul continuous_fst (hb.comp continuous_snd))

include hμ in
/-- **Cup of cocycles is a cocycle**: the key 2-cocycle identity for `(1,1)`. -/
lemma cup11_mem_Z2 (a : Z1 G M) (b : Z1 G N) : cup11Fun μ a.1 b.1 ∈ Z2 G P := by
  refine mem_Z2_iff.mpr
    ⟨continuous_cup11Fun μ (mem_Z1_iff.mp a.2).1 (mem_Z1_iff.mp b.2).1, fun g h k => ?_⟩
  have hca := (mem_Z1_iff.mp a.2).2 g h
  have hcb := (mem_Z1_iff.mp b.2).2 h k
  show g • cup11Fun μ a.1 b.1 (h, k) + cup11Fun μ a.1 b.1 (g, h * k)
      = cup11Fun μ a.1 b.1 (g * h, k) + cup11Fun μ a.1 b.1 (g, h)
  simp only [cup11Fun]
  rw [hca, hcb]
  simp only [smul_add, map_add, AddMonoidHom.add_apply, ← hμ, ← mul_smul]
  abel

include hμ in
/-- The `(1,1)` cup, bundled biadditively at the cocycle level and post-composed with the class
map `Z² → H²`. -/
def cup11ZH : Z1 G M →+ Z1 G N →+ H2 G P :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun b => H2mk G P ⟨cup11Fun μ a.1 b.1, cup11_mem_Z2 μ hμ a b⟩)
      (fun b b' => by
        rw [← map_add]; congr 1
        exact Subtype.ext (cup11Fun_add_right μ a.1 b.1 b'.1)))
    (fun a a' => by
      ext b
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← map_add]; congr 1
      exact Subtype.ext (cup11Fun_add_left μ a.1 a'.1 b.1))

include hμ in
/-- **Descent, right variable**: if the `N`-cocycle is a coboundary, the cup is a coboundary
(uses that the `M`-argument is a cocycle). -/
lemma cup11_bcobound (a : Z1 G M) {c : G → N} (hc : c ∈ B1 G N) :
    cup11Fun μ a.1 c ∈ B2 G P := by
  obtain ⟨n, hn⟩ := hc
  have hac := (mem_Z1_iff.mp a.2).2
  refine AddSubgroup.mem_map.mpr ⟨-(fun g => μ (a.1 g) (g • n)), ?_, ?_⟩
  · exact (continuous_pairing μ (mem_Z1_iff.mp a.2).1 (continuous_id.smul continuous_const)).neg
  · funext ⟨g, h⟩
    have hch : c h = h • n - n := by rw [← hn]; rfl
    show g • (-(fun g => μ (a.1 g) (g • n))) h - (-(fun g => μ (a.1 g) (g • n))) (g * h)
        + (-(fun g => μ (a.1 g) (g • n))) g = μ (a.1 g) (g • c h)
    simp only [Pi.neg_apply, smul_neg, hch, hac g h]
    simp only [smul_sub, map_add, map_sub, AddMonoidHom.add_apply, ← hμ, ← mul_smul]
    abel

include hμ in
/-- **Descent, left variable**: if the `M`-cocycle is a coboundary, the cup is a coboundary
(uses that the `N`-argument is a cocycle). -/
lemma cup11_acobound {c : G → M} (hc : c ∈ B1 G M) (b : Z1 G N) :
    cup11Fun μ c b.1 ∈ B2 G P := by
  obtain ⟨m, hm⟩ := hc
  have hbc := (mem_Z1_iff.mp b.2).2
  refine AddSubgroup.mem_map.mpr ⟨(fun g => μ m (b.1 g)), ?_, ?_⟩
  · exact continuous_pairing μ continuous_const (mem_Z1_iff.mp b.2).1
  · funext ⟨g, h⟩
    have hcg : c g = g • m - m := by rw [← hm]; rfl
    show g • (fun g => μ m (b.1 g)) h - (fun g => μ m (b.1 g)) (g * h) + (fun g => μ m (b.1 g)) g
        = μ (c g) (g • b.1 h)
    simp only [hcg, hbc g h]
    simp only [map_add, map_sub, AddMonoidHom.sub_apply, ← hμ]
    abel

include hμ in
/-- **The `(1,1)` cup product** `H¹(G,M) →+ H¹(G,N) →+ H²(G,P)`, bilinear by construction. -/
noncomputable def cup11 : H1 G M →+ H1 G N →+ H2 G P := by
  refine QuotientAddGroup.lift _
    (AddMonoidHom.mk' (fun a => QuotientAddGroup.lift _ (cup11ZH μ hμ a) ?_) ?_) ?_
  · -- for fixed cocycle a, the map kills N-coboundaries
    rintro b hb
    rw [AddSubgroup.mem_addSubgroupOf] at hb
    rw [AddMonoidHom.mem_ker]
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      ((AddSubgroup.mem_addSubgroupOf).mpr (cup11_bcobound μ hμ a hb))
  · -- additive in a
    intro a a'
    ext bq
    induction bq using QuotientAddGroup.induction_on with
    | H b =>
      simp only [QuotientAddGroup.lift_mk']
      rw [map_add]
      rfl
  · -- kills M-coboundaries
    rintro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    rw [AddMonoidHom.mem_ker]
    ext bq
    induction bq using QuotientAddGroup.induction_on with
    | H b =>
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply]
      exact (QuotientAddGroup.eq_zero_iff _).mpr
        ((AddSubgroup.mem_addSubgroupOf).mpr (cup11_acobound μ hμ ha b))

include hμ in
@[simp] lemma cup11_mk_mk (a : Z1 G M) (b : Z1 G N) :
    cup11 μ hμ (H1mk G M a) (H1mk G N b) = H2mk G P ⟨cup11Fun μ a.1 b.1, cup11_mem_Z2 μ hμ a b⟩ :=
  rfl


@[simp] lemma cup11_zero_left (y : H1 G N) : cup11 μ hμ 0 y = 0 := by
  rw [map_zero]; rfl


/-! ## The `(0,2)` cup product -/

/-- The `(0,2)`-cup cochain `(a ∪ b)(g,h) = μ a (b (g,h))`. -/
def cup02Fun (m : M) (b : G × G → N) : G × G → P := fun p => μ m (b p)

lemma cup02Fun_add_left (m m' : M) (b : G × G → N) :
    cup02Fun μ (m + m') b = cup02Fun μ m b + cup02Fun μ m' b := by
  funext p; simp only [cup02Fun, map_add, AddMonoidHom.add_apply, Pi.add_apply]

lemma cup02Fun_add_right (m : M) (b b' : G × G → N) :
    cup02Fun μ m (b + b') = cup02Fun μ m b + cup02Fun μ m b' := by
  funext p; simp only [cup02Fun, Pi.add_apply, map_add]

include hμ in
/-- Cup of an invariant with a 2-cocycle is a 2-cocycle. -/
lemma cup02_mem_Z2 (m : ↥(H0 G M)) (b : Z2 G N) : cup02Fun μ m.1 b.1 ∈ Z2 G P := by
  refine mem_Z2_iff.mpr
    ⟨continuous_pairing μ continuous_const (mem_Z2_iff.mp b.2).1, fun g h k => ?_⟩
  have hb := (mem_Z2_iff.mp b.2).2 g h k
  show g • μ m.1 (b.1 (h, k)) + μ m.1 (b.1 (g, h * k))
      = μ m.1 (b.1 (g * h, k)) + μ m.1 (b.1 (g, h))
  rw [← hμ g m.1 (b.1 (h, k)), m.2 g, ← map_add, ← map_add, hb]

include hμ in
/-- Descent for `(0,2)`: cup with a coboundary is a coboundary. -/
lemma cup02_bcobound (m : ↥(H0 G M)) {c : G × G → N} (hc : c ∈ B2 G N) :
    cup02Fun μ m.1 c ∈ B2 G P := by
  obtain ⟨ψ, hψc, hψ⟩ := hc
  refine AddSubgroup.mem_map.mpr ⟨fun g => μ m.1 (ψ g), continuous_pairing μ continuous_const hψc, ?_⟩
  funext ⟨g, h⟩
  have hc' : c (g, h) = g • ψ h - ψ (g * h) + ψ g := by rw [← hψ]; rfl
  show g • μ m.1 (ψ h) - μ m.1 (ψ (g * h)) + μ m.1 (ψ g) = μ m.1 (c (g, h))
  rw [hc', ← hμ g m.1 (ψ h), m.2 g, map_add, map_sub]

include hμ in
/-- The `(0,2)` cup, bundled biadditively at the cocycle level (`Z²`-slot first, so that it can be
descended with a single `QuotientAddGroup.lift`; the final order is fixed by `flip`). -/
def cup02FlipZH : Z2 G N →+ ↥(H0 G M) →+ H2 G P :=
  AddMonoidHom.mk'
    (fun b => AddMonoidHom.mk'
      (fun m => H2mk G P ⟨cup02Fun μ m.1 b.1, cup02_mem_Z2 μ hμ m b⟩)
      (fun m m' => by
        rw [← map_add]; congr 1
        exact Subtype.ext (cup02Fun_add_left μ m.1 m'.1 b.1)))
    (fun b b' => by
      ext m
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← map_add]; congr 1
      exact Subtype.ext (cup02Fun_add_right μ m.1 b.1 b'.1))

include hμ in
/-- **The `(0,2)` cup product** `H⁰(G,M) →+ H²(G,N) →+ H²(G,P)`. -/
noncomputable def cup02 : ↥(H0 G M) →+ H2 G N →+ H2 G P :=
  (QuotientAddGroup.lift _ (cup02FlipZH μ hμ) (by
    rintro b hb
    rw [AddSubgroup.mem_addSubgroupOf] at hb
    rw [AddMonoidHom.mem_ker]
    ext m
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      ((AddSubgroup.mem_addSubgroupOf).mpr (cup02_bcobound μ hμ m hb)))).flip

/-! ## The `(2,0)` cup product -/

/-- The `(2,0)`-cup cochain `(a ∪ b)(g,h) = μ (a (g,h)) ((g·h) • b)`. -/
def cup20Fun (a : G × G → M) (n : N) : G × G → P := fun p => μ (a p) ((p.1 * p.2) • n)

lemma cup20Fun_add_left (a a' : G × G → M) (n : N) :
    cup20Fun μ (a + a') n = cup20Fun μ a n + cup20Fun μ a' n := by
  funext p; simp only [cup20Fun, Pi.add_apply, map_add, AddMonoidHom.add_apply]

lemma cup20Fun_add_right (a : G × G → M) (n n' : N) :
    cup20Fun μ a (n + n') = cup20Fun μ a n + cup20Fun μ a n' := by
  funext p; simp only [cup20Fun, Pi.add_apply, smul_add, map_add]

lemma continuous_cup20Fun {a : G × G → M} (ha : Continuous a) (n : N) :
    Continuous (cup20Fun μ a n) :=
  continuous_pairing μ ha
    (Continuous.smul (continuous_fst.mul continuous_snd) continuous_const)

include hμ in
/-- Cup of a 2-cocycle with an invariant is a 2-cocycle. -/
lemma cup20_mem_Z2 (a : Z2 G M) (n : ↥(H0 G N)) : cup20Fun μ a.1 n.1 ∈ Z2 G P := by
  have hn : ∀ x : G, x • n.1 = n.1 := n.2
  refine mem_Z2_iff.mpr
    ⟨continuous_cup20Fun μ (mem_Z2_iff.mp a.2).1 n.1, fun g h k => ?_⟩
  have ha := (mem_Z2_iff.mp a.2).2 g h k
  show g • μ (a.1 (h, k)) ((h * k) • n.1) + μ (a.1 (g, h * k)) ((g * (h * k)) • n.1)
      = μ (a.1 (g * h, k)) ((g * h * k) • n.1) + μ (a.1 (g, h)) ((g * h) • n.1)
  simp only [hn]
  rw [← hμ g (a.1 (h, k)) n.1, hn, ← AddMonoidHom.add_apply, ← map_add,
    ← AddMonoidHom.add_apply, ← map_add, ha]

include hμ in
/-- Descent for `(2,0)`: cup of a coboundary with an invariant is a coboundary. -/
lemma cup20_acobound {c : G × G → M} (hc : c ∈ B2 G M) (n : ↥(H0 G N)) :
    cup20Fun μ c n.1 ∈ B2 G P := by
  have hn : ∀ x : G, x • n.1 = n.1 := n.2
  obtain ⟨ψ, hψc, hψ⟩ := hc
  refine AddSubgroup.mem_map.mpr ⟨fun g => μ (ψ g) n.1, ?_, ?_⟩
  · exact continuous_pairing μ hψc continuous_const
  · funext ⟨g, h⟩
    have hc' : c (g, h) = g • ψ h - ψ (g * h) + ψ g := by rw [← hψ]; rfl
    show g • μ (ψ h) n.1 - μ (ψ (g * h)) n.1 + μ (ψ g) n.1 = μ (c (g, h)) ((g * h) • n.1)
    rw [hc', hn, ← hμ g (ψ h) n.1, hn]
    simp only [map_add, map_sub, AddMonoidHom.add_apply, AddMonoidHom.sub_apply]

include hμ in
/-- The `(2,0)` cup, bundled biadditively at the cocycle level. -/
def cup20ZH : Z2 G M →+ ↥(H0 G N) →+ H2 G P :=
  AddMonoidHom.mk'
    (fun a => AddMonoidHom.mk'
      (fun n => H2mk G P ⟨cup20Fun μ a.1 n.1, cup20_mem_Z2 μ hμ a n⟩)
      (fun n n' => by
        rw [← map_add]; congr 1
        exact Subtype.ext (cup20Fun_add_right μ a.1 n.1 n'.1)))
    (fun a a' => by
      ext n
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [← map_add]; congr 1
      exact Subtype.ext (cup20Fun_add_left μ a.1 a'.1 n.1))

include hμ in
/-- **The `(2,0)` cup product** `H²(G,M) →+ H⁰(G,N) →+ H²(G,P)`. -/
noncomputable def cup20 : H2 G M →+ ↥(H0 G N) →+ H2 G P :=
  QuotientAddGroup.lift _ (cup20ZH μ hμ) (by
    rintro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    rw [AddMonoidHom.mem_ker]
    ext n
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      ((AddSubgroup.mem_addSubgroupOf).mpr (cup20_acobound μ hμ ha n)))

/-! ## Coefficient naturality (T-04 acceptance)

The cup product is natural in the pairing's target: post-composing `μ` with a continuous
`G`-equivariant `fP : P →+ P'` and cupping equals cupping and then applying the coefficient map
`mapCoeff2 fP`.  (Stated for the `(1,1)` cup; the same holds in the other shapes.) -/

section CoeffNat

variable {P' : Type*} [AddCommGroup P'] [TopologicalSpace P'] [IsTopologicalAddGroup P']
  [DistribMulAction G P'] [ContinuousSMul G P']
variable (fP : P →+ P') (hfPc : Continuous fP) (hfP : ∀ (g : G) (p : P), fP (g • p) = g • fP p)

/-- The pairing `μ` post-composed with a target map `fP`, as a biadditive pairing into `P'`. -/
def postPairing : M →+ N →+ P' := (AddMonoidHom.compHom fP).comp μ



end CoeffNat

end ContCoh

end GQ2
