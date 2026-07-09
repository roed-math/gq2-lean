import GQ2.IotaGammaA

/-!
# P-16d6e4aA (A-3) — `Q⁰` over `Γ_A` as a relator value in the `κ⁰`-extension

The evaluation brick of the (83)-for-`Γ_A` seam (`docs/p16d6e4aA-gammaA-gauss-design.md` §2):
the graph pullback is, on the nose, the pullback of the **base central cocycle** `κ⁰_q` on the
semidirect product `V ⋊ C` (eq. (61)/(62): `graphPullback dat ρ₀ b = κ⁰ ∘ (graph × graph)`,
where `graph γ = (b γ, ρ₀ γ)` is a homomorphism exactly because `b` is a crossed cocycle).
Hence, by A-2 (`QZero_eq_levelFactor_obs`) and the level-change naturality
(`relZPair_comap`), the base determinant form evaluates as a **relator value in the concrete
finite extension** `CentExt κ⁰`:

  `Q⁰_{Γ_A,ρ'}(c) = relZPair (graph-marking) κ⁰-cocycle |₁ + |₂`

where the graph marking is the image of the `Γ_A`-generator marking `gammaGen` under the
graph homomorphism — the four explicit pairs `(c(gᵢ), ρ'₀(gᵢ)) ∈ V ⋊ C`.  This is the A-4
interface: the two relator words evaluated at those pairs in `CentExt κ⁰` ARE the paper's
(83) quadratic in the generator values.

Contents: the semidirect group `Sd C V` (isolated carrier, no `Prod`-instance pollution);
`kappa0Cocycle` (`κ⁰` as a normalized `WordCoh2.TwoCocycle` — Lemma 6.1's associativity from
the `IsEquivariantFactorSet` clauses); `graphSdHom` (the crossed-cocycle graph hom) and its
continuity; the explicit `LevelFactor` for the graph pullback (kernel level of the graph
hom); and the assembled `QZero_eq_relZPair_kappa0`.

All std-3; no axioms, no sorries.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction WordCohBridge WordCoh2 ContCoh

/-! ## The semidirect product `V ⋊ C` as an isolated group carrier -/

section Sd

variable (C V : Type*) [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- The carrier of `V ⋊ C` — a `def` (not an `abbrev`), so the group structure below does
not leak onto raw products. -/
def Sd : Type _ := V × C

variable {C V}

/-- The `V`-component. -/
def Sd.v (p : Sd C V) : V := p.1

/-- The `C`-component. -/
def Sd.cc (p : Sd C V) : C := p.2

/-- Pairs as semidirect elements. -/
def Sd.mk (v : V) (c : C) : Sd C V := (v, c)

@[ext] theorem Sd.ext {p q : Sd C V} (h1 : p.v = q.v) (h2 : p.cc = q.cc) : p = q :=
  Prod.ext h1 h2

instance : Group (Sd C V) where
  mul p q := (p.1 + p.2 • q.1, p.2 * q.2)
  one := ((0 : V), (1 : C))
  inv p := (-(p.2⁻¹ • p.1), p.2⁻¹)
  mul_assoc p q r := by
    refine Prod.ext ?_ (mul_assoc _ _ _)
    show p.1 + p.2 • q.1 + (p.2 * q.2) • r.1 = p.1 + p.2 • (q.1 + q.2 • r.1)
    rw [smul_add, mul_smul, add_assoc]
  one_mul p := by
    refine Prod.ext ?_ (one_mul _)
    show (0 : V) + (1 : C) • p.1 = p.1
    rw [one_smul, zero_add]
  mul_one p := by
    refine Prod.ext ?_ (mul_one _)
    show p.1 + p.2 • (0 : V) = p.1
    rw [smul_zero, add_zero]
  inv_mul_cancel p := by
    refine Prod.ext ?_ (inv_mul_cancel _)
    show -(p.2⁻¹ • p.1) + p.2⁻¹ • p.1 = 0
    exact neg_add_cancel _

@[simp] theorem Sd.mul_v (p q : Sd C V) : (p * q).v = p.v + p.cc • q.v := rfl
@[simp] theorem Sd.mul_cc (p q : Sd C V) : (p * q).cc = p.cc * q.cc := rfl
@[simp] theorem Sd.one_v : (1 : Sd C V).v = 0 := rfl
@[simp] theorem Sd.one_cc : (1 : Sd C V).cc = 1 := rfl

instance [Finite C] [Finite V] : Finite (Sd C V) := inferInstanceAs (Finite (V × C))

instance [TopologicalSpace C] [TopologicalSpace V] : TopologicalSpace (Sd C V) :=
  inferInstanceAs (TopologicalSpace (V × C))

instance [TopologicalSpace C] [DiscreteTopology C] [TopologicalSpace V] [DiscreteTopology V] :
    DiscreteTopology (Sd C V) := inferInstanceAs (DiscreteTopology (V × C))

end Sd

/-! ## `κ⁰_q` as a normalized `TwoCocycle` on `V ⋊ C`  (Lemma 6.1's associativity) -/

section Kappa0Cocycle

variable {C V : Type*} [Group C] [AddCommGroup V] [DistribMulAction C V]
variable {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

include hdat in
/-- `m_c(0) = 0` (from `m_quad` at `v = w = 0` in characteristic 2). -/
theorem IsEquivariantFactorSet.m_zero (c : C) : dat.m c 0 = 0 := by
  have h := hdat.m_quad c 0 0
  simp only [add_zero, smul_zero, hdat.f_zero_left] at h
  -- `h : m_c 0 + m_c 0 + m_c 0 = 0`, i.e. `3·m_c 0 = 0`, i.e. `m_c 0 = 0` in `𝔽₂`
  have key : ∀ a : ZMod 2, a + a + a = 0 → a = 0 := by decide
  exact key _ h

/-- **The base central cocycle `κ⁰_q` as a normalized `TwoCocycle` on `V ⋊ C`** (eq. (61);
the cocycle identity is Lemma 6.1's "associativity of `E_f`", assembled from `f_cocycle`,
`m_quad`, and `m_mul`). -/
noncomputable def kappa0Cocycle : TwoCocycle (Sd C V) where
  κ p r := kappa0 dat (p.v, p.cc) (r.v, r.cc)
  norm := by
    show dat.f (0 : V) ((1 : C) • (0 : V)) + dat.m (1 : C) (0 : V) = 0
    rw [smul_zero, hdat.f_zero_left, hdat.m_one, add_zero]
  cocyc := by
    intro p r s
    show dat.f p.v (p.cc • r.v) + dat.m p.cc r.v
        + (dat.f (p * r).v ((p * r).cc • s.v) + dat.m (p * r).cc s.v)
      = dat.f p.v (p.cc • (r * s).v) + dat.m p.cc (r * s).v
        + (dat.f r.v (r.cc • s.v) + dat.m r.cc s.v)
    simp only [Sd.mul_v, Sd.mul_cc]
    -- abbreviations
    set a := p.v; set b := p.cc
    set x := r.v; set y := r.cc
    set w := s.v; set z := s.cc
    -- the three ledger identities
    have h1 := hdat.f_cocycle a (b • x) ((b * y) • w)
    have h2 := hdat.m_quad b x (y • w)
    have h3 := hdat.m_mul b y w
    have hsm : b • (x + y • w) = b • x + (b * y) • w := by rw [smul_add, mul_smul]
    have hsm2 : b • (y • w) = (b * y) • w := (mul_smul b y w).symm
    rw [hsm]
    rw [hsm2] at h2
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 + h2 + h3

@[simp] theorem kappa0Cocycle_κ (p r : Sd C V) :
    (kappa0Cocycle dat hdat).κ p r = dat.f p.v (p.cc • r.v) + dat.m p.cc r.v := rfl

end Kappa0Cocycle

/-! ## The graph homomorphism of a crossed cocycle -/

section GraphHom

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρM : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

/-- **The graph homomorphism** `γ ↦ (c(γ), ρ'₀(γ)) : Γ →* V ⋊ C` — the crossed-cocycle
condition is exactly the homomorphism law. -/
noncomputable def graphSdHom (c : VCocycle DD ρM) : Γ →* Sd DD.C0 DD.Vmod where
  toFun γ := (c.c γ, rho0 DD ρM γ)
  map_one' := by
    refine Prod.ext ?_ ?_
    · exact c.c_one
    · exact map_one (rho0 DD ρM)
  map_mul' γ δ := by
    refine Prod.ext ?_ ?_
    · exact c.crossed γ δ
    · exact map_mul (rho0 DD ρM) γ δ

@[simp] theorem graphSdHom_apply (c : VCocycle DD ρM) (γ : Γ) :
    graphSdHom c γ = (c.c γ, rho0 DD ρM γ) := rfl

/-- **The graph pullback is the `κ⁰`-pullback along the graph hom** (eq. (62), on the
nose). -/
theorem graphPullback_eq_kappa0_graph {q : DD.Vmod → ZMod 2}
    (hdat : IsEquivariantFactorSet q DD.dat) (c : VCocycle DD ρM) (p : Γ × Γ) :
    graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c p
      = (kappa0Cocycle DD.dat hdat).κ (graphSdHom c p.1) (graphSdHom c p.2) := rfl

end GraphHom

/-! ## The explicit level factorization over `Γ_A` and the assembled relator value -/

section GammaA

open WordCohBridge

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg} {DD : DescData D}
variable {ρM : ContinuousMonoidHom GA (Bg ⧸ D.M)}
variable [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
variable [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0] [Finite DD.Vmod]

/-- A crossed cocycle's underlying function is continuous into the (discrete) module: its
composition with the injective `iV ∘ ofAdd` is continuous into the discrete `Bg ⧸ T`, so
every fiber is open. -/
theorem continuous_vcocycle_c (c : VCocycle DD ρM) : Continuous c.c := by
  have hlc : IsLocallyConstant c.c := by
    intro s
    have hpre : c.c ⁻¹' s
        = (fun γ => iV DD (Multiplicative.ofAdd (c.c γ)))
          ⁻¹' ((fun v => iV DD (Multiplicative.ofAdd v)) '' s) := by
      ext γ
      simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · intro h
        exact ⟨c.c γ, h, rfl⟩
      · rintro ⟨v, hv, heq⟩
        rwa [← iV_ofAdd_inj DD heq]
    rw [hpre]
    exact IsOpen.preimage c.cont (isOpen_discrete _)
  exact hlc.continuous

/-- **The A-3 keystone**: over `Γ_A`, the base determinant form `Q⁰` of a crossed `V`-cocycle
is the **relator value in the concrete `κ⁰`-extension**: the (tame + wild) relator-`z` pair of
the `κ⁰`-cocycle on `V ⋊ C` at the marking `graph(gammaGen)` — the four explicit pairs
`(c(gᵢ), ρ'₀(gᵢ))`.  (A-2's `QZero_eq_levelFactor_obs` at the kernel level of the graph hom,
transported by `relZPair_comap`.) -/
theorem QZero_eq_relZPair_kappa0 [DistribMulAction GA (ZMod 2)] [ContinuousSMul GA (ZMod 2)]
    (htriv : ∀ (x : GA) (m : ZMod 2), x • m = m)
    {q : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q DD.dat)
    (c : VCocycle DD ρM) :
    QZero DD ρM c
      = (relZPair (gammaGen.map (graphSdHom c)) (kappa0Cocycle DD.dat hdat)).1
        + (relZPair (gammaGen.map (graphSdHom c)) (kappa0Cocycle DD.dat hdat)).2 := by
  classical
  -- the graph hom is continuous into the finite discrete `V ⋊ C`
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  have hgcont : Continuous (graphSdHom c) := by
    show Continuous fun γ => ((c.c γ, rho0 DD ρM γ) : DD.Vmod × DD.C0)
    exact (continuous_vcocycle_c c).prodMk
      ((continuous_of_discreteTopology (f := fun x : Bg ⧸ D.M => liftC0 DD x)).comp
        ρM.continuous)
  -- the composite from `F₄` and its (open, normal) kernel level
  set full : FreeProfiniteGroup (Fin 4) →* Sd DD.C0 DD.Vmod :=
    (graphSdHom c).comp (quotientMk NA).toMonoidHom with hfulldef
  have hfullcont : Continuous full := hgcont.comp (quotientMk NA).continuous
  have hkeropen : IsOpen (full.ker : Set (FreeProfiniteGroup (Fin 4))) := by
    have hs : (full.ker : Set (FreeProfiniteGroup (Fin 4))) = full ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hs]
    exact IsOpen.preimage hfullcont (isOpen_discrete _)
  set U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    ⟨⟨full.ker, hkeropen⟩, full.normal_ker⟩ with hUdef
  have hNAle : NA ≤ U.toSubgroup := by
    intro n hn
    show full n = 1
    show (graphSdHom c) (quotientMk NA n) = 1
    have h1 : quotientMk NA n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [h1, map_one]
  -- the descended level map, agreeing with the graph through `levelProj`
  set φU : (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) →* Sd DD.C0 DD.Vmod :=
    QuotientGroup.lift U.toSubgroup full (fun _ hu => hu) with hφUdef
  have hφlev : ∀ g : GA, φU (levelProj U hNAle g) = graphSdHom c g := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x => rfl
  -- the graph pullback is already `(1,1)`-normalized
  have h11 : graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c (1, 1) = 0 := by
    show DD.dat.f (c.c 1) (rho0 DD ρM 1 • c.c 1) + DD.dat.m (rho0 DD ρM 1) (c.c 1) = 0
    rw [c.c_one, smul_zero, hdat.f_zero_left, map_one, hdat.m_one, add_zero]
  have hnorm : normalizeCochain (graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c)
      = graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c := by
    funext p
    show graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c p
        - graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c (1, 1)
      = graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c p
    rw [h11, sub_zero]
  -- the explicit level factorization through the `κ⁰`-cocycle
  set F : LevelFactor (normalizeCochain (graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c)) :=
    ⟨U, hNAle, (kappa0Cocycle DD.dat hdat).comap φU, by
      intro x y
      rw [hnorm]
      show graphPullback DD.dat (fun γ => rho0 DD ρM γ) c.c (x, y)
        = (kappa0Cocycle DD.dat hdat).κ (φU (levelProj U hNAle x)) (φU (levelProj U hNAle y))
      rw [hφlev, hφlev]
      exact graphPullback_eq_kappa0_graph hdat c (x, y)⟩ with hFdef
  -- assemble: A-2's evaluation + the level-change naturality (`relZPair_comap`); the marking
  -- identification `(univMarking.map mk'_U).map φU = gammaGen.map (graphSdHom c)` holds
  -- definitionally (`QuotientGroup.lift` computes at `mk`), so the rewrite closes by `rfl`
  have hA2 := IotaGammaA.QZero_eq_levelFactor_obs htriv c F
  rw [hA2]
  show (relZPair (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        ((kappa0Cocycle DD.dat hdat).comap φU)).1
      + (relZPair (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        ((kappa0Cocycle DD.dat hdat).comap φU)).2 = _
  rw [← relZPair_comap]
  rfl

end GammaA

end AffineTLift

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (61) = ⟦eq-basekappacochain⟧
  * eq. (62) = ⟦eq-baseconnectingcochain⟧
  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
-/
