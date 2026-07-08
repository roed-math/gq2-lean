import GQ2.WordCoh2

/-!
# The mixed Heisenberg pairing as a relator obstruction (`mixedB = relZPair`)

A **generic** bridge (any finite `A`, `C` with `DistribMulAction C A`) recasting the traced
Heisenberg central coordinate `mixedB t x y` (`FoxHeisenberg`) as the `WordCoh2` relator-`z`
pair `relZPair (mBaseMarking t x y) kappaHeis` of an explicit 2-cocycle `kappaHeis` on the
base semidirect product `WordLift (A × A^∨) C`.

The structural heart is the isomorphism `HeisLift A C ≅ CentExt kappaHeis`: the map
`PhiHeis : CentExt kappaHeis →* HeisLift A C` carries the `liftMark` of `mBaseMarking` onto
`heisMarking t x y` and the fibre coordinate `.fib` onto the central coordinate `.z`.  Under
naturality of the relator values (`Marking.map_{tame,wild}Value`) this turns the traced-`z`
sum defining `mixedB` into the traced-`fib` sum defining `relZPair`.

This is the *source-generic, edge-free* half of the P-16c4 ledger identity
`obs(varCoc u) = mixedB t_ρ x_w y_φ`; the edge-specific half (identifying `varCoc u` with the
inflation of `kappaHeis`) is assembled downstream over the `RadicalCoverData` context.
-/

namespace GQ2

namespace MixedBObs

open FoxH WordCoh2

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The Heisenberg 2-cocycle** on the base semidirect product `(A × A^∨) ⋊ C`:
`κ((a,λ),g),((a',λ'),g')) = λ(g • a')`.  This is exactly the central defect of the
`HeisLift` multiplication, now packaged as a `TwoCocycle` so it can drive the `CentExt`
machinery of `WordCoh2`. -/
noncomputable def kappaHeis : TwoCocycle (WordLift (A × ElemDual A) C) where
  κ p q := p.u.2 (p.g • q.u.1)
  norm := by simp [WordLift.one_u]
  cocyc a b c := by
    show a.u.2 (a.g • b.u.1) + (a * b).u.2 ((a * b).g • c.u.1)
        = a.u.2 (a.g • (b * c).u.1) + b.u.2 (b.g • c.u.1)
    simp only [WordLift.mul_u, WordLift.mul_g, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
      Prod.smul_snd, map_add, ElemDual.add_apply, smul_add, mul_smul, ElemDual.smul_apply,
      inv_smul_smul]
    abel

/-- **The structural isomorphism** `CentExt kappaHeis →* HeisLift A C`, `(⟨(a,λ),g⟩, z) ↦ ⟨a,λ,z,g⟩`.
It is a homomorphism precisely because `kappaHeis`'s defect matches the `HeisLift`
multiplication's central term `λ(g • a')`. -/
noncomputable def PhiHeis : CentExt (kappaHeis (A := A) (C := C)) →* HeisLift A C where
  toFun p := ⟨p.base.u.1, p.base.u.2, p.fib, p.base.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl


/-- The base marking of `(A × A^∨) ⋊ C` whose generators carry the offsets `(x i, y i)` over
`t`'s generators — the base of the `heisMarking`. -/
noncomputable def mBaseMarking (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    Marking (WordLift (A × ElemDual A) C) :=
  ⟨⟨(x 0, y 0), t.σ⟩, ⟨(x 1, y 1), t.τ⟩, ⟨(x 2, y 2), t.x₀⟩, ⟨(x 3, y 3), t.x₁⟩⟩

omit [Group C] [DistribMulAction C A] in
/-- `mBaseMarking` is the `FoxHeisenberg` `liftMarking` at the paired offsets — the form the
`WordCohBridge` relator-death machinery (`liftMarking_eval_univ`) consumes. -/
theorem mBaseMarking_eq_liftMarking (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    mBaseMarking t x y = liftMarking t (fun i => (x i, y i)) := rfl

/-- `PhiHeis` carries the lift of `mBaseMarking` onto `heisMarking` (generator by generator). -/
theorem map_liftMark_mBase (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (liftMark (mBaseMarking t x y) kappaHeis).map PhiHeis = heisMarking t x y := rfl

/-- **`mixedB` is a relator-`z` pair.**  The traced Heisenberg central coordinate equals the
traced fibre coordinate of `kappaHeis`'s lifted base marking — i.e. `mixedB` *is* a `WordCoh2`
relator obstruction. -/
theorem mixedB_eq_relZPair [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A)
    (y : Fin 4 → ElemDual A) :
    mixedB t x y = (relZPair (mBaseMarking t x y) kappaHeis).1
                 + (relZPair (mBaseMarking t x y) kappaHeis).2 := by
  have htame := Marking.map_tameValue PhiHeis (liftMark (mBaseMarking t x y) kappaHeis)
  have hwild := Marking.map_wildValue PhiHeis (liftMark (mBaseMarking t x y) kappaHeis)
  rw [map_liftMark_mBase] at htame hwild
  show (heisMarking t x y).tameValue.z + (heisMarking t x y).wildValue.z = _
  rw [htame, hwild]
  rfl

/-! ## Obstruction of an inflated cocycle

The `WordCoh2` obstruction `obs` of a continuous 2-cocycle on `Γ_A` that factors *pointwise*
through a finite group `L` (`φ(a,b) = κ(H a)(H b)`) is the relator-`z` pair of the pushforward
marking `gammaGen.map H`.  This packages the entire `LevelFactor` / `relZPair_comap` computation
once and generically, so the edge-specific ledger identity is a one-line application. -/

section Inflation

open WordCohBridge ContCoh

variable [DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
  [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
  (htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NA) (m : ZMod 2), x • m = m)

/-- **Obstruction of an inflated cocycle.**  If a continuous 2-cocycle `φ` on `Γ_A` factors
pointwise through a finite group `L` as `φ(a,b) = κ(H a)(H b)` for a continuous hom
`H : Γ_A → L` and a 2-cocycle `κ` on `L`, its obstruction is the relator-`z` pair of the
pushforward marking `gammaGen.map H`. -/
theorem obs_inflation {L : Type*} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
    (H : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) L) (κ : TwoCocycle L)
    (φ : Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2))
    (hφ : ∀ a b, φ.1 (a, b) = κ.κ (H a) (H b)) :
    obs htriv φ = (relZPair (gammaGen.map H.toMonoidHom) κ).1
                + (relZPair (gammaGen.map H.toMonoidHom) κ).2 := by
  set G := H.comp (quotientMk NA) with hG
  have hNA : NA ≤ G.toMonoidHom.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    show H (quotientMk NA g) = 1
    rw [(quotientMk_eq_one_iff NA).mpr hg, map_one]
  have hopen : IsOpen ((G.toMonoidHom.ker : Subgroup (FreeProfiniteGroup (Fin 4)))
      : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((G.toMonoidHom.ker : Subgroup (FreeProfiniteGroup (Fin 4)))
        : Set (FreeProfiniteGroup (Fin 4))) = G ⁻¹' {1} := by
      ext g; simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set L)).preimage G.continuous_toFun
  set U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := G.toMonoidHom.ker, isOpen' := hopen } with hU
  have hUsub : NA ≤ U.toSubgroup := hNA
  set Gbar := QuotientGroup.kerLift G.toMonoidHom with hGbar
  have hhom : Gbar.comp (QuotientGroup.mk' U.toSubgroup)
      = H.toMonoidHom.comp (quotientMk NA).toMonoidHom := by
    ext g
    show Gbar (QuotientGroup.mk' U.toSubgroup g) = H (quotientMk NA g)
    exact QuotientGroup.kerLift_mk G.toMonoidHom g
  have hGbarproj : ∀ a : FreeProfiniteGroup (Fin 4) ⧸ NA, Gbar (levelProj U hUsub a) = H a := by
    intro a
    obtain ⟨g, rfl⟩ := quotientMk_surjective NA a
    rw [levelProj_quotientMk]
    exact QuotientGroup.kerLift_mk G.toMonoidHom g
  have hnorm : φ.1 (1, 1) = 0 := by rw [hφ, map_one, κ.norm]
  have hfact : ∀ p q, normalizeCochain φ.1 (p, q)
      = (κ.comap Gbar).κ (levelProj U hUsub p) (levelProj U hUsub q) := by
    intro p q
    rw [TwoCocycle.comap_κ, hGbarproj, hGbarproj, ← hφ]
    show φ.1 (p, q) - φ.1 (1, 1) = φ.1 (p, q)
    rw [hnorm, sub_zero]
  have hmark : (univMarking.map (QuotientGroup.mk' U.toSubgroup)).map Gbar
      = gammaGen.map H.toMonoidHom := by
    rw [Marking.map_map, gammaGen, Marking.map_map, hhom]
  show obsFun htriv φ = _
  rw [obsFun_eq htriv φ ⟨U, hNA, κ.comap Gbar, hfact⟩]
  show (relZPair (univMarking.map (QuotientGroup.mk' U.toSubgroup)) (κ.comap Gbar)).1
      + (relZPair (univMarking.map (QuotientGroup.mk' U.toSubgroup)) (κ.comap Gbar)).2 = _
  rw [← relZPair_comap, hmark]

end Inflation

end MixedBObs

end GQ2
