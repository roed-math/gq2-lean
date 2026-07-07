# P-16d6c1c/c2 keystone — complete design record (Fable, 2026-07-07)

*The full derivation for the remaining (135)-keystone file (`GQ2/KeystoneDelta.lean`), worked
against the paper (pp. 40–43, read 2026-07-07) and the **landed** c1a/c1b layers.  Everything
below is verified by hand at cochain level; the Lean-ification is mechanical (lemma_6_22-style
atom calculus).  Read together with `GQ2/VLiftCount.lean`'s master count
`two_mul_card_centralImage`, whose hypotheses (`haff`, `hkey`, `Δ`, `sh`) this file discharges.*

## 0. Architecture change (F-decision, supersedes the c2/spec §2 `Lin`/`κρ`/`ερ` shapes)

The Lean engine's `phase140_of_nonsingular` interpolates the paper's (140) through `lemma_8_5`'s
`(Lin, κ_ρ, ε_ρ, N(κ,ε))`-data.  The verification pass showed the per-`(χ,ρ)` keystone in that
form requires an affineness-in-`χ` structure the paper never proves (the paper's (140) never
introduces `N(κ,ε)`).  **Resolution: a second, paper-faithful reducer was added** —
`phase140_of_phaseObstruction` (`GQ2/PhaseObstruction.lean`, std-3, landed) — consuming per `ρ`

```
2·|D_T| · #(central red_T image)(ρ) = |V| · (|V| + G0 · Σ_{ζ∈D_T} phaseSign (phase ζ) ρ)   (hMobst)
```

plus `hμ` (μ-independence) and `hWV`; it internally runs the `T`-torsor factoring, the
`Σρ↔Σζ` swap, and the (141) count `Σ_ρ (±1) = 2n_{Γ,0}(ζ) − e_Γ(C)` (`sum_phaseSign`), and
outputs the c1s-repaired `eq140` display with `μ`-slot `|V|·μ₀`.  `Lin`/`κρ`/`ερ`/`lemma_8_5`
are **gone** from this route; `DT := ↥(TCharC D)` (the `(T^∨)^C`-model, `GQ2/VLiftCount.lean`)
with `hDT` trivial.  The old `phase140_of_nonsingular` stays untouched (co-owned file, unused
by this route).

`hMobst` is delivered by `two_mul_card_centralImage` (landed, std-3) given the keystone data.
The per-(ζ,ρ) bridge `phaseSign (phaseCover (Δ ζ)) ρ = sign (iotaB (pullCoc ρ' (Δ ζ)))` is
`centralCover_lift_iff` + `centralCoverOfCocycle_exists_section` (both landed) — an e-side
one-liner per direction (`iotaB_eq_zero_iff` matches the `if`-branches).

## 1. Objects (all landed in c1a/c1b unless noted)

Setting: `D : RadicalCoverData Bg`, `DD : DescData D`, `Dsc : Descent D`,
`σ/hσ` a splitting of `piQbar` (`descended_splitting`), `S : CountSections DD σ`
(normalized set-sections `mV` of `descend`, `uσ` of `piT` over `σ`, both `1 ↦ 1`),
`ρ : Γ →ₜ* Bg⧸M`, `ρ' := rho0 DD ρ : Γ →* C₀`.

* `VCocycle DD ρ` = crossed `Z¹_{Γ,ρ}(V)`, an elementary-abelian-2 `AddCommGroup`; finite.
* `tDef S hσ c : Γ×Γ → ↥D.T` — the `T`-defect of `fLift c := γ ↦ mV(c γ)·uσ(ρ'γ)`.
* `betaChi χ c := ι_Γ(χ ∘ tDef c)`, `χ ∈ ↥(TCharC D)`;  `betaXi c := ι_Γ(g_c^* ξ)`.
* `QZero DD ρ c := ι_Γ(graphPullback DD.dat ρ' c.c)` — note
  `graphPullback dat ρ' b (γ,δ) = kappa0 dat ((b γ, ρ'γ), (b δ, ρ'δ))` **exactly** (defs match).
* `mem_centralImage_iff` (131): `c` is a central-image `V`-coordinate ⟺
  `TLiftable c ∧ betaXi c = 0`.

New in the keystone file — the **raw semidirect calculus** (no bundled `V⋊C` group):

* `pmul p q := (p.1 + p.2 • q.1, p.2 * q.2)` on `DD.Vmod × DD.C0`; `pone := (0,1)`;
  `pmul_assoc` from `mul_smul`/`smul_add`.
* `jmap p := iV(ofAdd p.1) * σ(p.2) : Bg⧸T`; `jmap_mul : jmap p * jmap q = jmap (pmul p q)`
  (the `sigma_iV_comm` computation, as in `qOfCocycle`); `jmap pone = 1`.
* `J p := (mV p.1 : Bg) * uσ p.2`;  `piT (J p) = jmap p`;  `J pone = 1`.
* graph relations (`graph_c γ := (c.c γ, ρ'γ)`): `fLift c γ = J (graph_c γ)` (rfl),
  `pmul (graph_c γ) (graph_c δ) = graph_c (γδ)` (crossed law + `map_mul`),
  `(qOfCocycle c).1 γ = jmap (graph_c γ)` (rfl).  Hence
  `chiDef χ c = graph_c^* ωχ` and `pullCoc g_c ξ = graph_c^* κfull` **pointwise**, where
  `ωχ(p,q) := χ(JDefT p q)`, `κfull(p,q) := ξ(jmap p, jmap q)`.

## 2. The explicit decomposition of `ωχ` (NO abstract extraction needed)

Define the three `T`-valued defect atoms (memberships via `piT`-images; `M_cent_T` moves them
past `M`-factors):

* `mDef v w := mV v · mV w · (mV (v+w))⁻¹ ∈ T` (descend-image cancels; `mDef v v = 1` by
  `M`-elementarity + `mV 0 = 1`; **symmetric** by `M`-abelianness),
* `conjDef cc w := uσ cc · mV w · (uσ cc)⁻¹ · (mV (cc•w))⁻¹ ∈ T` (piT-image dies by
  `sigma_conj_iV`),
* `uDef cc dd := uσ cc · uσ dd · (uσ (cc·dd))⁻¹ ∈ T` (piT-image dies since `σ` is a hom) —
  **this is the class `e`** of Lemma 8.7.

**Product formula** (`M` abelian, `T` centralized by `M`):

```
JDef((v,cc),(w,dd)) = conjDef cc w · uDef cc dd · mDef v (cc•w)        (all-T product)
```

(Derivation: `J p · J q = mVv·[conjDef·mV(cc•w)·uσcc]·mVw→…`; three regroupings.)  Hence with

* `fχ v x := χ(mDef v x)`, `mχ cc w := χ(conjDef cc w)`, `eχ cc dd := χ(uDef cc dd)`,
* `datχ := ⟨fχ, mχ⟩ : FactorSet DD.C0 DD.Vmod`:

```
ωχ = kappa0 datχ + inflScalar eχ,      IsEquivariantFactorSet (0 : V → ZMod 2) datχ.
```

The factor-set fields check as: `f_cocycle` = `mDef`-cocycle identity (pure `M`-abelian
computation) + `χ`-additivity; `f_diag` = `mDef v v = 1` (= the zero form ✓); `f_polar` =
symmetry; `m_quad` = the `conjDef`-additivity defect (`uσ`-conjugates of `mDef`s, killed to
`χ(mDef(w,w')) + χ(mDef(cc•w,cc•w'))` by `TCharC.conj_invariant`); `m_mul` = the
`uσ(cc)·uσ(dd)`-vs-`uσ(ccdd)` discrepancy is a `T`-conjugation, `χ`-invisible; `m_one` from
`uσ 1 = 1`.

**Zero-form `kappa0`-normal form** (explicit, generic): if `dat'` is an equivariant factor set
for the **zero** form and `g : V → 𝔽₂` splits its `f'` (`f' = ∂g`, exists by §3), then

```
kappa0 dat' = gammaEdge γ'' + ∂(G),   G(v,cc) := g v,
γ''(cc)(x) := m'(cc, cc⁻¹•x) + g x + g (cc⁻¹•x),   and γ''(cc) is ADDITIVE
```

(additivity: the `m_quad` and `g`-defects are both `f'`-values and cancel in char 2 —
derivation in the session log; ~15 lines).  Applied to `datχ`:
`ωχ = gammaEdge γ''χ + inflScalar eχ + ∂Gχ` with `gχ` := the splitting of `fχ` (per-`χ`
`Classical.choose` — no additivity in `χ` needed anywhere).

## 3. The `V`-splitting lemma (generic, used twice)

**Lemma.** A symmetric, zero-diagonal, normalized 2-cocycle `φ` on a finite elementary-abelian
2-group `V` is `∂g` for some `g : V → 𝔽₂` with `g 0 = 0`.

Proof: `E := ZMod 2 × V` with `(s,v)+(t,w) := (s+t+φ(v,w), v+w)` is an `AddCommGroup`
(assoc = cocycle identity, comm = symmetry, self-inverse = zero diagonal), hence a
`Module (ZMod 2)` (`AddCommGroup.zmodModule`, exponent 2); the projection to `V` is linear
(additive map + `ZMod 2`-scalars are `0/1`) and surjective, so it has a **linear section**
(`LinearMap.exists_rightInverse_of_surjective`, field scalars); the section's first coordinate
`g` satisfies `g(v+w) = g v + g w + φ(v,w)`.  `g 0 = 0` from additivity.

## 4. The `Θ`-extraction (the only opaque piece: `κfull`)

`Θ := κfull + kappa0 DD.dat` is a normalized raw cocycle on the `pmul`-monoid with **zero
diagonal on `V`** and **symmetric `V×V`-part**:

* cocycle: `κfull` from `xi_cocycle` + `jmap_mul`; `kappa0 dat` needs the raw Serre identity —
  prove from `f_cocycle/m_quad/m_mul` (or observe `graphPullback_mem_Z2`'s inner computation);
* normalization: `ξ(1,·) = ξ(·,1) = 0` (from `s0_one`; two mini-lemmas), `jmap pone = 1`,
  `f_zero_*`, `m_one`, and `m_c 0 = 0` (from `m_quad` at `(0,0)`);
* diagonal on `V`: `κfull((v,1),(v,1)) = ξ(iV v, iV v) = q̄ v` (`xi_diag`) and
  `kappa0 dat`-diag `= f(v,v) = q̄ v` (`f_diag`) — sum `0`;
* `V×V`-symmetry: `kappa0|_{V×V} = f` has polar `polar q̄` (`f_polar`); `κfull|_{V×V}` has the
  **same** polar by the cover-commutator computation on `covQ` (§5) — sum symmetric.

With `gκ` := the §3-splitting of `Θ|_{V×V}` and `Θ' := Θ + ∂(gκ ∘ fst)`, the four-chase
extraction (cocycle identity at `(p,q,r) = ((v,1),(0,cc),(w,dd))`, `((v,1),(x,1),(0,ee))`,
`((0,cc),(w,1),(0,dd))`, `((ccw,1),(0,cc),(0,dd))`) gives **exactly**

```
Θ' = gammaEdge γκ + inflScalar δκ + ∂uκ,
uκ(v,cc) := Θ'((v,1),(0,cc)),  δκ(cc,dd) := Θ'((0,cc),(0,dd)),
γκ(cc)(x) := Θ'((0,cc),(cc⁻¹•x,1)) + uκ(x,cc),
```

with `γκ(cc)` additive (fifth chase; the `uκ`-corrections absorb — session log has the exact
telescoping).  Hence

```
κfull = kappa0 DD.dat + gammaEdge γκ + inflScalar δκ + ∂(uκ + gκ∘fst).
```

## 5. The cover-commutator = polar lemma (for §4's symmetry)

For `a = iV v`, `b = iV w` (commuting, order ≤ 2 images): with `X := s0 a·s0 b·s0(ab)⁻¹ ∈ ker`,
`comm' := s0 b·s0 a·(s0 b)⁻¹·(s0 a)⁻¹ ∈ ker (descP)`:

* `ξ(a,b) + ξ(b,a) = ccZsign comm'` (kernel calculus; `Y = comm'·X`),
* `(s0(ab))² = comm' · (s0 a)² · (s0 b)²` (central kernel juggling; `X² = 1`),
* so `q̄(v+w) = ccZsign comm' + q̄ v + q̄ w` (`xi_diag` thrice) ⟹
  `ξ(a,b)+ξ(b,a) = polar q̄ v w`.

## 6. The keystone assembly

Set `γtot χ := γ''χ + γκ`, `δtot χ := eχ + δκ`, `Wχ := Gχ + uκ + gκ∘fst`,
`κgen χ := kappa0 DD.dat + gammaEdge (γtot χ) + inflScalar (δtot χ)`.  Then
`Ψχ := ωχ + κfull = κgen χ + ∂Wχ` **pointwise** (§2 + §4).

* **Dual-crossed law** for `γtot` (needed for the shear): derive **abstractly** from
  `κgen χ` being a cocycle (it equals cocycle + coboundary): the Serre identity at
  `((0,c),(0,d),(x,1))` forces `γ(cd)(cd•x)`-vs-`γ(c)/γ(d)`-relations modulo `m`-terms whose
  own `m_mul` law cancels them; outcome `γtot(c·d)(x) = γtot(c)(x) + γtot(d)(c⁻¹•x)`.
* `aχ := polarInv (γtot χ)` pointwise (via `exists_polar_inverse` on `q̄`, `En.hns`); the
  dual-crossed law + `polar` `C`-equivariance (`q̄` invariant) give the crossed law
  `aχ(cd) = aχ c + c•aχ d` (`ha`), so `sh χ := aχ ∘ ρ'` is a `VCocycle` (continuity through
  the discrete `Bg⧸M`).
* **`Δχ := DeltaScalar DD.dat (γtot χ) (δtot χ) (aχ)`** (the Lean-6.22-normalized total
  phase, cup term included — documented deviation (b), harmless as the family is existential).
* `prop_8_8_target q̄ hquad DD.dat hdat (γtot χ) (δtot χ) aχ ha hkill` gives `w` with the
  pointwise shear identity; pulling back along `graph_c` (using
  `shear aχ ∘ graph_c = graph_{c + sh χ}` and `pmul`-graph multiplicativity) and substituting
  `c ↦ c + sh χ` (char 2) yields the **exact cochain identity**

  ```
  graph_c^* Ψχ  +  graph_{c+shχ}^* (kappa0 DD.dat)  +  ρ'^* Δχ   ∈  B²(Γ,𝔽₂)
  ```

  (the three `∂`-terms have explicit continuous witnesses `w∘graph`, `Wχ∘graph`).
* `ι_Γ`-additivity (`iotaB_add`, `hH2`) splits it into **`hkey`**:
  `betaChi χ c + betaXi c = QZero (c + sh χ) + ι_Γ(ρ'^*Δχ)` — noting
  `chiDef χ c + xiPull c = graph_c^*Ψχ` pointwise and
  `graph^*(kappa0 dat) = graphPullback dat ρ'` definitionally.
  Memberships needed: `graph^*Ψχ ∈ Z2` (= `chiDef_mem_Z2` + `pullCoc_mem_Z2` at `xi_cocycle`),
  a generic-Γ `graphPullback ∈ Z2` (adapt `SectionSix.graphPullback_mem_Z2`'s inner computation
  — that one is `AbsGalQ2`-bound), and `ρ'Δχ ∈ Z2` (from `hcoc` below).

* **Normalizations for the phase covers** (c2's `hcoc/hl/hr`): `hcoc` because
  `inflScalar Δχ = shear^*κgen + kappa0 + ∂w` is a sum of cocycles (shear is a `pmul`-hom by
  `ha`), and the `((0,g),(0,h),(0,k))`-restriction of its Serre identity is the `C`-level
  cocycle law; `hl/hr` by direct evaluation (`aχ 1 = 0`, `eχ/δκ/uκ` normalized, `m_one`,
  `f_zero_*` — all listed in the session derivation).

* **`haff`** (the master count's affineness): from §2,
  `chiDef χ c = [cupχ c] + ρ'^*eχ + ∂(Gχ∘graph_c)` with
  `cupχ c (γ,δ) := γ''χ(ρ'γ)(ρ'γ • c.c δ)` **additive in `c`** (γ''-additivity); the fourfold
  sum `βχ(c+c') + βχ c + βχ c' + βχ 0` is `ι` of `2·cupχ(c) + 2·cupχ(c') + 4·ρ'eχ + ∂(…) = ∂(…)`,
  i.e. `0`.  (Each summand is in `Z2` as `graph^*ωχ + ∂`.)

## 7. What remains Γ-specific (threaded to P-16d6e's residue list)

`hsep` (the `(T^∨)^C`-separation, 5.16 cl. 6-side for `G_ℚ₂` / 5.15-side for `Γ_A` — the d6a
`hsep_hom` idiom), `hpartial` (∂-surjectivity: every `χ ≠ 0` has a `c` with
`betaChi χ c ≠ betaChi χ 0`), `hZcard` (`#Z¹_{Γ,ρ}(V) = #V²`), `hGaussZ`
(`Σ_c sign(QZero c) = #V · G0` — the source-Gauss transport; pin both sides via §6.2 as in
c3-G0, or Arf-parity), `hH2` (`#H²(Γ,𝔽₂) = 2`), `hμ` (P-16d6b + PhaseLIndep + per-source
`κ_M`/`κ_I`), `hfg`, `htriv`.

## 8. e-assembly sketch (per source, zero-edge case `hN : ∃ N…`)

`Dsc := ⟨choice hN⟩`; `DD := descDataOfEnrichment En l h` (fields map 1:1 — `C0 := RF.YC`,
`piC0 := RF.piBC`, `hkerC0 := RF.ker_piBC`, `descend/qbar/dat/…` from `En`; only wrapper);
`σ/hσ := descended_splitting DD Dsc`; `S := (countSections_exist …).some`;
`DT := ↥(TCharC (En.radData l h))`; `Δ` from the keystone file;
`phase ζ := centralCoverOfCocycle (Δ ζ) hcoc hl hr`; per-(ζ,ρ) sign bridge via
`centralCover_lift_iff` + the exported section; `hMobst := two_mul_card_centralImage …`;
`RecursionInputs.phase140 := fun l h hN => phase140_of_phaseObstruction …` — noting
`cardV := Nat.card En.Vmod`, `hWV := enrichment_card_Vmod`, `μ₀`-pinning via
`tcocycle_card_l_indep` + P-16d6b.  (139): `half139_via_radData` + `half139_local` (`G_ℚ₂`) /
P-16c (`Γ_A`).  (136): `blockStageR136_ofSplitCriterion` + routes in `p16d6a-handoff.md` §3.
Statement touch on `prop_8_9` (coordinate): add `0 < Nat.card DT` to the `∃` (P-17i) — free
since `0 ∈ TCharC D`; keep `hfgF` hypothesis-side (B1 reserved to P-17i).

## 9. Landed record (Fable 5, 2026-07-07) — name map for d6e

Everything in §§1–7 is now **landed and std-3** in `GQ2/KeystoneDelta.lean` (plus the c1b
files).  The d6e-facing names (all in `GQ2.SectionEight.AffineTLift`, binders as shown):

* **`shChi S Dsc hσ hinvQ χ : VCocycle DD ρ`** — the shear cocycle `a_χ ∘ ρ'` (§6's `sh_χ`).
* **`DeltaChi S Dsc hσ χ : DD.C0 × DD.C0 → ZMod 2`** — the total scalar phase
  `DeltaScalar DD.dat γtotHom δtotλ (achi …)` (§6's `Δ_χ`).
* **`keystone S Dsc hσ hinvQ htriv hH2 χ c`** — the (135)-Γ identity
  `betaChi S hσ χ c + betaXi hσ Dsc c
     = QZero DD ρ (c + shChi S Dsc hσ hinvQ χ) + iotaB (pullCoc ρ' (DeltaChi S Dsc hσ χ))`,
  i.e. `two_mul_card_centralImage`'s `hkey` at `Δ := DeltaChi S Dsc hσ`,
  `sh := shChi S Dsc hσ hinvQ`.  Γ-residues: `htriv`, `hH2` only.
* **`DeltaChi_cocycle S Dsc hσ hinvQ χ g h k`** — `hcoc` for `centralCoverOfCocycle`.
* **`DeltaChi_one_left / DeltaChi_one_right S Dsc hσ hinvQ χ cc`** — `hl` / `hr`.
* Support (new, reusable): `graphPullback_mem_Z2_of_cocycle` (generic-Γ Lemma 6.1/(62)),
  `graphCob_mem_B2`, `chiJDefT_serre`, `bundle_serre`, `theta'_pone_left/right`,
  `uDef_one_left/right`, `gammatot_zero`, `gammatot_one`, `achi_one`,
  `deltatot_one_left/right`.
* `hinvQ : IsInvariant DD.C0 DD.qbar` is the ONLY extra datum vs. `DescData` — supplied by
  `En.hinv` at e (as anticipated in §6).

So §8's sketch instantiates as: `phase ζ := centralCoverOfCocycle (DeltaChi S Dsc hσ ζ)
(fun g h k => DeltaChi_cocycle …) (DeltaChi_one_left …) (DeltaChi_one_right …)`, and
`hkey := keystone S Dsc hσ hinvQ htriv hH2`.  The per-(ζ,ρ) sign bridge (§8) is the one
remaining c-lane-adjacent lemma, owned by d6e.

Addendum (same day): the per-(ζ,ρ) sign bridge of §8 is ALSO landed generically —
**`sign_iotaB_pullCoc_eq_lift_sign`** (`GQ2/PhaseObstruction.lean`, LiftIff section, std-3):
`sign (iotaB (pullCoc ⇑f δ)) = if (∃ lift of f through centralCoverOfCocycle δ hcoc hl hr)
then 1 else -1` for any bundled `f : Γ →ₜ* Y₀`.  d6e instantiates it at `δ := DeltaChi S Dsc
hσ ζ`, `f :=` the bundled `rho0`-hom of `rhoPrime …ρ` (whose coercion is defeq to the master
count's `fun γ => rho0 DD ρ' γ`), and rewrites `phaseSign` by its definition — closing the
gap between `two_mul_card_centralImage`'s conclusion and `phase140_of_phaseObstruction`'s
`hMobst` up to the per-source residues.
