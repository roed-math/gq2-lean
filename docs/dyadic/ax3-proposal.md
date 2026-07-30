# AX3 proposal — `MarkedRecip`: marked local reciprocity for finite dyadic `K`

**Ticket AX3** (dyadic campaign, lane AX; board `docs/dyadic/tickets.md:339`, plan §4 row AX3).
Memo only — no Lean lands with this commit, census unchanged (9).  Protocol: this memo → owner
sign-off (**G-AX**) → census-flip commit per the b9a checklist (`docs/orchestration/b9a-tickets.md`).
Until the flip, every consumer binds the statement as an explicit hypothesis (§7).

Sources: packet `refs/dyadic-presentations-formalization-proof.tex` §8 (Prop 8.1 :774, Cor 8.2
:801), §12 local-inputs table (`MarkedRecip` row :1000–1002), §7 (Def 7.1 :711, Prop 7.2 :726),
§3 (Prop 3.4 :258, Thm 3.5 :288); draft `refs/dyadic-presentations.tex` §2 (eq:CI :232,
eq:lambda :237, eq:gamma :242, Warning :246, type-`N` paragraph :326–346), §7 (:1030–1144),
§10.2 (:1307–1324).  Packet overrides draft where they disagree (`refs/README.md`); nothing in
this memo hits a disagreement except the sign row, which is already settled (packet Prop 8.1).

Repo state referenced at branch `dyadic-ax` (= `dyadic` = `master` `d0714a7` for all cited
files).

---

## 0. What the interface must deliver (consumer-derived spec)

The packet's `MarkedRecip` row (§12 :1000): *"The full ℤ₂-valued geometric unramified character
and the marked cyclotomic quotient (C, I, λ, γ)."*  Concretely, with `G_K = K.fixingSubgroup`,
`D_K = G_K(2)`, `χ = χ_K : G_K → ℤ₂ˣ` the 2-cyclotomic character and `ν = ν_ur^K : G_K ↠ ℤ₂`
normalized geometrically (`ν(Φ_geom) = 1`, draft :142–146):

```
C = χ(D_K) = χ(G_K),   I = χ(ker ν),   A = ν(ker χ) = 2^r ℤ₂          (draft eq. 2.1)
λ : C ↠ ℤ/2^r,  λ(χ g) = ν(g) mod 2^r                                  (draft eq. 2.2)
γ = χ(σ)·I ∈ C/I for σ a geometric Frobenius lift,  λ(γ) = 1           (draft eq. 2.3)
```

Consumers and what they touch:

| consumer | needs | where |
|---|---|---|
| F4 branch classification | `(C,I,λ,γ)`-level data (abstract, no field) **plus** the field bridge for the corollary "η even ⇒ K(i)/K unramified" (packet Prop 8.1) and Cor 8.2's `(r,ε,η) = (1,1,1)` test vector | `tickets.md:143–151` |
| MC5 marked-core certificate | the K-side marked pair `(χ_K, ν_K)` on `D_K` and its `(C,I,λ,γ)`, to feed packet Prop 7.2's "equality of the marked data produces ū" | `tickets.md:234–241`; packet :739–746 |
| B1 boundary lane (future) | full `ν_K` on `G_K`, surjective, whose tame factorization matches AX4's `ν_t` and whose pro-2 factorization is the marked `ν` on `D_K` (packet Prop 3.4(3), Thm 3.5); merge gate 7.6 "full ℤ₂-valued marking, mod 2 not enough" | plan §7.6; packet :258–307 |
| AS3/AS5 instances + final theorem | per-field computability of `(C, I, λ, γ, r, ε, η)` (five quadratic test vectors, §5) and the statement vocabulary for "the isomorphism identifies … the full geometric unramified character" (packet Thm 1.1 :136–138) | `tickets.md:445–472` |

Design constraint from the trust boundary (plan §0.3, packet :1023): the axiom may assert only
independently published local CFT facts about `G_K`; never anything word- or presentation-side.

---

## 1. Decomposition: derivable vs axiom-worthy

### 1.1 `χ_K` — the cyclotomic character of `G_K`.  **(a) derivable, zero new axioms.**

The existing object carrying χ on the ℚ₂ side is **`GQ2.chiCyc`** (`GQ2/Reciprocity.lean:128`)
— Mathlib's `cyclotomicCharacter (AlgebraicClosure ℚ_[2]) 2` precomposed with the Galois action
— together with its abelianized descent `chiCycAb` (:144).  It is *not* B3c: B3c's `chiTwo`
(`GQ2/Orientation.lean:77`) is the D₀-side descent bundled with the Labute normalization; the
raw character is `chiCyc` and is axiom-free.  (`GQ2/MuN.lean:151` is only the B6 coefficient
module, not the character.)

Since `μ_{2^∞} ⊂ ℚ̄₂` and its Galois action are the same for every subgroup of the ambient
group, `χ_K` **is the literal restriction**:

```
noncomputable def chiCycK (K) : ↥K.fixingSubgroup →* ℤ_[2]ˣ := chiCyc.comp K.fixingSubgroup.subtype
```

Derivation sketch of the abelianized/descended forms (all formal):
`commClosureK := (commutator ↥K.fixingSubgroup).topologicalClosure ≤ ker` (continuous into
abelian T2 — verbatim the `commClosure_le_ker_chiCyc` proof, `GQ2/Reciprocity.lean:138`), lift
to `GalKab K := ↥K.fixingSubgroup ⧸ commClosureK`; descent to
`D_K := maxProPQuotient 2 ↥K.fixingSubgroup` (`GQ2/MaxProP.lean:152`) via
`proPKernel_le_ker` + `isProP_two_unitsPadicInt` (`GQ2/ZtwoPowering.lean:559` — this instance
now exists, so the device B3c avoided is available; cf. `GQ2/Orientation.lean:45–48`).

Plumbing hazard (not mathematics): `K.fixingSubgroup` lives in `Kummer.GaloisGroup ℚ_[2]`
(`GQ2/Kummer.lean:68`) while `chiCyc`'s domain is `AbsGalQ2` — definitionally equal types with
**different registered `Group` instances**; pin the domain as in the `restrictHom` precedent
(`GQ2/Reciprocity.lean:166–171`).

### 1.2 `ν_ur^K` — the full ℤ₂-valued unramified character.  **(c) irreducible published input** (clause-pinned, §2).

Answer to the dispatch's normalization question (`ν_K = (1/f)·ν_{ℚ₂}|_{G_K}`?): at the Ẑ level
`ν̂_{ℚ₂}|_{G_K} = f · ν̂_K` — geometric Frob_K restricts to Frob_{ℚ₂}^f on ℚ₂^ur (residue field
𝔽_{2^f}), so **`ν_{ℚ₂}(Frob_K) = f`**, and taking 2-primary components commutes with the
integer multiplication, giving `ν_{ℚ₂}|_{G_K} = f · ν_K` on the ℤ₂ parts.  So restriction
determines `ν_K` **only together with the exact-divisibility fact**
`ν_{ℚ₂}(G_K) = f·ℤ₂` — and when `f` is even this is strictly more than the restriction:
for `K = ℚ₂(√5)` (`f = 2`) the restricted character has image `2ℤ₂`, is not surjective, and
"divide by 2" is not a hom you can extract from it without knowing the divisibility, which is
itself unprovable in-repo (no ramification theory; B13's residue degree
`f` in `DyadicUnitFiltration` is pinned only by unit-filtration counts,
`GQ2/Foundations/Interfaces.lean:280–314`).  **Verdict: B5/B10 restrict to `f·ν_K`, which
underdetermines the required datum; `ν_K` is genuinely new content.**  We do *not* axiomatize
the `f`-relation; instead we pin `ν_K` the way B5 pins `ν_ur` — through `rec_K` on units and
uniformizers — and the `f`-relation becomes a **derivable stress test** (§2.4) using the
in-repo norm-valuation identity `‖N x‖ = ‖x‖^n` (`GQ2/UnitNormIndex.lean`, `norm_val`) plus
`n = e·f` from B13.

Soundness inheritances from B5 (`GQ2/Reciprocity.lean:75–79`): the target must be
`Multiplicative ℤ_[2]` (profinite), never `ℤ` — a discrete target would make the axiom prove
`False`.

### 1.3 `rec_K` and the reciprocity clauses.  **(c) irreducible published input**, minimized.

Mirror of B5's bundle at base `K`, with two deliberate deviations:

* **(c1) norm functoriality replaces the general cyclotomic clause.**  The standard diagram
  `incl_* ∘ rec_K = rec_{ℚ₂} ∘ N_{K/ℚ₂}` (inclusion of groups ↔ norm of fields; *not* the
  transfer diagram, which pairs with the field inclusion) lets the general-K cyclotomic values
  be **derived** from B5's clause (c): `χ_K^ab(rec_K x) = χ_{ℚ₂}^ab(rec_{ℚ₂}(N x))` = the
  inverse of the unit part of `N_{K/ℚ₂} x`.  This single clause is what makes `C`, `I`, `λ`
  instance-computable through Hilbert-symbol/norm arithmetic (§1.5, §5) — it is "where genuine
  K-reciprocity enters".  The norm map already has the repo spelling
  `Units.map (Algebra.norm ℚ_[2])` (`normSubgroup`, `GQ2/Reciprocity.lean:161`).
* **Clause (a) (norm residue over K: `Gal(L/K) ≅ Kˣ/N_{L/K}Lˣ` for finite abelian `L/K`) is
  omitted.**  Consumer audit (§0) found no dyadic-campaign consumer: the ℚ₂ clause (a) is
  consumed only by `GQ2/UnitNormIndex.lean` (`norm_reciprocity` grep), whose K-analogue no lane
  needs.  Omitting it keeps the axiom strictly smaller than a verbatim B5-at-K; it can be added
  as a bundle field later (statement extension, owner-gated) if a lane surfaces a need.
  **Owner question Q2.**

The unit/uniformizer ν-clauses `(b_K)` are stated without introducing a valuation `v_K` (no
such object exists in-repo): units via the B11b idiom `‖(u : ℚ̄₂)‖ = 1`
(`GQ2/Foundations/Interfaces.lean:222`), uniformizers via the B13 idiom "maximal spectral norm
`< 1`" (`GQ2/Foundations/Interfaces.lean:283–285`).  Existence of a uniformizer (so the
∀-clause has content) is supplied by the axiom-free `dyadicUnitFiltration K` (:311).

### 1.4 `C = χ(D_K)`.  **(a) derivable as a definition; values are instance work.**

`C := (chiCycKAb K).range` — no clause.  `χ(D_K) = χ(G_K) = χ(G_K^ab)-image` because `ℤ₂ˣ` is
pro-2 and abelian (both factorizations formal).  The **values** of `C` per field are where
LCFT's "cyclotomic image ↔ norm data" enters, and they are *derivable per instance* from (c1) +
B5(c) + density: `C = closure χ(rec_K Kˣ) = (unit parts of N_{K/ℚ₂}(Kˣ))⁻¹-closure` (image of
a compact group is closed; `denseRange` clause).  Norm-group membership is decided by the
in-repo Hilbert layer: B11a `hilbertSymbol_normCriterion_finiteDyadic`
(`GQ2/Foundations/Axioms.lean:368`) at base ℚ₂ with `a = d` decides `b ∈ N_{ℚ₂(√d)/ℚ₂}` via
the norm form, and B7′ `hilbertSymbol_dyadic` (`GQ2/Foundations/Interfaces.lean:66`) computes
the symbol.  The finite-level pinning of a closed subgroup of `ℤ₂ˣ × ℤ₂` from finitely many
generators (mod 16 × mod 4 suffices for all five quadratic fields) is kernel-`decide` work.
So: **no C-clause in the axiom.**  The B11a/`unramifiedQuadratic_units_are_norms`/
`dyadicNormCriterion` interfaces asked about in the dispatch are exactly sufficient for the
finite-level consequences the theorem consumes; nothing new is needed on the norm side.

### 1.5 `I`, `λ`, surjectivity, `γ`.  **(b) derivable from a smaller new clause — the `(r, A)` pack.**

The one genuinely new finiteness fact is draft eq. 2.1's third equation:

> `A = ν_ur(ker χ) = 2^r ℤ₂` for some finite `r`.

Formal parts (derivable): `ν(ker χ)` is a closed subgroup of ℤ₂ (compact image); closed
subgroups of ℤ₂ are `0` or `2^r ℤ₂` (closed ⇒ ℤ₂-submodule by density of ℤ ⇒ ideal of a DVR).
Non-formal part: **`ν(ker χ) ≠ 0`**, i.e. the unramified part of the cyclotomic 2-tower
`K(μ_{2^∞})/K` is finite.  We carry `(r, hA)` as axiom data (two ∀∃ clauses, §2), which is the
verbatim shape of eq. 2.1.

Everything else in the `(C, I, λ, γ)` block is then **derived** (proof sketches, all short):

* **λ well-defined**: `χ g = χ g' ⇒ ν g ≡ ν g' (mod 2^r)` — immediate from `hA`(⊆).
* **`I = ker λ`**: `I = χ(ker ν) ⊆ ker λ` trivially; conversely if `λ(χ g) = 0` then
  `ν g ∈ 2^r ℤ₂ = ν(ker χ)` (hA ⊇), pick `h ∈ ker χ` with `ν h = ν g`, then `g h⁻¹ ∈ ker ν`
  and `χ(g h⁻¹) = χ g`.  (This equality is what makes "I" and "ker λ" interchangeable in F4.)
* **λ surjective**: `ν` surjective (itself derived: the image is a closed subgroup of ℤ₂
  containing `ν(rec π)^ℤ = (−1)·ℤ`, closure ℤ₂ — uses only clause (b_K)-uniformizer and
  compactness; B5 carries surjectivity as a field, we do not need to).
* **`γ` well-defined with `λ γ = 1`**: any `σ` with `ν σ = 1` exists by surjectivity; two such
  differ by `ker ν`, whose χ-image is `I`; `λ(χ σ) = ν σ = 1 mod 2^r`.
* **`I` is the honest inertia image** (mathematical faithfulness note, not a Lean obligation):
  `ker ν ⊇ inertia` with pro-odd quotient (odd part of Frobenius), and χ kills any pro-odd
  image inside the pro-2 target `ℤ₂ˣ`, so `χ(ker ν) = χ(I_K)`.  This is why eq. 2.1's `I`
  deserves the name; it is also why positive `I`-membership is instance-derivable from *unit*
  norms only: `rec(unit) ∈ ker ν` by (b_K), so `closure χ(rec(O_Kˣ)) ⊆ I`, while negative
  membership `c ∉ I` follows from a `λ`-value ≠ 0.  In particular `(1+8ℤ₂) ⊆ I` always, since
  `N_{K/ℚ₂}(w) = w^n` for `w ∈ ℤ₂ˣ ⊆ O_Kˣ` and `(ℤ₂ˣ)² = 1+8ℤ₂` (Hensel; in-repo squares
  machinery).  No "rec(units) = inertia" clause (Serre LF XIII §4 Prop 13 shape) is needed in
  the axiom: consumers never need the *equality*, only the two derivable directions above.

### 1.6 The fixed-field bridge ("K(i)/K unramified ⟺ …").  **(c) one composite clause, one direction.**

Packet Prop 8.1's proof (:783–799) uses exactly: *if the inertia image `I` acts trivially on
`μ₄` (i.e. `I ⊆ 1 + 4ℤ₂`), then `K(i)/K` is unramified.*  Where `K(i)` lives in the repo:
`quadExt K δi` (`GQ2/TraceForm.lean:68`) with `δi² = −1`; "unramified" has exactly one repo
spelling — the deliberately-isolated convention `HasEqualNormValueGroups K δi`
(`GQ2/Foundations/Interfaces.lean:109`, the B11b hypothesis; negative stress test :128 shows it
genuinely detects `e = 1`; note it is trivially satisfied when `i ∈ K`, which is the correct
convention for the degenerate case).  Only the **data ⇒ field** direction is ever consumed
(Prop 8.1 itself, and its contrapositive turning the standing ramified-`i` hypothesis into
"η odd"), so the clause is a single implication:

> if every `g ∈ ker ν` has `χ(g) ≡ 1 (mod 4)`, then `HasEqualNormValueGroups K δi` for every
> square root `δi` of `−1`.

This is the composite where "(C,I,λ) ↔ actual field extensions" faithfulness is concentrated;
class-3 by construction (inertia-fixed-field + the repo's `e = 1` convention).  The converse
direction is deliberately not asserted (nothing consumes it; the final theorem's ramified-`i`
hypothesis can be discharged per instance by a `¬HasEqualNormValueGroups` proof in the
`not_hasEqualNormValueGroups_sqrt_two` pattern, or the hypothesis can be spelled in marked-data
form — **owner question Q4**).

### 1.7 Summary table

| component | class | mechanism |
|---|---|---|
| `χ_K`, `χ_K^ab`, descent to `D_K` | (a) derivable | restriction of `chiCyc` (`GQ2/Reciprocity.lean:128`); lifts formal (§1.1) |
| `C` (as object) | (a) derivable | `:= (chiCycKAb K).range` |
| `C` (values per field) | (a) derivable per instance | (c1) + B5(c) + density + B7′/B11a norm arithmetic (§5) |
| `rec_K` (existence, continuity, density) | (c) axiom | NSW (7.1.1)/(7.1.5) at base `K` |
| `(b_K)` ν-normalization on units/uniformizers | (c) axiom | Serre LF XIII §4 Prop 13 + geometric convention (B5/B10′ house normalization) |
| (c1) norm functoriality vs B5 | (c) axiom | Serre LF Ch. XI §3 / NSW class-formation functoriality (verify numbers, Q7) |
| clause (a) norm residue over K | omitted | no consumer (Q2) |
| `ν_K` surjectivity | (b) derived | from (b_K)-uniformizer + compactness (§1.5) |
| `(r, A = 2^r ℤ₂)` | (c) axiom (2 clauses) | draft eq. 2.1; finiteness of the unramified part of the cyclotomic tower |
| `λ`, `I = ker λ`, λ-surjectivity, `γ` | (b) derived | §1.5 from `hA` + surjectivity |
| K(i) bridge (one direction) | (c) axiom (composite) | §1.6 |
| `f`-relation `ν_{ℚ₂}∘incl = f·ν_K` | derived stress test | §1.2, §2.4; never a clause |

---

## 2. The proposed interface

### 2.1 Definition layer (axiom-free file, `module`-style leaf)

New statement file — working name `GQ2/Dyadic/MarkedRecipBundle.lean`, namespace `GQ2.Dyadic`
(module-style; it must stay importable from `GQ2/Foundations/Axioms.lean`, hence may `public
import` only statement-layer files: `GQ2.Reciprocity`, `GQ2.Kummer`-side vocabulary; **not**
the §8/§9 stack, and — cycle alert — not `GQ2.Foundations.Interfaces`, see Q3).  Contents:

```lean
variable (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]

/-- `G_K = Gal(ℚ̄₂/K)` as the fixing subgroup, the repo's K-side vocabulary (B6/B9/B11a). -/
abbrev GalK : Type := ↥K.fixingSubgroup

/-- Closed commutator subgroup and topological abelianization of `G_K`
(the `commClosure`/`AbsGalQ2ab` device of `GQ2/Reciprocity.lean:110–121`, verbatim at `K`). -/
noncomputable abbrev commClosureK : Subgroup (GalK K) := (commutator (GalK K)).topologicalClosure
noncomputable abbrev GalKab : Type := GalK K ⧸ commClosureK K
noncomputable def toAbK : GalK K →* GalKab K := QuotientGroup.mk' (commClosureK K)

/-- Restriction of the 2-adic cyclotomic character to `G_K` (§1.1) and its descent. -/
noncomputable def chiCycK : GalK K →* ℤ_[2]ˣ := ...     -- chiCyc ∘ subtype, instance-pinned
noncomputable def chiCycKAb : GalKab K →* ℤ_[2]ˣ := ... -- lift, kills commClosureK

/-- The abelianized inclusion `G_K^{ab} →* G_{ℚ₂}^{ab}` (lift of `toAb ∘ subtype`). -/
noncomputable def inclAbK : GalKab K →* AbsGalQ2ab := ...

/-- Norm on units, `(↥K)ˣ →* ℚ₂ˣ` (the `normSubgroup` map, `GQ2/Reciprocity.lean:161`). -/
noncomputable def normUnitsK : (↥K)ˣ →* ℚ_[2]ˣ := Units.map (Algebra.norm ℚ_[2] (S := K)).toMonoidHom
```

### 2.2 The bundle

```lean
/-- **Marked local reciprocity for a finite dyadic `K` (the packet's `MarkedRecip`).**
The arithmetic reciprocity map `rec_K` and the geometric full `ℤ₂`-valued unramified
coordinate `ν_ur^K`, pinned against the ℚ₂ bundle `R` by norm functoriality, together with the
marked cyclotomic quotient datum `(r, A = 2^r ℤ₂)` of draft eq. 2.1 and the `K(i)`
fixed-field bridge (packet Prop. 8.1's input).  `C`, `I`, `λ`, `γ` are *derived* from these
fields (see the interface file), not carried.  Conventions inherited verbatim from B5
(`GQ2/Reciprocity.lean` module docstring): `rec` arithmetic, `ν` geometric
(`ν(rec π) = −1` for a uniformizer `π`), `ν`-target the profinite `Multiplicative ℤ₂`
(soundness: a discrete target would be inconsistent). -/
structure MarkedRecip (R : LocalReciprocity)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K] where
  /-- The arithmetic local reciprocity map `rec_K : Kˣ →* G_K^{ab}`. -/
  recip : (↥K)ˣ →* GalKab K
  /-- `rec_K` is continuous. -/
  continuous_recip : Continuous recip
  /-- `rec_K` has dense image (`G_K^{ab}` is the profinite completion of `Kˣ`). -/
  denseRange_recip : DenseRange recip
  /-- The full unramified coordinate `ν_ur^K : G_K^{ab} →* Multiplicative ℤ₂` (target
  profinite — B5 soundness note). -/
  nu_ur : GalKab K →* Multiplicative ℤ_[2]
  /-- `ν_ur^K` is continuous. -/
  continuous_nu_ur : Continuous nu_ur
  /-- **(c1) Norm functoriality against the ℚ₂ bundle**: `incl_* ∘ rec_K = rec ∘ N_{K/ℚ₂}`.
  [Serre LF Ch. XI §3; NSW class-formation functoriality — this is the inclusion↔norm
  diagram, *not* the transfer↔field-inclusion diagram.] -/
  norm_compat : ∀ x : (↥K)ˣ, inclAbK K (recip x) = R.recip (normUnitsK K x)
  /-- **(b_K) units.** `ν_ur^K(rec_K u) = 1` for every unit (`‖u‖ = 1`, the B11b idiom).
  [Serre LF Ch. XIII §4, Prop. 13: reciprocity maps units into (onto) inertia.] -/
  nu_ur_recip_unit : ∀ u : (↥K)ˣ, ‖((u : ↥K) : AlgebraicClosure ℚ_[2])‖ = 1 →
      nu_ur (recip u) = 1
  /-- **(b_K) uniformizers.** `ν_ur^K(rec_K π) = ofAdd (−1)` for `π` of maximal norm `< 1`
  (the B13 uniformizer idiom): `rec_K π` is arithmetic Frobenius mod inertia; geometric
  coordinate `−1`.  [Serre LF XIII §4 Prop. 13 corollary; B10′ orientation pattern.] -/
  nu_ur_recip_uniformizer : ∀ π : (↥K)ˣ,
      ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖ < 1 →
      (∀ z : ↥K, z ≠ 0 → ‖(z : AlgebraicClosure ℚ_[2])‖ < 1 →
        ‖(z : AlgebraicClosure ℚ_[2])‖ ≤ ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖) →
      nu_ur (recip π) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2])
  /-- The marked level `r`: `ν_ur^K(ker χ_K) = 2^r ℤ₂` (draft eq. 2.1's `A`).  Finiteness of
  `r` = finiteness of the unramified part of `K(μ_{2^∞})/K`. -/
  r : ℕ
  /-- `A ⊆ 2^r ℤ₂` (λ well-definedness direction). -/
  nu_ker_chi_le : ∀ g : GalKab K, chiCycKAb K g = 1 →
      ∃ y : ℤ_[2], (nu_ur g).toAdd = 2 ^ r * y
  /-- `A ⊇ 2^r ℤ₂` (exactness of the level; `I = ker λ` direction). -/
  nu_ker_chi_ge : ∀ y : ℤ_[2], ∃ g : GalKab K,
      chiCycKAb K g = 1 ∧ (nu_ur g).toAdd = 2 ^ r * y
  /-- **The `K(i)` fixed-field bridge** (packet Prop. 8.1's input, one direction): if the
  inertia image `I = χ(ker ν)` lies in `1 + 4ℤ₂` (trivial action on `μ₄`), then `K(i)/K` is
  unramified in the repo's equal-norm-value-groups convention.  [Composite: Galois
  correspondence for the inertia fixed field + the `e = 1` criterion; the convention is the
  isolated `def` `HasEqualNormValueGroups`, B11b precedent.] -/
  ki_unramified : (∀ g : GalKab K, nu_ur g = 1 →
        (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1) →
      ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi
```

Notes on the encoding:

* `PadicInt.toZModPow 2 : ℤ_[2] →+* ZMod 4` (mathlib `RingHoms.lean:445`) encodes
  "`≡ 1 mod 4`"; the same map at exponent `r` powers the λ extraction (§4).
* No `surjective_nu_ur`, no clause (a_K), no `C`/`I`/`λ`/`γ` fields, no `f` field — all
  derived or omitted per §1.  This is the smallest field list found that covers §0's consumer
  matrix.
* Dependent fields (`nu_ker_chi_*` mention `r`) are ordinary Lean structure dependency.
* The structure is parametrized by `R : LocalReciprocity` exactly as B10′'s
  `OrientedTameQuotient (R : LocalReciprocity)` (`GQ2/TameQuotient.lean:99`); at the axiom
  use-site it is pinned to the B5 axiom.

### 2.3 The axiom (draft statement for `GQ2/Foundations/Axioms.lean`)

One new axiom (§6 for the count discussion), quantified over the base like B6's
`tateDualityAt` (`GQ2/Foundations/Axioms.lean:197`):

```lean
/-- **[Composite — AX3 (marked local reciprocity over finite dyadic `K`).]**  Local class
field theory for every finite `K/ℚ₂` inside `ℚ̄₂` provides the marked reciprocity bundle:
the arithmetic reciprocity map `rec_K` (continuous, dense image) and the geometric full
`ℤ₂`-valued unramified coordinate `ν_ur^K`, normalized on units and uniformizers, compatible
with the `ℚ₂` bundle B5 under `N_{K/ℚ₂}` (norm functoriality), carrying the marked cyclotomic
level `r` with `ν_ur^K(ker χ_K) = 2^r ℤ₂` (the draft's eq. 2.1 datum `A`), and the `μ₄`
fixed-field bridge (trivial inertia action on `μ₄` implies `K(i)/K` unramified in the
equal-norm-value-groups convention).  The derived layer (`GQ2/Dyadic/MarkedRecipBundle.lean`)
constructs from these fields the marked cyclotomic quotient `(C, I, λ, γ)` of draft
eq. 2.1–2.3 = the packet's §12 `MarkedRecip` interface; surjectivity of `ν_ur^K` and of `λ`,
`I = ker λ`, and the Frobenius coset `γ` with `λ(γ) = 1` are theorems over the bundle, not
clauses.

**Composite classification** (the B3c/B8/B11a class): (i) existence/density of `rec_K` and
the unit/uniformizer normalization are classical [NSW (7.1.1)/(7.1.5) at base `K`; Serre LF
Ch. XIII §4 Prop. 13 and corollary]; (ii) norm functoriality is classical [Serre LF Ch. XI §3;
NSW Ch. I §5 functoriality — exact proposition numbers verified at G-AX]; (iii) the finite
level `r` is the classical finiteness of the unramified part of the 2-cyclotomic tower over
`K`; (iv) the `K(i)` bridge couples the inertia fixed-field correspondence to the repo's
`HasEqualNormValueGroups` convention (a `def`, asserted by nothing — B11b precedent).  The
clause set deliberately omits the finite-layer norm-residue isomorphism (no consumer) and
asserts nothing word- or presentation-side (packet §12 trust boundary).

Citation: NSW [1] (7.1.1)/(7.1.5); Serre, *Local Fields* [7], Ch. XI §3, Ch. XIII §4
Prop. 13; cyclotomic-tower ramification: Serre LF Ch. IV; NSW Ch. VII §7.5.  Paper: packet
§8 (Prop. 8.1, Cor. 8.2), §12 (`MarkedRecip` row); draft §2 (eq. 2.1–2.3, Warning).
`docs/literature-axioms.md` AX3 (dyadic). -/
axiom markedRecipAt (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] : Dyadic.MarkedRecip localReciprocity K
```

Faithfulness class: **composite project interface** (Axioms.lean header taxonomy :55–59), with
clauses (i)–(iii) individually at "classical with encoding choices" strength.  The honest
deviations to flag in `docs/literature-axioms.md`: uniformizer spelled spectrally (B13 idiom);
unramifiedness spelled by the `HasEqualNormValueGroups` convention (isolated def); clause (a)
omitted; `λ`/`γ` derived rather than asserted.

### 2.4 Derived layer shipped with the bundle file (axiom-free, bundle-parametrized)

Following the B5 stress-test discipline (`GQ2/Reciprocity.lean:262–327` — everything below
takes `(B : MarkedRecip R K)`, so `#print axioms` = std-3):

* `surjective_nu_ur`, `surjective_lambda`, `exists_frobenius_lift` (§1.5 proofs);
* `CK := (chiCycKAb K).range`, `IK : Subgroup ℤ_[2]ˣ` (χ-image of `ker ν`; closed because the
  domain is compact under the threaded `[CompactSpace]`-style binders — same binder discipline
  as `DyadicOrientation`, `GQ2/Orientation.lean:73`), `lambda_welldef`, `I_eq_ker_lambda`;
* descents `chiTwoK`, `nuTwoK` to `D_K = maxProPQuotient 2 (GalK K)` via
  `isProP_two_unitsPadicInt` / `isProP_two_multPadicInt` (`GQ2/PropOneOne.lean:55`) — the
  MC5/boundary-facing forms;
* the `f`-relation stress test: for `FF : DyadicUnitFiltration K`,
  `∀ x, (R.nu_ur (inclAbK K (B.recip x))).toAdd = FF.f • (B.nu_ur (B.recip x)).toAdd`
  (derived from `norm_compat` + `R.nu_ur_recip` + `norm_val` of `GQ2/UnitNormIndex.lean`; then
  extended to all of `GalKab K` by density — this is the §1.2 verification, as a regression);
* the (r, ε, η) extraction API (§4) and the `CyclotomicFrobeniusDatum` bridge for F4.

---

## 3. The ℚ₂ compatibility clause (merge-gate-8-style regression)

Statement to prove in the derived layer, at `K = ⊥` (the bottom intermediate field):

```lean
theorem markedRecip_bot_reduces (B : MarkedRecip localReciprocity ⊥) :
    (∀ x : (↥(⊥ : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])))ˣ,
        inclAbK ⊥ (B.recip x) = localReciprocity.recip (botUnitsEquiv x)) ∧
    B.r = 0 ∧
    ∀ g : GalKab ⊥, B.nu_ur g = localReciprocity.nu_ur (inclAbK ⊥ g)
```

Proof route (all bundle-level, no new axiom): (i) `Algebra.norm ℚ_[2]` on the rank-1 `⊥` is
the canonical identification `botUnitsEquiv` (mathlib rank-one norm lemma; locate at
implementation time), so `norm_compat` *is* the first clause; (ii) `2 ∈ ⊥` satisfies the
uniformizer spec, so `B.nu_ur (B.recip 2̄) = ofAdd (−1)` while
`chiCycKAb ⊥ (B.recip 2̄) = chiCycAb (R.recip 2) = 1` (B5 clause (c)-uniformizer,
`GQ2/Reciprocity.lean:257`) — a `ker χ` element with unit ν-value, so `nu_ker_chi_le` forces
`(−1) = 2^r·y`, hence `B.r = 0`; (iii) ν-agreement: both sides are continuous homs agreeing on
the dense `rec`-image (`nu_ur_recip_*` versus `R.nu_ur_recip` through (i)), `inclAbK ⊥` being
the abelianized form of `fixingSubgroup ⊥ = ⊤`.  Step (iii) carries the plumbing burden
(⊥-transport + the instance-path caution of §1.1); if it stalls, the (i)+(ii) fragment is
already the substantive regression and (iii) can be a follow-up ticket.  `B.r = 0` is the
marked-data check that ℚ₂ is type `L` (`r = 0`, `I = C` — draft §2 type-L paragraph :271).

---

## 4. Consumers: binder forms and the (r, ε, η) extraction API

### 4.1 Interim hypothesis binders (pre-flip; the `BLabHypothesis` discipline, `GQ2/Roe/MarkedPro2.lean:141`)

The structure (not the axiom) is what consumers name; they all keep compiling unchanged after
the census flip, which merely provides the canonical instance.

* **F4** (`GQ2/Dyadic/Branches.lean`): data-level classification stays field-free on the
  abstract `CyclotomicFrobeniusDatum` (draft §10.2 :1310–1321).  Field-interpretation
  corollary (packet Prop 8.1 clause):

  ```lean
  theorem ki_unramified_of_eta_even (B : MarkedRecip localReciprocity K)
      (hα : 2 ≤ α) (hεη : lambdaOf B ((1 - 2^α)⁻¹-unit) hu ∈ evenSet) … :
      ∀ δi, δi ^ 2 = -1 → HasEqualNormValueGroups K δi
  ```

  and its contrapositive `eta_odd_of_ki_ramified` — the exhaustiveness input for the five-row
  branch datum ("the sign row does not exist").
* **MC5** (`GQ2/Dyadic/MarkedCore/Certificate.lean`): binds
  `(B : MarkedRecip localReciprocity K)` and states the marked-data equality hypothesis of
  packet Prop 7.2 against `B`'s derived `(CK, IK, lambdaOf, gamma)` transported through the
  hypothesized abstract iso (`MLabHypothesis`/`NLabHypothesis` binders), targeting
  `correction_nu` in the ledger §5.1 field list.  The ν it transports is the descended
  `nuTwoK B` on `D_K`.
* **B1 boundary lane** (future `GQ2/Dyadic/…` boundary file): binds
  `(B : MarkedRecip localReciprocity K)` and AX4's tame bundle *parametrized by `B`* —
  recommend AX4 adopt `structure OrientedTameQuotientK (B : MarkedRecip R K)` whose `ν_t`
  clauses are pinned against `B.recip` on units/uniformizers, exactly the B10′ pattern
  (`GQ2/TameQuotient.lean:99–108`); that is the "pairs with AX3 normalization" seam of plan §4.
  Then packet Prop 3.4(3)/Thm 3.5 hypotheses are equalities between `B`'s and the tame
  bundle's characters through the two quotients.
* **AS5**: the final theorem's "identifies … the full geometric unramified character" clause
  is stated as `ν`-compatibility against `(markedRecipAt K).nu_ur` (post-flip).

### 4.2 The (r, ε, η) extraction functions (derived layer; consumed by F4's branch rows)

```lean
variable (B : MarkedRecip R K)

/-- λ on a cyclotomic class: choice of preimage + `lambda_welldef` (§1.5). -/
noncomputable def lambdaOf (c : ℤ_[2]ˣ) (hc : c ∈ (chiCycKAb K).range) : ZMod (2 ^ B.r)
theorem lambdaOf_spec (g) (hg : chiCycKAb K g = c) :
    lambdaOf B c hc = PadicInt.toZModPow B.r (B.nu_ur g).toAdd
theorem lambdaOf_mul …    -- hom property on `CK`
theorem lambdaOf_eq_zero_iff_mem_I …

/-- ε ∈ ZMod 2, defined for r ≥ 1 by `λ(−1) = ε · 2^(r−1)` (packet §8 :771). -/
noncomputable def epsilonOf (hr : 1 ≤ B.r) (h₁ : (-1 : ℤ_[2]ˣ) ∈ (chiCycKAb K).range) : ZMod 2

/-- η for the `M_α` rows: `η = λ(u)`, `u = (1 − 2^α)⁻¹ ∈ 1 + 4ℤ₂` (packet §8 :765–772). -/
noncomputable def etaM (α : ℕ) (hα : 2 ≤ α) (hu : uUnit α ∈ (chiCycKAb K).range) : ZMod (2 ^ B.r)

/-- η for the `N_α` procyclic rows: `η = λ(v)`, `v = −(1 + 2^α)⁻¹` (draft §2, type-N
paragraph :331–335 — the dispatch's "draft §2.3 variant"). -/
noncomputable def etaN (α : ℕ) (hα : 2 ≤ α) (hv : vUnit α ∈ (chiCycKAb K).range) : ZMod (2 ^ B.r)

/-- Frobenius coset: any `g` with `(B.nu_ur g).toAdd = 1` represents `γ`; well-defined mod `I`,
`λ γ = 1`. -/
theorem gamma_welldef … ; theorem lambda_gamma …
```

Bridge to F4's abstract datum: `def toCyclotomicFrobeniusDatum (B) : CyclotomicFrobeniusDatum
↥(chiCycKAb K).range` with `lambda := Multiplicative.ofAdd ∘ lambdaOf B` packaged as a
`→* Multiplicative (ZMod (2^B.r))` hom, `lambda_surjective := surjective_lambda`; F4's
`inertiaImage`/`gammaCoset` then agree with `IK`/`gamma` by `I_eq_ker_lambda`/`gamma_welldef`.
The membership hypotheses (`−1 ∈ C`, `u ∈ C`) are exactly the branch hypotheses F4's rows carry
(M-rows have `−1 ∈ C` by type; instances discharge them by the §5 computations).

Value pipeline used by instances (record once; this is the sign-bearing formula):

> `λ(unit-part(N_{K/ℚ₂} x)) = + v_K(x) mod 2^r`, obtained from
> `λ(χ(rec x)) = ν(rec x) = −v_K(x)` and `χ(rec x) = unit-part(N x)^{-1}` — the two inversions
> cancel.  (Risk register R2.)

---

## 5. Worked instances: the five quadratic test vectors

Ramified-`i` quadratic fields `K = ℚ₂(√d)`, `d ∈ {−2, 2, 5, 10, −10}` (F5's list;
`d = −1, −5` are unramified-`i`).  Draft/packet anchors: √−2 draft §7.1 :1039 (`I = C = ⟨3⟩`,
`r = 0`); √2/√5 §7.2 :1058 (compact `M₃`/`M₂`); √10 §7.3 :1075 (marking `ν(a,b,c,d) =
(−4,0,2,1)`, inertia image `{±1}(1+8ℤ₂)`); √−10 packet Cor 8.2 :801 (`(r,ε,η) = (1,1,1)`,
`u = (−3)⁻¹ ≡ 5 (mod 8)`).  The following (C, I, λ, γ) data are what the eventual
implementation must reproduce; each line was recomputed for this memo via the §4.2 norm
pipeline (`C` = inverted unit parts of `N(Kˣ)`-closure; `I` ⊇ unit-norms and squares; negative
memberships via λ-values; symbols via the B7′ formula).

| `K` | type | `q_K` | `C` | `I` | `r` | `ε` | `η` | `γ` | key norm witnesses |
|---|---|---|---|---|---|---|---|---|---|
| `ℚ₂(√−2)` | `N₂` compact | 2 | `⟨3⟩ = ⟨−5⟩` (classes `{1,3} mod 8`; torsion-free, `−1 ∉ C`) | `= C` | 0 | — | — | trivial | `N(1+√−2) = 3`; `N(√−2) = 2` (unit part 1, `v` odd ⇒ `r = 0`) |
| `ℚ₂(√2)` | `M₃` compact | 2 | `{±1}(1+8ℤ₂)` (`= ⟨−1⟩×⟨(1−8)⁻¹⟩`) | `= C` | 0 | — | — | trivial | `N(1+√2) = −1`; `N(2+√2) = 2` ⇒ `r = 0` |
| `ℚ₂(√5)` | `M₂` compact | **4** | `ℤ₂ˣ = {±1}(1+4ℤ₂)` | `= C` | 0 | — | — | trivial | unramified field: `N(O_Kˣ) = ℤ₂ˣ` (B11b, `GQ2/Foundations/Interfaces.lean:217`); the only `f = 2` row — exercises AX4 at `q_K = 4` |
| `ℚ₂(√10)` | `M₂` procyclic | 2 | `ℤ₂ˣ` | `{±1}(1+8ℤ₂)` | 1 | **0** | 1 | `5·I` | `N(3+√10) = −1` (unit! ⇒ `−1 ∈ I`, `ε = 0`); `N(√10) = −10` ⇒ `λ(−5) = 1`; `λ(5) = λ(−5)+λ(−1) = 1 = η` |
| `ℚ₂(√−10)` | `M₂` procyclic | 2 | `ℤ₂ˣ` | classes `{1,3} mod 8` | 1 | **1** | 1 | `−1·I = 5·I` | `N(1+√−10) = 11 ∈ I`; `−5 = N(unit)` (Hilbert `(−10,−5)₂ = 1` at `v = 0`) ⇒ `−5 ∈ I`; `N(x) = −2` solvable (`(−10,−2)₂ = 1`) at `v` odd ⇒ `λ(−1) = 1 = ε`; `η = λ(u) = λ(5) = λ(−1)+λ(−5) = 1` |

Cross-checks: (i) √10 vs √−10 differ **only in ε** — this is the draft Warning's "same abstract
type `M₂`, different marked Frobenius systems", and matches the draft's √10 coordinates
(`x₁ = b` with no `σ^{ε·2^{r−1}}` factor ⇔ `ε = 0`, :1083 against :288) and packet Cor 8.2's
`ε = 1` for √−10.  (ii) `η` odd in both procyclic rows ⇔ ramified-`i` (Prop 8.1) ✓.
(iii) √−2's `C = ⟨−(1+2²)⟩` matches the `N_α` image shape at `α = 2` (`−5 ≡ 3 mod 8`).
(iv) `1+8ℤ₂ ⊆ I` in every row (squares are norms, §1.5) ✓.  (v) ℚ₂ itself: `r = 0`, `I = C =
ℤ₂ˣ` (type `L`) — the §3 regression.  Suggested implementation home for the table: the F5
python harness gets mod-16 × mod-4 closed-subgroup pins, and the Lean instances (AS3) prove
the `r/ε/η` rows via the §4.2 API; the memo's witnesses above are the exact elements to use.

Caveat for the implementer: no quadratic field exercises `r ≥ 2` or the `N`-procyclic row —
see risk R2/R3 for the synthetic tests that must cover those.

---

## 6. Census plan

**Count: exactly one new axiom** (`markedRecipAt`), census 9 → 10 on branch `dyadic` (master
stays at 9; the flip commit happens on `dyadic` only).  No second axiom is warranted: the
plain-reciprocity vs marked-pack split (two axioms) buys cleaner per-clause faithfulness labels
but breaks the B5/B10′ house pattern of one bundle per interface and doubles the ledger
surface; the docstring's per-clause classification (§2.3) achieves the same review
granularity.  **Owner question Q1** if the split is preferred anyway.

Replace-vs-extend analysis:

* **B5** (`localReciprocity`, `GQ2/Foundations/Axioms.lean:171`): **extend, do not replace.**
  A b9a-style subsumption (state only the general-K axiom, re-derive B5 at `K = ⊥` under the
  old name) is *technically* available via §3, but the ⊥-transport (bot-equiv on units, `⊤`
  fixing subgroup, abelianization transport, instance-path pinning) is a real plumbing project
  whose failure modes are exactly the silent-normalization kind; and B5 would still be needed
  as the `R`-parameter of the new bundle's `norm_compat` unless the clause is re-anchored,
  which would change B5's 17-consumer surface.  Not recommended; the §3 regression delivers
  the same audit value.  (**Q6**)
* **B3c** (`dyadicOrientation`, :158): **untouched, not extended by AX3.**  Its general-K
  content decomposes as: cyclotomic character = derivable restriction (§1.1); presentation-side
  `χ_P` values = MC2 definitions; abstract Demushkin iso = G-Lab hypothesis (never an axiom by
  default, plan A3).  AX3 supplies only what B3c's *cyclotomic interface* supplied at ℚ₂, in
  marked-quotient form — the plan §4 row's "extends B5, B3c" should be read that way.
* **B10** (`tameQuotient`, :325): **untouched**; the general-K oriented tame quotient is AX4,
  whose bundle should be parametrized by this ticket's `MarkedRecip` (§4.1, B1 bullet).  Note
  `W_K = W_{ℚ₂} ∩ G_K` is true but useless here — B10 gives no handle on the intersection's
  quotient presentation at `q_K`; AX4 remains a genuine Iwasawa-at-K axiom.

Census-flip checklist, instantiated from the b9a template
(`docs/orchestration/b9a-tickets.md:27–45`):

1. Land `GQ2/Dyadic/MarkedRecipBundle.lean` (structure §2.2 + derived layer §2.4 + §3
   regression + §5 instance lemmas as they arrive) — axiom-free, `module`-style, `lake env
   lean` green.  Ownership: F4's scope or a small new ticket AX3-b (**Q5**); `GQ2.lean` import
   line is orchestrator-owned (board 2026-07-29 protocol (a)).
2. Owner **G-AX** sign-off on this memo's §2.3 statement, the Q1–Q7 answers, and PDF
   verification of the Serre XI §3 / NSW functoriality numbers (Q7) — the house "verified
   against the cited PDFs" line must not be written before that check.
3. Single atomic census commit on `dyadic`: the axiom into `GQ2/Foundations/Axioms.lean` (+
   `public import GQ2.Dyadic.MarkedRecipBundle`; header census list 9 → 10 with an AX3/B5-K
   row); `scripts/check_axioms.sh` `EXPECTED_AXIOMS` bump; `docs/literature-axioms.md` new row
   (label: propose **B5-K**, alias AX3, to keep the B-taxonomy); `formalization.yaml` axiom
   list; `GQ2/AxiomLedger.lean` row; check whether `Challenge.lean`/`comparator-config.json`
   pin the axiom-name list (they did at b9a T5) and update.
4. Gates before merge to `dyadic`: full build green; `check_axioms.sh` passes (count exact);
   audited ℚ₂ capstones print byte-identical axiom sets (check 5 — the new axiom must not leak
   into any ℚ₂ capstone); zero sorries outside allowlist; consumers that pre-bound the
   structure keep compiling unchanged.
5. Docs sweep (literature-axioms cross-refs; this memo gains a "landed as" postscript).

---

## 7. Risk register — where a wrong normalization silently poisons downstream

* **R1 (geometric vs arithmetic Frobenius, the double convention).**  `rec` arithmetic + `ν`
  geometric is the B5 house pair (`GQ2/Reciprocity.lean:49–66`); the tame side additionally has
  `σ = geometric` with NSW's relation under `σ ↦ σ⁻¹` (`GQ2/TameQuotient.lean:33–47,86–87`).
  A `+1` where `−1` belongs in `nu_ur_recip_uniformizer` flips `γ` and every odd λ-value.
  Guards: the §3 regression (agrees with B5's `nu_ur_recip_uniformizer = ofAdd(−1)` stress,
  :281); AX4 must pin its `ν_t` against *this* bundle's `recip`, never independently.
* **R2 (the double inversion in the λ pipeline).**  `χ(rec x) = unit-part(N x)^{-1}` and
  `ν(rec x) = −v_K(x)` cancel to `λ(unit-part(N x)) = +v_K(x) mod 2^r` (§4.2).  **Every
  quadratic instance has `r ≤ 1`, where signs mod `2^r` are invisible** — worse, a global
  ν-sign flip changes `(ε, η)` mod 2 not at all (`2^{r−1} ≡ −2^{r−1}`, `η` odd ⇔ `−η` odd).
  Mandatory guard: a **synthetic `r = 2` mock bundle** stress test (hand-built `MarkedRecip`
  over an abstract group with prescribed `(χ, ν)`) checking `lambdaOf`/`epsilonOf`/`etaM`
  against hand values, signs included.  No field instance will catch this class of error.
* **R3 (λ additive vs multiplicative; draft §10.2's `Multiplicative (ZMod (2^r))`).**  F4's
  `CyclotomicFrobeniusDatum` target is `Multiplicative (ZMod (2^r))` (draft :1313) while the
  branch equations `λ(−1) = ε·2^{r−1}`, `λ(u) = η` are additive.  Fix one bridge
  (`toCyclotomicFrobeniusDatum`, §4.2) and state all extraction specs additively via `toAdd`;
  never mix `ofAdd`-values into the branch rows directly.
* **R4 (nat subtraction at `r = 0`).**  `ε·2^{r−1}` is garbage at `r = 0` (`0 − 1 = 0` in ℕ ⇒
  `2^{r−1} = 1`); `ZMod (2^0) = ZMod 1` collapses everything.  `epsilonOf`/`etaM`/`etaN` carry
  `(hr : 1 ≤ B.r)`; compact rows (`r = 0`) must never call them (their branch data is the
  `r = 0` fact itself).
* **R5 (discrete-target inconsistency).**  Inherited B5 trap (`GQ2/Reciprocity.lean:75–79`):
  any future refactor replacing `Multiplicative ℤ_[2]` by `ℤ` or `Multiplicative ℤ` makes the
  axiom false (compact source, discrete infinite target).  Same for a hypothetical `Ẑ`-valued
  "full unramified character" — the *2-primary* ℤ₂-coordinate is the sound choice and is what
  the packet consumes (merge gate 7.6 "full ℤ₂-valued", not Ẑ-valued).
* **R6 (instance-path trap).**  `Kummer.GaloisGroup ℚ₂` vs `AbsGalQ2` carry different `Group`
  instances (`GQ2/Reciprocity.lean:166–171`); `chiCycK`/`inclAbK` must pin domains once, or
  every downstream `simp`/`ext` fights defeq.  Cost is plumbing, not soundness — but a wrong
  fix (a second, rival abelianization) *would* be a soundness-adjacent fork; reuse
  `commClosure`-style definitions verbatim.
* **R7 (import cycle for the `K(i)` clause).**  `HasEqualNormValueGroups` lives in
  `GQ2/Foundations/Interfaces.lean:109`, which imports `Axioms.lean` — the bundle file (which
  `Axioms.lean` must import at flip time) cannot import it.  Options: (i) move the `def` (+
  deprecated alias) into a statement-layer file — one-line A6-frozen-file edit, orchestrator
  approval needed; (ii) inline an identical ∀-statement in the clause (byte-duplication,
  zero-touch).  Recommend (i).  **Owner question Q3.**
* **R8 (vacuous clauses).**  `nu_ur_recip_uniformizer` quantifies over a spectral-norm spec;
  if mis-stated (e.g. requiring a bundled filtration nobody instantiates) it is vacuously true
  and the bundle silently loses its Frobenius pin.  Guard: the derived `surjective_nu_ur` and
  the §3 `B.r = 0` computation both *fail to prove* if the clause is vacuous at ℚ₂ — keep both
  in the bundle file's test section from day one.
* **R9 (module-system).**  The bundle file must remain importable by the `module`-style
  `Axioms.lean` and must not (transitively) import the plain-import §8/§9 stack (R31a rule,
  plan A5).  `MarkedRecipBundle` as specified imports only statement-layer files — keep it so;
  MC5/boundary consumers, which do sit above the stack, import the bundle, never vice versa.

---

## 8. Open questions for the owner (G-AX gate)

* **Q1** One axiom (recommended, §6) or split plain-reciprocity / marked-pack into two?
* **Q2** Confirm omission of the finite-layer norm-residue clause (a_K) (§1.3).  If any lane
  is expected to need `Gal(L/K) ≅ Kˣ/N(Lˣ)` (e.g. a future K-side unit-index count), say so
  now — adding the field later is a statement change under G-AX rules.
* **Q3** `HasEqualNormValueGroups` import cycle: move the def (one-line edit to the frozen
  Interfaces file, alias kept) vs inline duplication (§7 R7).
* **Q4** Hypothesis spelling of "K(i)/K ramified" in the final theorem (AS5): field-language
  `¬ HasEqualNormValueGroups` (instances discharge by explicit norm-value mismatch, pattern
  `not_hasEqualNormValueGroups_sqrt_two`) vs marked-data `¬(I ≤ 1+4ℤ₂)` (self-contained, ties
  to the classical statement only through the documented bridge).  The AX3 clause set supports
  both; the packet's headline reads better with the former.
* **Q5** Ownership of `GQ2/Dyadic/MarkedRecipBundle.lean`: extend F4's file list or open a
  small ticket AX3-b (statement + derived layer + §3 regression + R2's synthetic `r = 2`
  test).  It blocks MC5's and F4's binder spelling, so it should land early in wave 1.
* **Q6** Confirm extend-not-replace for B5 (no ⊥-subsumption), §6.
* **Q7** PDF verification at sign-off: exact proposition numbers for Serre LF Ch. XI §3
  (norm functoriality of the reciprocity map) and the NSW Ch. I §5 / Ch. VII §7.1 functoriality
  statement; also the mathlib name for the rank-one `Algebra.norm` identification used in §3(i).
  This memo deliberately does not claim "verified against the cited PDFs".

---

**Postscript (orchestrator, 2026-07-29): LANDED.** Owner sign-off at gate G-AX (answers Q1–Q7
recorded on the board): one axiom; a_K clause omitted; def moved with alias; field-language
spelling for AS5; bundle file via ticket AX3-b (`GQ2/Dyadic/MarkedRecipBundle.lean`, merged);
extend-not-replace for B5 confirmed; citation targets approved with **PDF verification
pending** (UNVERIFIED annotations retained). Census flip 9 → 10 committed as **B5-K**
`GQ2.markedRecipAt` in `GQ2/Foundations/Axioms.lean`; ledger/probe/yaml/comparator rows
updated; ℚ₂ capstone prints unchanged (check-5 frozen census).
