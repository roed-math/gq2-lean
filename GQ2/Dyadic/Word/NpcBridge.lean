/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.NpcJet.Handles
import GQ2.Dyadic.Certificates.Mpc

/-!
# The `NpcJet` ↔ `WordCoh` bridge (ticket WW6)

The NC lane (`GQ2/Dyadic/NpcJet/`) proved its centrepiece — `npc_cross_operators`, the
S3.2-corrected cross-operator identity — inside the **non-`module`** central extension
`GQ2.WordCoh2.CentExt` of `GQ2.SectionEight.AffineTLift.Sd C V`, against the cocycle
`GQ2.SectionEight.AffineTLift.kappa0Cocycle`.  The dyadic `Word/` layer (MC-OB's
`Word/WordCoh.lean`, WW4's `Word/Hessian.lean`) works inside the **`module`** extension
`GQ2.Dyadic.WordCoh.CentExt` of `GQ2.SectionSix.SemiProd C V`, against
`GQ2.Dyadic.kappa0Cocycle`.  Three independent reports (WMP-c, WNP-c, WWH) recorded that these
are *the same mathematics on different carriers* and that nothing connected them; WW4's
`HessRelZTarget` and CB-5M sit behind that gap.

This file is the connection, as a **plain-import leaf above both sides** (the module rule: a
plain file may import a `module` file, not conversely, so a leaf importing `NpcJet/*` **and**
`Word/Hessian.lean` must itself be plain).  Nothing above is edited; nothing here is a `sorry`
and no axiom beyond the standard three is used.

## Contents

* **§1 the base carriers** — `sdEquiv : Sd C V ≃* SemiProd C V`.  Both are `def`s for `V × C`
  with the same product `(v,c)(w,d) = (v + c·w, cd)`, so the identification is the identity
  function and every component reading is `rfl`.
* **§2 the cocycles** — `ofWordCoh2`/`toWordCoh2`, the `WordCoh2 ↔ WordCoh` `TwoCocycle`
  translation (the exact analogue of MC-OB's ratified `ofDRCoh`/`toDRCoh`), and the theorem
  that pins the two `κ⁰`s to one another: `ofWordCoh2_kappa0Cocycle` says the NC lane's cocycle
  **is** the `Word/` cocycle pulled back along `sdEquiv`.
* **§3 the extension carriers** — `centExtEquiv`, a `MulEquiv` of the two `CentExt`s that is the
  identity on the underlying `(V × C) × 𝔽₂`; in particular it **preserves the fibre on the
  nose** (`centExtEquiv_fib`, `rfl`), which is what makes every jet value transportable.
  `centExtHom` is its `ContinuousMonoidHom` packaging, for `Marking.eval` naturality.
* **§4 the slice calculus** — `centExtEquiv` carries `NpcJet.elt`/`sliceElt`/`cLine` to
  `hessElt`/`hessSlice`/`hessLine`, and WWH's measurement is discharged as theorems in both
  directions: the five laws that exist on both sides are proved to be images of one another,
  and the **six laws the `Word/` side lacks** (`cLine_inv`, `sliceElt_mul_cLine`,
  `cLine_mul_sliceElt`, `sliceElt_conj`, `sliceElt_sq` and NC2's `y^k` power law) are supplied
  on the `Word/` carrier by transport.
* **§5 the marking** — the NC lane's Gate-E marking `npcMarking` pushes to `npcMarkingW`, and
  `npcMarkingW_eq_lift` identifies **that** with `WordCoh.lift` of WN0-b's already-existing
  graph marking `GQ2.Dyadic.Certificates.hessMark` at `(c₀, c₁, 0)`.  So the two lanes were
  evaluating at literally the same marking all along, one carrier apart.
* **§6 the centrepiece transported** — `npc_cross_operators_word`,
  `npc_cross_operators_handles_std_word`, the hash-pinned form
  `npc_cross_operators_npcW_word` (the shape `Certificates/Npc.lean` actually cites) and the
  `hessRelZ` forms `hessRelZ_npcWord`/`npcW_hessRelZTarget`: the NC identity in `Word/`
  vocabulary (`WordCoh.CentExt`, `hessSlice`, `hessLine`, `hessRelZ`), with no `WordCoh2` name
  anywhere in the statement.  `hVu_of_simple` needs no transport — it is a statement about the
  `C`-module `V` alone and was already carrier-free; `hVu_of_simple_restated` records that.
* **§7 `HessRelZTarget`** — WW4 gap item 5.  `npc_hessRelZTarget` **discharges** the target on
  the procyclic-`N` row, which is the proof that the target's shape is right; and
  `mpcHessRelZTarget` states it, fully instantiated, on the procyclic-`M` row.  See the caveat
  below: the bridge makes the `M` statement *nameable*, but it is not what proves it.

## What the bridge does and does not buy for WMP-c's successor

The gap WMP-c recorded had two components, and they are not the same size.

1. **The carrier gap** — "`npc_cross_operators` exists `WordCoh2`-typed" (WNP-c), "unmergeable
   while `NpcJet` is plain-import and `Word/` is module-style" (WWH).  This file **closes** it:
   §3–§6 move every NC-lane value into `Word/` vocabulary, and §7 shows the target type is
   inhabited by exhibiting a proof of it on the `N` row.

2. **The missing `M`-row jet theorem.**  `HessRelZTarget` for the procyclic-`M` row needs
   `hessRelZ (hessMark …) … (mpcW α r p η 0) = plusFormD d₀ q (c₀, c₁)` — the
   `npc_cross_operators` *analogue for `mpcW`*.  No such theorem exists anywhere: the NC lane
   proved the identity for `npcWord`, and `Certificates/Mpc.lean` never evaluates `mpcW` at a
   graph-type κ⁰-marking at all (its only `Marking.eval` of `mpcW`, `eval_sqrtNeg10_factored`,
   is a value-level factorization).  **The bridge does not supply that, and cannot**: it is a
   transport, and there is nothing on the `M` row to transport.

So the honest statement of the residue is: item 5 was blocked on *two* things, the bridge and an
`M`-row jet computation; the bridge is now landed and the jet computation is what remains.  What
the successor gains concretely is listed at `mpcHessRelZTarget`.

## The de-duplication WWH recorded: costed, not performed

WWH's finding was that after its hoist the NC lane's slice kit is *the second copy* of the
`hessSlice`/`hessLine` calculus, and that "de-duplicating them is not a `module`-file job".  With
the bridge landed, here is the costing.  **The retirement is possible** — and this file
deliberately does not do it: `NpcJet/*` is closed and heavily consumed.

*No module-rule obstruction.*  `NpcJet/Defs.lean` is plain and already imports the `module` file
`GQ2.Dyadic.Word.Eval`, so it may equally import `GQ2.Dyadic.Word.Hessian`; and `Word/Hessian`'s
own imports (`Phase`, `Stokes`, `WordCoh`, `SectionSix`, `OrbitData`) are all `module` and none
reaches `NpcJet`, so there is no cycle.  WWH's "unmergeable while `NpcJet` is plain-import"
reading is one direction too strong: what the module rule forbids is `Word/Hessian` importing
`NpcJet`, not the converse.

*The internal cost is the whole lane.*  The kit is used at **111 occurrences of `sliceElt` and
41 of `cLine`** inside `NpcJet/`, plus `elt` and NC2 §3's power law; retiring it means retyping
all of `NpcJet/{Defs,Omega,Seams,Main,Handles}` onto `WordCoh.CentExt (kappa0Cocycle dat hdat)`.
Six statements would first have to be added to the `Word/` kit — `hessLine_inv`,
`hessSlice_mul_hessLine`, `hessLine_mul_hessSlice`, `hessSlice_conj_hessLine`,
`hessSlice_sq_of_npc`, `hessElt_pow`/`_eq_hessSlice`/`orderOf_hessElt_dvd_two_mul` — because the
`Word/` copy is strictly *smaller* than the NC one.  §4 below already supplies exactly those,
so that part of the cost is now paid.

*The external cost is five lines.*  The certificate layer never touches the NC carrier: `CentExt`
and `kappa0Cocycle` occur **zero** times in `Certificates/NpcFox.lean` and
`Certificates/Npc.lean`.  The entire external surface is the five `npcMarking …|>.eval …|>.fib`
spellings at `NpcFox.lean:1752` and `Npc.lean:1101, 1116, 1132, 1254` — and §5–§6 below give the
`Word/`-carrier replacement for each.

*Recommendation.*  Not now, and not as a lane-wide retype.  The bridge makes the second copy
cheap to live with (every law is one `rw` from the other lane's), whereas the retype touches a
closed, audited lane for no new mathematics.  The moment to do it is if `NpcJet` is reopened for
other reasons.

## A resolver gap, noted in passing

`hessRelZ_npcWord` carries a `PWord.ResolvedAt` hypothesis and the compact rows do not.  That is
not a weakness of the bridge: `npcWord` has an `η̂`-exponent node (`PWord.etaPow` is a `profPow`
at `etaHatZ η`, not at `ω₂`), so it is not `ω₂`-only and F2's hypothesis-free bridges
(`eval_eq_evalFin`, `eval_eq_evalNat_exponent`) do not apply.  What *would* remove the hypothesis
is a general `Zhat`-resolver lemma — the non-`ω₂` analogue of `PWord.zpowHat_omega2_zpow`,
i.e. "in a finite group, every `γ : Zhat` acts as a single integer power valid at all elements
simultaneously".  The repo has the per-element formula (`zpowHat_etaHatZ`) but no such uniform
statement and no `Zhat → ZMod N` reduction.  The profinite form `npc_cross_operators_word` is
unconditional, so nothing is blocked; and the procyclic-`M` row is `ω₂`-only at an `ω₂`-only
`η`-display (`mpc_eval_eq_hessRelZ`), so its target will not need one.

## Axiom prints (recorded at commit time)

`#print axioms` gives **the standard three** (`propext`, `Classical.choice`, `Quot.sound`) or a
strict subset of them, for every one of the 67 declarations — measured, not asserted, on the
built module.  Headlines checked: `sdEquiv`, `finiteSemiProd`, `ofWordCoh2`,
`kappa0Cocycle_κ_sdEquiv`, `ofWordCoh2_kappa0Cocycle`, `centExtEquiv`, `centExtEquiv_fib`,
`centExtHom`, `hessElt`, `centExtEquiv_sliceElt`, `centExtEquiv_cLine`, `hessSlice_mul_of_npc`,
`sliceElt_mul_of_hess`, `hessSlice_commR_of_npc`, `sliceElt_comm_of_hess`, `hessLine_inv`,
`hessSlice_mul_hessLine`, `hessLine_mul_hessSlice`, `hessSlice_conj_hessLine`,
`hessSlice_sq_of_npc`, `hessElt_pow`, `hessElt_pow_eq_hessSlice`, `orderOf_hessElt_dvd_two_mul`,
`map_npcMarking`, `map_npcMarkingH`, `npcMarkingW_eq_lift`, `npcMarkingHW_zero`,
`npc_cross_operators_word`, `npc_cross_operators_handles_std_word`,
`npc_cross_operators_npcW_word`, `hVu_of_simple_restated`, `hessRelZ_npcWord`,
`npc_hessRelZTarget`, `npcW_hessRelZTarget`, `mpcHessRelZTarget`, `mpcHessRelZTarget_iff`,
`mpc_eval_eq_hessRelZ`.  Two print a proper subset: `sdEquiv` is `[propext]` and
`hVu_of_simple_restated` is `[propext, Quot.sound]`.

No sorries, no new axioms, **no `decide` at all**, and none of the nine obligations is touched.

## Module rule, and the consumer it locks out

Verified before writing: `GQ2/Dyadic/NpcJet/*.lean` are plain (they import
`GQ2.GaussZ.RelatorGammaA`, plain), `GQ2/Dyadic/Word/{WordCoh,Hessian,Eval,Phase,Stokes}.lean`
are `module`, and `GQ2/Dyadic/{Words,Certificates}/*.lean` are plain (the WN0-a ruling).  A
plain file may import both kinds, so this leaf is plain — and therefore **no `module` file can
import it**.  Concretely: `GQ2/Dyadic/Word/Export.lean` and any future `module` file under
`Word/` cannot see anything below.  Every actual consumer of this bridge —
`Certificates/Mpc.lean`, `Certificates/Npc.lean`, `Certificates/N0.lean`, `CertificateMain.lean`
— is plain, so nothing that needs it is locked out today.

The file lives under `Word/` because that is where its `Word/`-side vocabulary lives, but it is
the one plain file in that directory.  It is **not** registered in `GQ2.lean` (WW6 owns only
this file); build it with `lake build GQ2.Dyadic.Word.NpcBridge`.
-/

namespace GQ2.Dyadic.NpcBridge

open GQ2.SectionSix GQ2.QuadraticFp2

/-! ## §1. The base carriers

`GQ2.SectionEight.AffineTLift.Sd C V` (non-`module`) and `GQ2.SectionSix.SemiProd C V`
(`module`) are two `def`s for `V × C` carrying the same semidirect product
`(v,c)·(w,d) = (v + c·w, cd)`.  WW4's `Word/Hessian.lean` docstring records this as
"definitionally equal group laws"; here it is a `MulEquiv`, so it can be transported along. -/

section Base

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- **The base-carrier correspondence**: the NC lane's semidirect carrier `Sd C V` and the
`Word/` layer's `SemiProd C V` are the same group, by the identity function.  Every field is
`rfl`: both types unfold to `V × C`, and both products are the literal lambda
`fun p q ↦ (p.1 + p.2 • q.1, p.2 * q.2)` (`Sd`'s `Group` instance gives it directly; `SemiProd`
takes it from its `Mul` instance through `Group.ofLeftAxioms`). -/
def sdEquiv : SectionEight.AffineTLift.Sd C V ≃* SemiProd C V where
  toFun p := p
  invFun p := p
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem sdEquiv_fst (p : SectionEight.AffineTLift.Sd C V) :
    (sdEquiv p).1 = p.v := rfl

@[simp] theorem sdEquiv_snd (p : SectionEight.AffineTLift.Sd C V) :
    (sdEquiv p).2 = p.cc := rfl

@[simp] theorem sdEquiv_mk (v : V) (c : C) :
    sdEquiv (SectionEight.AffineTLift.Sd.mk v c) = ((v, c) : SemiProd C V) := rfl

@[simp] theorem sdEquiv_symm_apply (p : SemiProd C V) :
    sdEquiv.symm p = SectionEight.AffineTLift.Sd.mk p.1 p.2 := rfl

/-- Finiteness of the `module`-side carrier.  `GQ2/SectionSix.lean` declares the topology and
the discreteness of `SemiProd` but not its finiteness, and `Certificates/N0.lean` works around
that with a file-`local instance`; a `local` instance cannot be consumed downstream, and the
`Marking.eval` statements of §6 need this one in their *statements*, so it is exported here. -/
instance finiteSemiProd [Finite C] [Finite V] : Finite (SemiProd C V) :=
  inferInstanceAs (Finite (V × C))

end Base

/-! ## §2. The 2-cocycles

`GQ2.WordCoh2.TwoCocycle` (non-`module`) and `GQ2.Dyadic.WordCoh.TwoCocycle` (`module`) are
field-for-field identical structures — MC-OB's `Word/WordCoh.lean` says so in its
`## Deduplication` note and already ships the same translation for the third copy
(`ofDRCoh`/`toDRCoh`).  This section is that translation for the `WordCoh2` copy, plus the
theorem the NC lane actually needs: its `κ⁰` is the `Word/` `κ⁰` pulled back along `sdEquiv`. -/

section Cocycle

variable {L : Type} [Group L]

/-- Read a `GQ2.WordCoh2` 2-cocycle as a dyadic-`WordCoh` one.  Dedup twin: `WordCoh.ofDRCoh`. -/
def ofWordCoh2 (c : WordCoh2.TwoCocycle L) : WordCoh.TwoCocycle L := ⟨c.κ, c.norm, c.cocyc⟩

/-- Read a dyadic-`WordCoh` 2-cocycle as a `GQ2.WordCoh2` one. -/
def toWordCoh2 (c : WordCoh.TwoCocycle L) : WordCoh2.TwoCocycle L := ⟨c.κ, c.norm, c.cocyc⟩

@[simp] theorem ofWordCoh2_κ (c : WordCoh2.TwoCocycle L) : (ofWordCoh2 c).κ = c.κ := rfl

@[simp] theorem toWordCoh2_κ (c : WordCoh.TwoCocycle L) : (toWordCoh2 c).κ = c.κ := rfl

@[simp] theorem ofWordCoh2_toWordCoh2 (c : WordCoh.TwoCocycle L) :
    ofWordCoh2 (toWordCoh2 c) = c := rfl

@[simp] theorem toWordCoh2_ofWordCoh2 (c : WordCoh2.TwoCocycle L) :
    toWordCoh2 (ofWordCoh2 c) = c := rfl

end Cocycle

section Kappa0

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The two `κ⁰`s agree pointwise along `sdEquiv`.**  Both are `GQ2.kappa0` of the same
datum — `GQ2/OrbitData.lean` is `module`-style and is imported by both lanes — read through
`Sd.v`/`Sd.cc` on one side and `Prod.fst`/`Prod.snd` on the other. -/
theorem kappa0Cocycle_κ_sdEquiv (p r : SectionEight.AffineTLift.Sd C V) :
    (SectionEight.AffineTLift.kappa0Cocycle dat hdat).κ p r
      = (kappa0Cocycle dat hdat).κ (sdEquiv p) (sdEquiv r) := rfl

/-- **The cocycle correspondence.**  The NC lane's `κ⁰` *is* WW4's `κ⁰` pulled back along the
base-carrier identification — the statement that makes the two central extensions of §3
isomorphic rather than merely similar. -/
theorem ofWordCoh2_kappa0Cocycle :
    ofWordCoh2 (SectionEight.AffineTLift.kappa0Cocycle dat hdat)
      = (kappa0Cocycle dat hdat).comap (sdEquiv : SectionEight.AffineTLift.Sd C V ≃* _) :=
  WordCoh.TwoCocycle.ext' rfl

end Kappa0

/-! ## §3. The extension carriers

The two `CentExt` definitions are byte-identical (`def CentExt (_c) : Type _ := L × ZMod 2`
with the same `Group` instance), so once §1 and §2 identify the base and the cocycle the two
extensions are the same group by the identity function.  What matters downstream is
`centExtEquiv_fib`: the identification preserves the fibre coordinate **on the nose**, so any
jet value proved on one side is the same element of `𝔽₂` on the other. -/

section Extension

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The carrier correspondence** for the `κ⁰`-extensions: the NC lane's evaluation group and
the `Word/` layer's are the same group, by the identity function. -/
def centExtEquiv :
    WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat)
      ≃* WordCoh.CentExt (kappa0Cocycle dat hdat) where
  toFun p := p
  invFun p := p
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem centExtEquiv_base
    (p : WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat)) :
    WordCoh.CentExt.base (centExtEquiv dat hdat p) = sdEquiv (WordCoh2.CentExt.base p) := rfl

/-- **The fibre is preserved on the nose.**  This is the load-bearing line of the whole file:
every NC-lane jet value is a `.fib`, and this says the transported element carries the same
`𝔽₂` value, definitionally. -/
@[simp] theorem centExtEquiv_fib
    (p : WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat)) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) (centExtEquiv dat hdat p)
      = WordCoh2.CentExt.fib (c := SectionEight.AffineTLift.kappa0Cocycle dat hdat) p := rfl

@[simp] theorem centExtEquiv_symm_fib (p : WordCoh.CentExt (kappa0Cocycle dat hdat)) :
    WordCoh2.CentExt.fib (c := SectionEight.AffineTLift.kappa0Cocycle dat hdat)
        ((centExtEquiv dat hdat).symm p)
      = WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) p := rfl

/-- The central inclusions correspond. -/
@[simp] theorem centExtEquiv_incl (z : ZMod 2) :
    centExtEquiv dat hdat (WordCoh2.CentExt.incl _ z)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z := rfl

/-- Right conjugation is preserved — the identification is the identity function and the two
group laws are the same, so `conjR` transports definitionally. -/
@[simp] theorem centExtEquiv_conjR
    (x g : WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat)) :
    centExtEquiv dat hdat (conjR x g)
      = conjR (centExtEquiv dat hdat x) (centExtEquiv dat hdat g) := rfl

/-- The commutator is preserved. -/
@[simp] theorem centExtEquiv_commR
    (x y : WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat)) :
    centExtEquiv dat hdat (commR x y)
      = commR (centExtEquiv dat hdat x) (centExtEquiv dat hdat y) := rfl

/-- The carrier correspondence as a `ContinuousMonoidHom` — both extensions carry the discrete
topology, so continuity is free.  This is the form `Marking.map_eval` consumes. -/
noncomputable def centExtHom :
    ContinuousMonoidHom (WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat))
      (WordCoh.CentExt (kappa0Cocycle dat hdat)) :=
  ⟨(centExtEquiv dat hdat).toMonoidHom, continuous_of_discreteTopology⟩

@[simp] theorem centExtHom_coe : ⇑(centExtHom dat hdat) = ⇑(centExtEquiv dat hdat) := rfl

@[simp] theorem centExtHom_fib
    (p : WordCoh2.CentExt (SectionEight.AffineTLift.kappa0Cocycle dat hdat)) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) (centExtHom dat hdat p)
      = WordCoh2.CentExt.fib (c := SectionEight.AffineTLift.kappa0Cocycle dat hdat) p := rfl

end Extension

/-! ## §4. The slice calculus

WWH measured NC2's `elt`/`sliceElt`/`cLine` kit (`NpcJet/Defs.lean` §2) and WW4's
`hessSlice`/`hessLine`/`hessLineHom` kit (`Word/Hessian.lean`, hoisted there from
`Certificates/N0.lean`) as *the same mathematics on different carriers*.  Below that measurement
is discharged as theorems.

The `Word/` side has no typed constructor for the general element `((v,c),z)` — NC2's `elt`,
whose whole purpose is friction 1 (raw `Prod` literals finding `Prod.mul` instead of the
extension's product).  `hessElt` supplies it, and every correspondence below is stated in those
terms.

**The two kits are not the same size.**  `hessSlice_mul`, `hessSlice_inv`, `hessSlice_commR`,
`hessLine_mul`, `hessSlice_zero_zero` exist on both sides; those are shown to be images of one
another.  Six pieces of NC2 have no `Word/`-side statement at all — `cLine_inv`,
`sliceElt_mul_cLine`, `cLine_mul_sliceElt`, `sliceElt_conj`, `sliceElt_sq` and the whole `y^k`
power law of §3 — and they are supplied here by transport.  (`hessSlice_sq` and
`hessSlice_conj_line` *do* exist, but downstream in the plain files `Certificates/M0.lean` and
`Certificates/L.lean`, not in the `module` kit; the versions below are the `Word/`-carrier
statements of NC2's, and `hessSlice_sq_of_npc` shows the two spellings agree.) -/

section Slice

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The typed general element** `((v,c),z)` of the `Word/`-side `κ⁰`-extension — the
`module`-carrier twin of NC2's `elt`, and the same mitigation of NC2's friction 1: routing
every element through this constructor keeps `Prod`'s component-wise multiplication from being
found in place of the extension's. -/
def hessElt (v : V) (c : C) (z : ZMod 2) : WordCoh.CentExt (kappa0Cocycle dat hdat) :=
  ((v, c), z)

@[simp] theorem hessElt_base (v : V) (c : C) (z : ZMod 2) :
    WordCoh.CentExt.base (hessElt dat hdat v c z) = ((v, c) : SemiProd C V) := rfl

@[simp] theorem hessElt_fib (v : V) (c : C) (z : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) (hessElt dat hdat v c z) = z := rfl

theorem hessElt_one : hessElt dat hdat 0 1 0 = 1 := rfl

theorem hessSlice_eq_hessElt (v : V) (z : ZMod 2) :
    hessSlice dat hdat v z = hessElt dat hdat v 1 z := rfl

theorem hessLine_eq_hessElt (c : C) : hessLine dat hdat c = hessElt dat hdat 0 c 0 := rfl

/-! ### The objects correspond -/

/-- NC2's typed constructor transports to `hessElt`. -/
@[simp] theorem centExtEquiv_elt (v : V) (c : C) (z : ZMod 2) :
    centExtEquiv dat hdat (NpcJet.elt dat hdat v c z) = hessElt dat hdat v c z := rfl

/-- **NC2's Heisenberg slice is WW4's**, on the nose. -/
@[simp] theorem centExtEquiv_sliceElt (v : V) (z : ZMod 2) :
    centExtEquiv dat hdat (NpcJet.sliceElt dat hdat v z) = hessSlice dat hdat v z := rfl

/-- **NC2's κ-free `C`-line is WW4's**, on the nose. -/
@[simp] theorem centExtEquiv_cLine (c : C) :
    centExtEquiv dat hdat (NpcJet.cLine dat hdat c) = hessLine dat hdat c := rfl

/-- The `C`-line hom of the two lanes is the same hom. -/
theorem centExtEquiv_comp_cLine :
    (fun c : C ↦ centExtEquiv dat hdat (NpcJet.cLine dat hdat c)) = ⇑(hessLineHom dat hdat) :=
  rfl

/-! ### The five shared laws are images of one another

Each is proved *from the other lane's statement* through the bridge — not re-proved.  This is
the derivability that the retirement costing in the module docstring rests on. -/

/-- WW4's slice product law, obtained from NC2's. -/
theorem hessSlice_mul_of_npc (v w : V) (z z' : ZMod 2) :
    hessSlice dat hdat v z * hessSlice dat hdat w z'
      = hessSlice dat hdat (v + w) (z + z' + dat.f v w) := by
  rw [← centExtEquiv_sliceElt dat hdat v z, ← centExtEquiv_sliceElt dat hdat w z',
    ← map_mul, NpcJet.sliceElt_mul dat hdat, centExtEquiv_sliceElt]

/-- NC2's slice product law, obtained from WW4's. -/
theorem sliceElt_mul_of_hess (v w : V) (z z' : ZMod 2) :
    NpcJet.sliceElt dat hdat v z * NpcJet.sliceElt dat hdat w z'
      = NpcJet.sliceElt dat hdat (v + w) (z + z' + dat.f v w) :=
  (centExtEquiv dat hdat).injective <| by
    rw [map_mul, centExtEquiv_sliceElt, centExtEquiv_sliceElt, centExtEquiv_sliceElt,
      hessSlice_mul dat hdat]

/-- WW4's slice inversion law, obtained from NC2's. -/
theorem hessSlice_inv_of_npc (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    (hessSlice dat hdat v z)⁻¹ = hessSlice dat hdat v (z + q v) := by
  rw [← centExtEquiv_sliceElt dat hdat v z, ← map_inv, NpcJet.sliceElt_inv dat hdat hV2,
    centExtEquiv_sliceElt]

/-- NC2's slice inversion law, obtained from WW4's. -/
theorem sliceElt_inv_of_hess (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    (NpcJet.sliceElt dat hdat v z)⁻¹ = NpcJet.sliceElt dat hdat v (z + q v) :=
  (centExtEquiv dat hdat).injective <| by
    rw [map_inv, centExtEquiv_sliceElt, centExtEquiv_sliceElt, hessSlice_inv dat hdat hV2]

/-- WW4's slice commutator law, obtained from NC2's.  Note the two lanes spell the answer
differently — NC2 as the slice element `((0,1), b_q(d,w))`, WW4 as the central inclusion
`ι(b_q(d,w))` — and the bridge shows the spellings are the same element. -/
theorem hessSlice_commR_of_npc (hV2 : ∀ v : V, v + v = 0) (d w : V) (ζ ξ : ZMod 2) :
    commR (hessSlice dat hdat d ζ) (hessSlice dat hdat w ξ)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (polar q d w) := by
  rw [← centExtEquiv_sliceElt dat hdat d ζ, ← centExtEquiv_sliceElt dat hdat w ξ,
    ← centExtEquiv_commR, NpcJet.sliceElt_comm dat hdat hV2]
  rfl

/-- NC2's slice commutator law, obtained from WW4's. -/
theorem sliceElt_comm_of_hess (hV2 : ∀ v : V, v + v = 0) (d w : V) (ζ ξ : ZMod 2) :
    commR (NpcJet.sliceElt dat hdat d ζ) (NpcJet.sliceElt dat hdat w ξ)
      = NpcJet.sliceElt dat hdat 0 (polar q d w) :=
  (centExtEquiv dat hdat).injective <| by
    rw [centExtEquiv_commR, centExtEquiv_sliceElt, centExtEquiv_sliceElt, centExtEquiv_sliceElt,
      hessSlice_commR dat hdat hV2]
    rfl

/-- WW4's `C`-line product law, obtained from NC2's. -/
theorem hessLine_mul_of_npc (c d : C) :
    hessLine dat hdat c * hessLine dat hdat d = hessLine dat hdat (c * d) := by
  rw [← centExtEquiv_cLine dat hdat c, ← centExtEquiv_cLine dat hdat d, ← map_mul,
    NpcJet.cLine_mul dat hdat, centExtEquiv_cLine]

/-- NC2's `C`-line product law, obtained from WW4's. -/
theorem cLine_mul_of_hess (c d : C) :
    NpcJet.cLine dat hdat c * NpcJet.cLine dat hdat d = NpcJet.cLine dat hdat (c * d) :=
  (centExtEquiv dat hdat).injective <| by
    rw [map_mul, centExtEquiv_cLine, centExtEquiv_cLine, centExtEquiv_cLine,
      hessLine_mul dat hdat]

/-! ### The six pieces the `Word/` kit lacks, supplied by transport -/

/-- **The `Word/`-carrier `C`-line inversion law** (NC2's `cLine_inv`; no `module`-side
statement existed). -/
theorem hessLine_inv (c : C) : (hessLine dat hdat c)⁻¹ = hessLine dat hdat c⁻¹ := by
  rw [← centExtEquiv_cLine dat hdat c, ← map_inv, NpcJet.cLine_inv dat hdat,
    centExtEquiv_cLine]

/-- **Slice times `C`-line** on the `Word/` carrier (NC2's `sliceElt_mul_cLine`): this is how a
`δ₀`-base `((c₀,u),0)` is assembled from the Gate-E letters. -/
theorem hessSlice_mul_hessLine (v : V) (z : ZMod 2) (c : C) :
    hessSlice dat hdat v z * hessLine dat hdat c = hessElt dat hdat v c z := by
  rw [← centExtEquiv_sliceElt dat hdat v z, ← centExtEquiv_cLine dat hdat c, ← map_mul,
    NpcJet.sliceElt_mul_cLine dat hdat, centExtEquiv_elt]

/-- **`C`-line times slice** on the `Word/` carrier (NC2's `cLine_mul_sliceElt`). -/
theorem hessLine_mul_hessSlice (c : C) (w : V) (z' : ZMod 2) :
    hessLine dat hdat c * hessSlice dat hdat w z'
      = hessElt dat hdat (c • w) c (z' + dat.m c w) := by
  rw [← centExtEquiv_cLine dat hdat c, ← centExtEquiv_sliceElt dat hdat w z', ← map_mul,
    NpcJet.cLine_mul_sliceElt dat hdat, centExtEquiv_elt]

/-- **The `Word/`-carrier slice conjugation law** (NC2's `sliceElt_conj`): right conjugation by a
`C`-line element applies the **inverse** operator.  This is the mechanism that produces the three
inverse conjugators of the corrected `L_c = A⁻¹ + B + B·A⁻¹`, now stated `module`-side.

`Certificates/L.lean`'s `hessSlice_conj_line` is the `z = 0` case of this, in a plain file. -/
theorem hessSlice_conj_hessLine (v : V) (z : ZMod 2) (g : C) :
    conjR (hessSlice dat hdat v z) (hessLine dat hdat g)
      = hessSlice dat hdat (g⁻¹ • v) (z + dat.m g⁻¹ v) := by
  rw [← centExtEquiv_sliceElt dat hdat v z, ← centExtEquiv_cLine dat hdat g,
    ← centExtEquiv_conjR, NpcJet.sliceElt_conj dat hdat, centExtEquiv_sliceElt]

/-- **The `Word/`-carrier slice square law** (NC2's `sliceElt_sq`), in NC2's spelling
`((v,1),z)² = ((0,1), q v)`. -/
theorem hessSlice_sq_of_npc (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    hessSlice dat hdat v z ^ 2 = hessSlice dat hdat 0 (q v) := by
  rw [← centExtEquiv_sliceElt dat hdat v z, ← map_pow, NpcJet.sliceElt_sq dat hdat hV2,
    centExtEquiv_sliceElt]

/-- The two spellings of the square law agree: NC2's slice element `((0,1), q v)` **is** WW4's
central inclusion `ι(q v)` (`Certificates/M0.lean`'s `MCompact.hessSlice_sq` uses the latter). -/
theorem hessSlice_zero_eq_incl (z : ZMod 2) :
    hessSlice dat hdat 0 z = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z := rfl

/-! ### NC2 §3's power law on the `Word/` carrier

`normSum` and `powCharge` are carrier-free — they are functions of the module datum alone — so
only the three statements about powers of `((v,c),0)` need transporting.  These are what NC3's
`ω₂`-bridge consumes, and the `Word/` layer had no form of them. -/

/-- **The `y^k` power law** on the `Word/` carrier (NC2's `elt_pow`). -/
theorem hessElt_pow (v : V) (c : C) (k : ℕ) :
    hessElt dat hdat v c 0 ^ k
      = hessElt dat hdat (NpcJet.normSum c k v) (c ^ k) (NpcJet.powCharge dat c v k) := by
  rw [← centExtEquiv_elt dat hdat v c 0, ← map_pow, NpcJet.elt_pow dat hdat, centExtEquiv_elt]

/-- **The `y^m` reduction** on the `Word/` carrier (NC2's `elt_pow_eq_sliceElt`): once the
`c`-norm of `v` vanishes and `c^m = 1`, the `m`-th power lands in the Heisenberg slice. -/
theorem hessElt_pow_eq_hessSlice {c : C} {m : ℕ} (hm : c ^ m = 1) {v : V}
    (hN : ∑ i ∈ Finset.range m, c ^ i • v = 0) :
    hessElt dat hdat v c 0 ^ m = hessSlice dat hdat 0 (NpcJet.powCharge dat c v m) := by
  rw [← centExtEquiv_elt dat hdat v c 0, ← map_pow, NpcJet.elt_pow_eq_sliceElt dat hdat hm hN,
    centExtEquiv_sliceElt]

/-- **The order bound** on the `Word/` carrier (NC2's `orderOf_elt_dvd_two_mul`) — the
divisibility hypothesis NC3's `ω₂`-power bridge consumes. -/
theorem orderOf_hessElt_dvd_two_mul {c : C} {m : ℕ} (hm : c ^ m = 1) {v : V}
    (hN : ∑ i ∈ Finset.range m, c ^ i • v = 0) :
    orderOf (hessElt dat hdat v c 0) ∣ 2 * m := by
  rw [← centExtEquiv_elt dat hdat v c 0, (centExtEquiv dat hdat).orderOf_eq]
  exact NpcJet.orderOf_elt_dvd_two_mul dat hdat hm hN

end Slice

/-! ## §5. The Gate-E marking

NC2's `npcMarking` puts `σ, τ` on the `C`-line and the wild letters on the Heisenberg slice with
offsets `c₀, c₁, 0`.  Pushed along `centExtEquiv` it becomes exactly the `WordCoh.lift` of
WN0-b's graph marking `GQ2.Dyadic.Certificates.hessMark` at `(c₀, c₁, 0)` — the marking the
`Word/` layer's compact rows are already evaluated at (`hessRelZ_nCompact`,
`sqrtNegTwoHessMarking`).  So the two lanes were never marking differently; only the carrier
differed. -/

section Marking

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The Gate-E marking in `Word/` vocabulary**: `σ ↦ hessLine s`, `τ ↦ hessLine u`, wild
letters on the Heisenberg slice at `c₀`, `c₁` and (the boundary letter) `0`. -/
noncomputable def npcMarkingW (s u : C) (c₀ c₁ : V) :
    Marking 2 (WordCoh.CentExt (kappa0Cocycle dat hdat)) :=
  Marking.ofLetters (hessLine dat hdat s) (hessLine dat hdat u)
    ![hessSlice dat hdat c₀ 0, hessSlice dat hdat c₁ 0, hessSlice dat hdat 0 0]

/-- The genus-`h` Gate-E marking in `Word/` vocabulary (NC6's `npcMarkingH`). -/
noncomputable def npcMarkingHW (m : ℕ) (s u : C) (e : ℕ → V) :
    Marking (m + 2) (WordCoh.CentExt (kappa0Cocycle dat hdat)) :=
  Marking.ofLetters (hessLine dat hdat s) (hessLine dat hdat u)
    (fun i ↦ hessSlice dat hdat (e i.val) 0)

/-- **The marking transports.** -/
theorem map_npcMarking (s u : C) (c₀ c₁ : V) :
    (NpcJet.npcMarking dat hdat s u c₀ c₁).map ⇑(centExtEquiv dat hdat)
      = npcMarkingW dat hdat s u c₀ c₁ := by
  refine Marking.ext fun g ↦ ?_
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => fin_cases i <;> rfl

/-- **The genus-`h` marking transports.** -/
theorem map_npcMarkingH (m : ℕ) (s u : C) (e : ℕ → V) :
    (NpcJet.npcMarkingH dat hdat m s u e).map ⇑(centExtEquiv dat hdat)
      = npcMarkingHW dat hdat m s u e := by
  refine Marking.ext fun g ↦ ?_
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => rfl

/-- **The transported marking is the lift of WN0-b's graph marking.**  This is the sentence the
three reports were missing: `NpcJet.npcMarking` and `Certificates.hessMark` describe the same
Gate-E data, and after §3 they are literally the same function. -/
theorem npcMarkingW_eq_lift (s u : C) (c₀ c₁ : V) :
    ⇑(npcMarkingW dat hdat s u c₀ c₁)
      = WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0])
          (kappa0Cocycle dat hdat) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => fin_cases i <;> rfl

/-- At `m = 0` and a boundary-normalized offset function the two `Word/`-side markings agree. -/
theorem npcMarkingHW_zero (s u : C) (e : ℕ → V) (he2 : e 2 = 0) :
    npcMarkingHW dat hdat 0 s u e = npcMarkingW dat hdat s u (e 0) (e 1) := by
  refine Marking.ext fun g ↦ ?_
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      fin_cases i
      · rfl
      · rfl
      · exact congrArg (fun v ↦ hessSlice dat hdat v 0) he2

end Marking

/-! ## §6. The centrepiece, transported

`npc_cross_operators` and NC6's handle form, restated with no `WordCoh2` name anywhere: the
value lives in `WordCoh.CentExt (kappa0Cocycle dat hdat)`, the marking is built from `hessLine`
and `hessSlice`, and the fibre is read by `WordCoh.CentExt.fib`.  The right-hand sides keep
NC2's `npcQ0` and `lcOp`, which are functions of the module datum only and are already
carrier-free. -/

section Headline

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- **The corrected noncompact-`N` cross-operator identity, in `Word/` vocabulary.**

This is NC5's `npc_cross_operators` — the S3.2-corrected `L_c = A⁻¹ + B + B·A⁻¹` replacing
draft eq:Ncross's `L_c = A⁻¹` — with its value transported into the `module`-side κ⁰-extension.
Nothing is re-proved: the content is NC5's, and the only new ingredient is §3's carrier
identification, which preserves the fibre definitionally.

Hypotheses are NC5's verbatim (`hV2` characteristic 2, `hu` rule 1, `hVu` rule 2, `hα` sharp);
in particular the identity still holds for **all** `r : ℕ` and **all** `η : ℤ_[2]`. -/
theorem npc_cross_operators_word (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((npcMarkingW dat hdat s u c₀ c₁).eval (NpcJet.npcWord α r η))
      = NpcJet.npcQ0 dat s η c₀ + polar q c₁ (NpcJet.lcOp s η r c₀) := by
  have h := Marking.map_eval (centExtHom dat hdat) (NpcJet.npcMarking dat hdat s u c₀ c₁)
    (NpcJet.npcWord α r η)
  rw [centExtHom_coe, map_npcMarking dat hdat s u c₀ c₁] at h
  rw [← h]
  exact NpcJet.npc_cross_operators dat hdat hV2 s u hu hVu α hα r η c₀ c₁

/-- **The handle form, in `Word/` vocabulary** (NC6's `npc_cross_operators_handles_std`): the
genus-`h` core gains the hyperbolic sum `∑_j b_q(e_{3+2j}, e_{4+2j})`. -/
theorem npc_cross_operators_handles_std_word (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (h : ℕ) (e : ℕ → V) (he2 : e 2 = 0) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((npcMarkingHW dat hdat (2 * h) s u e).eval
          (NpcJet.npcWordH (2 * h) α r η
            (fun j ↦ ⟨(3 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩)
            (fun j ↦ ⟨(4 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩) h))
      = NpcJet.npcQ0 dat s η (e 0) + polar q (e 1) (NpcJet.lcOp s η r (e 0))
        + ∑ j ∈ Finset.range h, polar q (e (3 + 2 * j)) (e (4 + 2 * j)) := by
  have hm := Marking.map_eval (centExtHom dat hdat)
    (NpcJet.npcMarkingH dat hdat (2 * h) s u e)
    (NpcJet.npcWordH (2 * h) α r η
      (fun j ↦ ⟨(3 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩)
      (fun j ↦ ⟨(4 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩) h)
  rw [centExtHom_coe, map_npcMarkingH dat hdat (2 * h) s u e] at hm
  rw [← hm]
  exact NpcJet.npc_cross_operators_handles_std dat hdat hV2 s u hu hVu α hα r η h e he2

/-- **The identity at the hash-pinned certificate word, in `Word/` vocabulary.**

`Certificates/Npc.lean` does not cite `npc_cross_operators` directly — it cites WNP-b's
`npc_cross_operators_npcW`, the same identity at the *frozen* tree `Words.Npc.npcW` whose digest
the freeze pins, reached through WNP-a's value bridge `eval_npcW_eq_eval_npcWord`.  That bridge
is generic over profinite targets, so it applies to the `Word/` carrier unchanged; this is
therefore the form a `Word/`-layer consumer will actually want. -/
theorem npc_cross_operators_npcW_word (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) (c₀ c₁ : V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((npcMarkingW dat hdat s u c₀ c₁).eval (Words.Npc.npcW α r 0 e))
      = NpcJet.npcQ0 dat s e.toPadic c₀ + polar q c₁ (NpcJet.lcOp s e.toPadic r c₀) := by
  rw [Words.Npc.eval_npcW_eq_eval_npcWord]
  exact npc_cross_operators_word dat hdat hV2 s u hu hVu α hα r e.toPadic c₀ c₁

end Headline

section Companion

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- **NC5's packet-facing companion needs no transport.**  `hVu_of_simple` is a statement about
the `C`-module `V` alone — no extension, no cocycle, no carrier — so it is already citable from
`Word/`-layer code exactly as it stands.  Recorded here so that the audit of "what the NC lane
exports across the bridge" is complete: two of the three items needed transport, this one did
not. -/
theorem hVu_of_simple_restated {u : C}
    (hsimple : ∀ W : AddSubgroup V, (∀ h : C, ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, u • v ≠ v) (hnorm : ∀ g : C, g * u * g⁻¹ ∈ Subgroup.zpowers u) :
    ∀ v : V, u • v = v → v = 0 :=
  NpcJet.hVu_of_simple hsimple hram hnorm

end Companion

/-! ## §7. `hessRelZ` and WW4 gap item 5

WW4's `hessRelZ` is the *integer-resolver* denotation (`PWord.evalZ` at the zero-fibre lift),
while the NC lane evaluates profinitely (`Marking.eval`).  F2's two-form bridge
`PWord.eval_eq_evalZ` connects them under `ResolvedAt`; `npcWord` carries a genuine `η̂`-exponent
(`PWord.etaPow` is a `profPow` at `etaHatZ η`, not at `ω₂`), so the procyclic-`N` row is **not**
`ω₂`-only and the resolver hypothesis is real, not removable. -/

section HessRelZ

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

/-- **The word-side Hessian equation for the procyclic-`N` row.**

The evaluated Hessian of the frozen noncompact-`N` word at the graph-type κ⁰-marking is the
corrected endpoint `Q₀(c₀) + b_q(c₁, L_c c₀)`.  This is the `npc_cross_operators` analogue of
`hessRelZ_nCompact` — the shape `HessRelZTarget` asks for — now available on this row.

The resolver hypothesis is the honest one: unlike the compact rows, `npcWord` is not `ω₂`-only,
so `E` must compute `η̂` at the elements actually reached. -/
theorem hessRelZ_npcWord (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat))
      E E₂ (NpcJet.npcWord α r η)) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (NpcJet.npcWord α r η)
      = NpcJet.npcQ0 dat s η c₀ + polar q c₁ (NpcJet.lcOp s η r c₀) := by
  rw [hessRelZ, hessEvalZ, ← PWord.eval_eq_evalZ _ E E₂ _ hres,
    ← npcMarkingW_eq_lift dat hdat s u c₀ c₁]
  exact npc_cross_operators_word dat hdat hV2 s u hu hVu α hα r η c₀ c₁

/-- **WW4 gap item 5, discharged on the procyclic-`N` row.**

`HessRelZTarget` is `Certificates/Mpc.lean`'s name for "the word-side equation the certificate
layer wants but nobody proved".  This exhibits an inhabitant: with the bridge in hand the target
type is not merely nameable, it is provable — on the row where the jet theorem exists.

The endpoint is read in `plusFormD` shape: `Q(c₀, c₁) = Q₀(c₀) + b_q(c₀, L_c c₀ … )` is the
corrected-Npc endpoint of WW4's `npcShape_certificate`, with `Q₀ := npcQ0 dat s η` and
`Lc := lcOp s η r`, exactly as that docstring's "wave-2 bridge item" predicted. -/
theorem npc_hessRelZTarget (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (c₀ c₁ : V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat))
      E E₂ (NpcJet.npcWord α r η)) :
    Certificates.MProcyclic.HessRelZTarget dat hdat
      (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) E E₂ (NpcJet.npcWord α r η)
      (fun p ↦ NpcJet.npcQ0 dat s η p.1 + polar q p.2 (NpcJet.lcOp s η r p.1)) c₀ c₁ :=
  hessRelZ_npcWord dat hdat hV2 s u hu hVu α hα r η c₀ c₁ E E₂ hres

/-- **The same, at the hash-pinned certificate word** — the form matching WNP-b's
`npc_cross_operators_npcW`, and the one a `Word/`-layer certificate would consume. -/
theorem npcW_hessRelZTarget (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) (c₀ c₁ : V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat))
      E E₂ (Words.Npc.npcW α r 0 e)) :
    Certificates.MProcyclic.HessRelZTarget dat hdat
      (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) E E₂ (Words.Npc.npcW α r 0 e)
      (fun p ↦ NpcJet.npcQ0 dat s e.toPadic p.1
        + polar q p.2 (NpcJet.lcOp s e.toPadic r p.1)) c₀ c₁ := by
  show hessRelZ _ _ E E₂ _ = _
  rw [hessRelZ, hessEvalZ, ← PWord.eval_eq_evalZ _ E E₂ _ hres,
    ← npcMarkingW_eq_lift dat hdat s u c₀ c₁]
  exact npc_cross_operators_npcW_word dat hdat hV2 s u hu hVu α hα r e c₀ c₁

end HessRelZ

/-! ### The procyclic-`M` row: the statement WMP-c could not make

Below is `HessRelZTarget` for the procyclic-`M` row, fully instantiated: the marking is WN0-b's
`hessMark` at `(c₀, c₁, 0)` (the same one the `N` rows use, and the one §5 shows the NC lane's
Gate-E marking to be), the word is the frozen `Words.Mpc.mpcW α r p η 0`, and the target
polynomial is `mpcHessianCertificate`'s endpoint `plusFormD d₀ q` at its abstract κ⁰-normalized
diagonal `d₀`.

Every name in it exists and the statement typechecks — that is this file's deliverable on item
5.  **Proving it is not**, and the reason is worth being precise about: the missing ingredient is
not the bridge but an `mpcW` jet theorem.  See the module docstring. -/

section MpcTarget

open Words.Mpc

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **WW4 gap item 5 for the procyclic-`M` row, stated.**

`hessRelZ` of the frozen `mpcW` at the graph-type κ⁰-marking equals the row's endpoint
polynomial `plusFormD d₀ q` at `(c₀, c₁)` — the `npc_cross_operators` analogue for `mpcW`,
which is what `mpcHessianCertificate`'s `affinePhase` is an *input* for rather than a
consequence of. -/
def mpcHessRelZTarget (d₀ : V → ZMod 2) (s u : C) (c₀ c₁ : V) (α r p : ℕ) (η : EtaDisplay)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : Prop :=
  Certificates.MProcyclic.HessRelZTarget dat hdat
    (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) E E₂ (mpcW α r p η 0)
    (plusFormD d₀ q) c₀ c₁

/-- The target, unfolded — what a successor ticket actually has to prove. -/
theorem mpcHessRelZTarget_iff (d₀ : V → ZMod 2) (s u : C) (c₀ c₁ : V) (α r p : ℕ)
    (η : EtaDisplay) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    mpcHessRelZTarget dat hdat d₀ s u c₀ c₁ α r p η E E₂
      ↔ hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)
            E E₂ (mpcW α r p η 0)
          = d₀ c₀ + polar q c₀ c₁ :=
  Iff.rfl

/-- **The `M` row is resolver-immune where the `N` row is not.**  `mpcW` at an `ω₂`-only
`η`-display *is* `ω₂`-only (`Words.Mpc.isOmega2Only_mpcW`), so on that row the profinite value
and the `hessRelZ` value coincide for **every** resolver pair — the target above may be proved
at any `E`, `E₂` and read profinitely afterwards.  Contrast `hessRelZ_npcWord`, which carries a
real `ResolvedAt` hypothesis because `npcWord` has an `η̂`-exponent node. -/
theorem mpc_eval_eq_hessRelZ [Finite C] [Finite V] (s u : C) (c₀ c₁ : V) (α r p : ℕ)
    {η : EtaDisplay} (hη : η.IsOmega2Only) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hE : ∀ x : WordCoh.CentExt (kappa0Cocycle dat hdat), x ^ᶻ omega2 = x ^ E omega2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((Marking.mk (WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0])
          (kappa0Cocycle dat hdat))).eval (mpcW α r p η 0))
      = hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)
          E E₂ (mpcW α r p η 0) := by
  rw [Marking.eval_def, hessRelZ, hessEvalZ]
  exact congrArg _ (PWord.eval_eq_evalZ _ E E₂ _
    (PWord.resolvedAt_of_isOmega2Only _ E E₂ hE _ (isOmega2Only_mpcW α r p hη 0)))

end MpcTarget

end GQ2.Dyadic.NpcBridge
