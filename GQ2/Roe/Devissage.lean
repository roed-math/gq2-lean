/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Devissage.Naturality
public import GQ2.Roe.Devissage.TracedRows
public import GQ2.Roe.Devissage.EvalPairings
public import GQ2.Roe.Devissage.Chi1
public import GQ2.Roe.Devissage.SelfDual
public import GQ2.Roe.Devissage.LESCore
public import GQ2.Roe.Devissage.LESExact
public import GQ2.Roe.Devissage.LESMaster
public import GQ2.Roe.Devissage.GeneratesBridge

@[expose] public section

/-!
# §5.11 dévissage on the `r_R` spine: two-out-of-three for `IsSelfDualR`

Mechanical R-spine clone hub, mirroring `GQ2/Devissage.lean` (campaign decision,
`docs/orchestration/roe-r20-recon.md`).  `lemma_5_11_R` (bottom of
`GQ2/Roe/Devissage/GeneratesBridge.lean`) is the two-out-of-three property of `IsSelfDualR` along
a short exact sequence of finite elementary `𝔽₂[C]`-modules, proved via the long exact cohomology
sequence of the Roe word complex `C_R(A) : A --d⁰--> A⁴ --d¹_R--> A²` exactly as the `Γ_A`
capstone.

The proofs port **verbatim** onto the `r_R` spine (they only forward `hw : t.WildRelR` and use
`d¹_R∘d⁰ = 0`, functoriality, the LES, and finite linear algebra — never unfolding the aux words);
the elementary-dual pack (`GQ2.Devissage.ElemDualPack`) and every `(A)`-classified helper are
reused from `GQ2.Devissage.*`, never cloned.  The traced-row seams `prop_5_8_*_R`/`lemma_5_6_R`
(nominally ticket R23) are provided in `GQ2.Roe.Devissage.TracedRows`.
-/
