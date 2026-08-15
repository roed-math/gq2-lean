/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcBuild

/-!
# W86-LADDER5: the `M6` ladder at class five and above

Wave 85 (`GQ2/Dyadic/Instances/MpcBuild.lean`) climbed the class-four rung of the `M6` ansatz and
built the increment engine that prices every correction slot exactly.  This module takes the
ladder up from there.

Declaration prefix `mpcLad` (namespace `GQ2.Dyadic.Instances.MpcLad`).  No `sorry`, no new
axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.
-/

namespace GQ2.Dyadic.Instances.MpcLad

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcPiv GQ2.Dyadic.Instances.MpcOrb GQ2.Dyadic.Instances.MpcWord
open GQ2.Dyadic.Instances.MpcBld
open GQ2.Roe.Labute GQ2.Dyadic.SqCore

noncomputable section

/-! ## §0 Orientation -/

/-- The wave-85 class-four witness, as a four-tuple in the shape the solution sets take. -/
def mpcLadW4 : (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) × (DM 2 0 : Type) :=
  (mpcBldW, mpcBldW, 1, 1)

theorem mpcLad_w4_mem : mpcLadW4 ∈ mpcWordSet 4 := by
  refine ⟨⟨mpcBld_w_mem, ?_⟩, ⟨mpcBld_w_mem, ?_⟩, one_mem _, one_mem _,
    mpcBld_mem_four_witness⟩ <;>
  exact mpcBld_chi_commP _ _

section AxiomPins

#print axioms mpcLadW4
#print axioms mpcLad_w4_mem

end AxiomPins

end

end GQ2.Dyadic.Instances.MpcLad
