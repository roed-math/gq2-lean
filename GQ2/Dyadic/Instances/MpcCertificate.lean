/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.GeneralAssembly
import GQ2.Dyadic.Instances.FieldBranchIdentification
import GQ2.Dyadic.Instances.FieldUnimodularity

/-!
# The marked-core certificate producer for the procyclic `M` rows

Lane W79-MPC.  Wave 78 (`docs/dyadic/w78-unimod-note.md` §2.3) showed that at `ℚ₂(√10)` and
`ℚ₂(√−10)` the marked level is `B.r = 1`, so wave 77's branch data for those two fields, built at
`pres = .M0 2 0`, carry an unsatisfiable hypothesis.  `Main.lean:136-137` puts both fields on the
`.Mpc 2 1 _ 1` rows instead.  This module supplies the producer that row needs.

Work in progress: the skeleton is banked first, per lane protocol.
-/

namespace GQ2.Dyadic.Instances.MpcCertificate

end GQ2.Dyadic.Instances.MpcCertificate
