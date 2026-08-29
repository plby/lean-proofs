/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularBoundarySplit

/-!
# Cardinal and source facts for singular-row terminal requests

The next row of the singular construction is built in a quotient by the
current stop-over `D`.  Its designated sources are the terminals of the old
components whose initial vertices belong to the requested set `T`.  This file
packages the two facts needed to apply the lower half-way clause there:

* those terminals belong to the source of `G / D`; and
* passage along the old warp preserves the cardinality of `T` exactly.

The cardinal bijection is proved in `SingularBoundarySplit`.  The source
argument is stated first with the precise abstract hypothesis
`D ⊆ (G / D).source`, and then specialized to a separating trimmed stop-over,
where the quotient source is literally `D`.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularRequestedFrontier

open SingularBoundarySplit SingularContinuation

universe u

variable {V : Type u}

/-- Restricting the old family by its initial vertices cannot create a new
terminal. -/
theorem requestedFrontier_subset_terminalFrontier
    (G : DWeb V) (W : Set G.DPath) (T : Set V) :
    requestedFrontier G W T ⊆ G.terminalFrontier W := by
  rintro x ⟨p, hp, hterminal⟩
  exact ⟨p, hp.1, hterminal⟩

/-- Abstract quotient-source form: it is enough that the current stop-over
is contained in the source of its quotient. -/
theorem requestedFrontier_subset_quotientSource
    {G : DWeb V} {W : Set G.DPath} {D T : Set V}
    (hterminal : G.terminalFrontier W ⊆ D)
    (hDsource : D ⊆ (G.quotient D).source) :
    requestedFrontier G W T ⊆ (G.quotient D).source :=
  (requestedFrontier_subset_terminalFrontier G W T).trans
    (hterminal.trans hDsource)

/-- For a separating trimmed stop-over, the current boundary is exactly the
source of the quotient, so every requested old terminal is a legal source for
the next row. -/
theorem requestedFrontier_subset_quotientSource_of_stopover
    {G : DWeb V} {W : Set G.DPath} {D T : Set V}
    (hsep : IsSeparatorFrom G G.source D)
    (htrim : IsTrimmedSeparator G D)
    (hterminal : G.terminalFrontier W ⊆ D) :
    requestedFrontier G W T ⊆ (G.quotient D).source := by
  rw [quotient_source_eq_stopover G hsep htrim]
  exact (requestedFrontier_subset_terminalFrontier G W T).trans hterminal

end SingularRequestedFrontier
end CardinalInduction
end Erdos599
