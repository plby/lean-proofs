/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRelaxedCorridor
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Assertion 8.17 for the legal-ladder auxiliary web

The current concrete cut package defines `G0` extensionally as the surviving
fragments which are blockable: either they meet the relaxed escape region or
they are finite.  Thus the fragment-classification form of Assertion 8.17 is
the escape branch of that definition.  The nontrivial edge-gadget work is in
the later backward splice: a relaxed escape may begin after the virtual
forward step, and reversing the contacted fragment absorbs that open start
before the suffix is stored by the descent.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace GroundingAssertion817

open DirectedPath

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

abbrev Aux (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal) :=
  L.popularAuxiliaryInput hlegal

abbrev LV (L : Gamma.KappaLadder kappa) (_hlegal : L.IsLegal) :=
  PopularAuxiliary.Input.LambdaVertex V L.groundedInfiniteRecords

/-- Assertion 8.17: every surviving fragment which meets the start-relaxed
escape region is retained in `G0`.

This statement retains the separator parameter because downstream Section 8
interfaces supply it uniformly, although membership in the extensional `G0`
itself needs only the escape witness.
-/
theorem fragment_meeting_relaxedEscape_mem_G0
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (C : Set (LV L hlegal))
    (_hC : Popular.IsSeparator (Aux L hlegal).lambda C)
    (P : (Aux L hlegal).Fragment)
    (hP : P ∈ GroundingCut.fragments (Aux L hlegal) C)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape
      (Aux L hlegal) C P) :
    P ∈ GroundingCut.G0 (Aux L hlegal) C :=
  GroundingCut.fragment_meeting_escape_mem_G0
    (Aux L hlegal) C P hP hescape

end GroundingAssertion817
end Erdos599
