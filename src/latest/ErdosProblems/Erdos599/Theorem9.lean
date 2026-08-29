/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ExtensionClauseStep
import ErdosProblems.Erdos599.HalfwayClause

/-!
# Erdős Problem 599: the cardinal-induction assembly

This module is the final assembly point for Aharoni--Berger, Theorem 9.2,
and its source-cardinal specialization, Theorem 7.29.  The foundational
well-founded induction is in `CardinalInduction`; the concrete extension
and half-way steps are imported here once their independent constructions
have been discharged.

The public theorem in this module has no result-producing hypotheses: it
states directly that every unhindered concrete web is linkable.
-/

noncomputable section

namespace Erdos599
namespace Theorem9

open Cardinal

universe u

variable {V : Type u}

/-- Aharoni--Berger, Theorem 9.2: the simultaneous extension and half-way
clauses hold at every cardinal.  The half-way clause is guarded by the
source-faithful infinitude condition in `CardinalInductionAt`. -/
theorem universalCardinalInduction :
    ∀ kappa : Cardinal.{u},
      CardinalInduction.UniversalCardinalInductionAt V kappa :=
  CardinalInduction.universalCardinalInduction_of_steps
    CardinalInduction.extensionClauseStep
    CardinalInduction.halfwayClauseStep

/-- Aharoni--Berger, Theorem 7.29: every unhindered web is linkable. -/
theorem unhindered_isLinkable (Gamma : DWeb V)
    (hGamma : Gamma.IsUnhindered) :
    CardinalInduction.IsLinkable Gamma :=
  CardinalInduction.linkable_of_cardinalInductionAt_source Gamma
    (universalCardinalInduction #Gamma.source Gamma hGamma)

end Theorem9
end Erdos599
