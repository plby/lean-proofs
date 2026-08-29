/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ExactFrontierExtensionClauseStep

/-!
# Exact-frontier assembly of Aharoni--Berger's simultaneous induction

The singular extension construction needs the literal frontier produced by
the lower half-way clauses.  The regular construction uses the same stronger
lower hypothesis.  This file records the final well-founded assembly seam:
once the exact-lower regular branch and the exact half-way branch are
available, every unhindered web is linkable.

This is deliberately an assembly lemma, not a replacement for either of the
two graph-theoretic branch constructions.
-/

noncomputable section

open Cardinal

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- Assemble the exact-frontier induction from the two remaining public
branch steps.  Countable and singular extension cases are discharged by
`extensionClauseStepExact_of_exactRegularStep`. -/
theorem universalExactFrontierCardinalInduction_of_branchSteps
    (regularStep : ∀ rho : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V rho → rho.IsRegular →
      aleph0 < rho → UniversalExtensionClauseAt V rho)
    (halfwayStep : ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      aleph0 ≤ kappa →
        ∀ Gamma : DWeb V, Gamma.IsUnhindered →
          ExactFrontierHalfwayClauseAt Gamma kappa) :
    ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionAt V kappa :=
  universalExactFrontierCardinalInduction_of_steps
    (extensionClauseStepExact_of_exactRegularStep regularStep) halfwayStep

/-- Source-cardinal specialization of the exact-frontier simultaneous
induction. -/
theorem unhindered_isLinkable_of_exactFrontier_branchSteps
    (regularStep : ∀ rho : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V rho → rho.IsRegular →
      aleph0 < rho → UniversalExtensionClauseAt V rho)
    (halfwayStep : ∀ kappa : Cardinal.{u},
      UniversalExactFrontierCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      aleph0 ≤ kappa →
        ∀ Gamma : DWeb V, Gamma.IsUnhindered →
          ExactFrontierHalfwayClauseAt Gamma kappa)
    (Gamma : DWeb V) (hGamma : Gamma.IsUnhindered) :
    IsLinkable Gamma := by
  let hExact :=
    universalExactFrontierCardinalInduction_of_branchSteps
      regularStep halfwayStep
  exact linkable_of_cardinalInductionAt_source Gamma
    ((hExact #Gamma.source Gamma hGamma).toCardinalInductionAt)

#print axioms universalExactFrontierCardinalInduction_of_branchSteps
#print axioms unhindered_isLinkable_of_exactFrontier_branchSteps

end CardinalInduction
end Erdos599
