/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularSafeCompletedMachine
import ErdosProblems.Erdos599.SingularSafeDesignatedLinkage

/-!
# Finite safe-batch selection for the singular completed-row machine

The completed-row machine asks for safely deletable target linkages in each
current residual.  Below `aleph0` every request is finite, so the finite
iteration of Aharoni--Berger Theorem 6.1 supplies that input
unconditionally.  This is the base case of any transfinite designated-batch
selection argument.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SingularSafeSelectionFinite

open SingularSafeCompletedMachine SingularSafeDesignatedLinkage

universe u

variable {V : Type u}

/-- Repackage an ambient safe designated linkage in `G.delete X` as the
residual batch consumed by the completed-row machine. -/
def safeBatchInDeletionOfSafeDesignated
    (G : DWeb V) (X A : Set V)
    (S : SafeDesignatedLinkage (G.delete X) A) :
    SafeBatchInDeletion G X A where
  paths := S.paths
  linkage := S.linkage
  residual := S.residual_unhindered

/-- At every threshold at most `aleph0`, all smaller requests are finite and
can be safely completed in an arbitrary unhindered residual. -/
theorem safeBatchSelectionBelow_of_le_aleph0
    {G : DWeb V} (hNorm : G.IsNormalized)
    {kappa : Cardinal.{u}} (hkappa : kappa ≤ aleph0) :
    SafeBatchSelectionBelow G kappa := by
  intro X A hresidual hAsource hAcard
  have hAfinite : A.Finite :=
    Cardinal.lt_aleph0_iff_set_finite.mp (hAcard.trans_le hkappa)
  obtain ⟨S⟩ := SingularSafeDesignatedLinkage.exists_finite
    (G.delete X) (isNormalized_delete hNorm X) hresidual
      hAfinite hAsource
  exact ⟨safeBatchInDeletionOfSafeDesignated G X A S⟩

theorem safeBatchSelectionBelow_aleph0
    {G : DWeb V} (hNorm : G.IsNormalized) :
    SafeBatchSelectionBelow G aleph0 :=
  safeBatchSelectionBelow_of_le_aleph0 hNorm le_rfl

#print axioms safeBatchSelectionBelow_of_le_aleph0

end SingularSafeSelectionFinite
end CardinalInduction
end Erdos599

