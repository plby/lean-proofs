/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.CFP.Witness

/-!
# Enlarging the source of a fixed-scale CFP witness

This file records the elementary loss bookkeeping needed after CFP
preprocessing.  A witness whose structured core lies in a smaller source can
be regarded as a witness for a larger source, provided the number of newly
adjoined elements is charged to the loss.  The progression, reserve, scale,
and coverage data are unchanged.
-/

namespace Erdos186.CFP

noncomputable section

namespace FixedScaleWitness

variable {d s D k extraLoss preprocessingLoss scaleNum scaleDen : ℕ}
    {H K : Finset (LatticePoint d)}

/-- Enlarge the source of a fixed-scale witness, charging the cardinality
increase to an additional preprocessing loss. -/
noncomputable def enlargeSource
    (W : FixedScaleWitness H s D k extraLoss scaleNum scaleDen)
    (hHK : H ⊆ K)
    (hlarge : K.card ≤ H.card + preprocessingLoss) :
    FixedScaleWitness K s D k (preprocessingLoss + extraLoss)
      scaleNum scaleDen := by
  let E : EnhancedCFPWitness K s D k (preprocessingLoss + extraLoss) :=
    { W.enhanced with
      core_subset := W.enhanced.core_subset.trans hHK
      core_large := by
        have hcore := W.enhanced.core_large
        omega }
  exact ⟨E, W.scaleNum_eq, W.scaleDen_eq⟩

/-- Proposition-valued form of `enlargeSource`, convenient at existence
boundaries. -/
theorem nonempty_enlargeSource
    (hW : Nonempty
      (FixedScaleWitness H s D k extraLoss scaleNum scaleDen))
    (hHK : H ⊆ K)
    (hlarge : K.card ≤ H.card + preprocessingLoss) :
    Nonempty
      (FixedScaleWitness K s D k (preprocessingLoss + extraLoss)
        scaleNum scaleDen) := by
  exact ⟨(Classical.choice hW).enlargeSource hHK hlarge⟩

end FixedScaleWitness

end

end Erdos186.CFP
