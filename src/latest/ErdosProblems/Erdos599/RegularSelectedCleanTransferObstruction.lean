/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularProgressiveExchangeCounterexample
import ErdosProblems.Erdos599.RegularCompletedPendingSplice

/-!
# A bottleneck obstruction to monotone selected/clean transfer

Retaining an already completed target component while absorbing every clean
component which meets it is not a valid generic exchange rule.  In the
crossing web, the completed `d-x-t1` component has claimed `x`, while every
target path from `b` extending the displayed pending prefix must also use
`x`.  Thus no forward successor can both retain the displayed row and link
`b`, even if the successor is presented as a selected/clean union.

The regular successor therefore has to choose its clean family disjointly
from the completed carrier (as in `IsCleanTargetStep`); it cannot repair an
arbitrary collision afterwards while monotonically preserving the completed
row.
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace RegularSelectedCleanTransferObstruction

open SingularSafeBatchCounterexample
open SingularSafeBatchCounterexample.Vertex
open SingularProgressiveExchangeCounterexample

/-- Exact failure of the proposed monotone `K`-versus-clean transfer. -/
theorem no_forward_selectedCleanTransfer :
    ¬ ∃ (selected clean : Set web.DPath),
      web.IsWarp (selected ∪ clean) ∧
        web.ForwardExtension paths (selected ∪ clean) ∧
        LinksToTarget web clean {b} := by
  rintro ⟨selected, clean, hwarp, hforward, hcleanLinks⟩
  apply no_forward_warp_links_b
  refine ⟨selected ∪ clean, hwarp, hforward, ?_⟩
  intro a ha
  obtain ⟨p, hp, rest⟩ := hcleanLinks a ha
  exact ⟨p, Or.inr hp, rest⟩

/-- The same crossing web refutes the exact completed/pending successor
boundary used by the regular canonical recursion.  Freezing the completed
part cannot make the newly requested source `b` target-linked. -/
theorem no_cleanTargetStep_links_b :
    ¬ ∃ (T : Set web.DPath)
        (hcompat : web.StarCompatible
          (SingularExtension.pendingPart web paths) T),
      RegularCompletedPendingSplice.IsCleanTargetStep
          web paths T hcompat ∧
        LinksToTarget web
          (RegularCompletedPendingSplice.freezeCompletedStar
            web paths T hcompat) {b} := by
  rintro ⟨T, hcompat, hstep, hlinks⟩
  apply no_forward_warp_links_b
  exact ⟨
    RegularCompletedPendingSplice.freezeCompletedStar web paths T hcompat,
    RegularCompletedPendingSplice.IsCleanTargetStep.result_isWarp hstep,
    RegularCompletedPendingSplice.IsCleanTargetStep.result_forwardExtension
      hstep,
    hlinks⟩

end RegularSelectedCleanTransferObstruction
end CardinalInduction
end Erdos599
