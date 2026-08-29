/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayMacroStageAccounting

/-!
# The stopped-row boundary of a macro continuation

`MacroStageContinuationData` currently requires its completed target path to
use only edges of the stopped later row.  This is stronger than retaining an
ambient target linkage: the suffix after the first visit to the later slice
is not an edge of that stopped row.

The results below record the exact incompatibility.  A continuation whose
scheduled vertex is already a terminal of the later row forces that vertex
to lie in the ambient target.  Consequently a non-target later-row terminal
cannot be resolved by the current record; the transaction must explicitly
adjoin the retained ambient suffix (or use the full Assertion 9.30 splice).
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace Blueprint
namespace LinkageBlueprint

open DirectedPath _root_.Erdos599.Alternating

universe u

variable {V : Type u}
variable {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa theta : Cardinal.{u}}

namespace MarkerAbsorbedMacroRequest.MacroStageContinuationData

variable {S : MarkerAbsorbedMacroSeed
  (Gamma := Gamma) (Y := Y) (kappa := kappa)}
variable {C : ClubStageGeometry Gamma Y kappa theta}
variable {old : LinkageBlueprint Gamma Y kappa} {z : V}
variable {R : MarkerAbsorbedMacroRequest S}

/-- A target continuation confined to the stopped later row cannot leave a
terminal of that row.  Hence its scheduled terminal must already belong to
the ambient target. -/
theorem scheduled_mem_target_of_mem_laterTerminal
    (D : R.MacroStageContinuationData C old z)
    (hz : z ∈ Gamma.terminalFrontier S.later) :
    z ∈ Gamma.target := by
  by_contra hzTarget
  have hne : D.targetPath.start ≠ D.targetPath.finish := by
    intro h
    apply hzTarget
    rw [← D.targetPath_start, h]
    exact D.targetPath_finish
  obtain ⟨v, hv⟩ :=
    Alternating.FinitePath.exists_outgoing_edge_of_mem_support_of_ne_finish
      D.targetPath D.targetPath.start_mem_support hne
  rw [terminalFrontier_eq_vertexSet_diff_hasOutgoing
      S.later_isWarp S.later_finite] at hz
  apply hz.2
  refine ⟨v, D.targetPath_edges_row ?_⟩
  simpa only [D.targetPath_start] using hv

/-- In particular, the present macro-continuation record is empty at every
non-target terminal of its stopped later row. -/
theorem not_nonempty_of_mem_laterTerminal_of_not_mem_target
    (hz : z ∈ Gamma.terminalFrontier S.later)
    (hzTarget : z ∉ Gamma.target) :
    ¬ Nonempty (R.MacroStageContinuationData C old z) := by
  rintro ⟨D⟩
  exact hzTarget (D.scheduled_mem_target_of_mem_laterTerminal hz)

end MarkerAbsorbedMacroRequest.MacroStageContinuationData

end LinkageBlueprint
end Blueprint
end Erdos599
