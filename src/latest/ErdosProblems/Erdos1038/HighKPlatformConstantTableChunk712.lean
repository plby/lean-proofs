import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 712 through 712. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk712

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_712 :
    geometryCheck (table.cell ⟨712, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_712 :
    crossingCheck (table.cell ⟨712, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_712 :
    scalarCheck (table.cell ⟨712, by decide⟩) = true := by
  kernel_decide

theorem certificate_712 :
    Certificate (table.cell ⟨712, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_712,
    crossing_of_check crossingCheck_712,
    scalar_of_check scalarCheck_712⟩

end Erdos1038.HighKPlatformConstantTableChunk712
