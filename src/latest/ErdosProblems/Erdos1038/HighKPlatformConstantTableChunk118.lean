import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 118 through 118. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk118

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_118 :
    geometryCheck (table.cell ⟨118, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_118 :
    crossingCheck (table.cell ⟨118, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_118 :
    scalarCheck (table.cell ⟨118, by decide⟩) = true := by
  kernel_decide

theorem certificate_118 :
    Certificate (table.cell ⟨118, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_118,
    crossing_of_check crossingCheck_118,
    scalar_of_check scalarCheck_118⟩

end Erdos1038.HighKPlatformConstantTableChunk118
