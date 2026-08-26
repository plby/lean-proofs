import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 217 through 217. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk217

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_217 :
    geometryCheck (table.cell ⟨217, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_217 :
    crossingCheck (table.cell ⟨217, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_217 :
    scalarCheck (table.cell ⟨217, by decide⟩) = true := by
  kernel_decide

theorem certificate_217 :
    Certificate (table.cell ⟨217, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_217,
    crossing_of_check crossingCheck_217,
    scalar_of_check scalarCheck_217⟩

end Erdos1038.HighKPlatformConstantTableChunk217
