import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 123 through 123. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk123

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_123 :
    geometryCheck (table.cell ⟨123, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_123 :
    crossingCheck (table.cell ⟨123, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_123 :
    scalarCheck (table.cell ⟨123, by decide⟩) = true := by
  kernel_decide

theorem certificate_123 :
    Certificate (table.cell ⟨123, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_123,
    crossing_of_check crossingCheck_123,
    scalar_of_check scalarCheck_123⟩

end Erdos1038.HighKPlatformConstantTableChunk123
