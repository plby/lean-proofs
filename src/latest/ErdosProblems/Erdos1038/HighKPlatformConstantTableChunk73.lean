import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 73 through 73. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk73

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_073 :
    geometryCheck (table.cell ⟨73, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_073 :
    crossingCheck (table.cell ⟨73, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_073 :
    scalarCheck (table.cell ⟨73, by decide⟩) = true := by
  kernel_decide

theorem certificate_073 :
    Certificate (table.cell ⟨73, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_073,
    crossing_of_check crossingCheck_073,
    scalar_of_check scalarCheck_073⟩

end Erdos1038.HighKPlatformConstantTableChunk73
