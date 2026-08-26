import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 78 through 78. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk78

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_078 :
    geometryCheck (table.cell ⟨78, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_078 :
    crossingCheck (table.cell ⟨78, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_078 :
    scalarCheck (table.cell ⟨78, by decide⟩) = true := by
  kernel_decide

theorem certificate_078 :
    Certificate (table.cell ⟨78, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_078,
    crossing_of_check crossingCheck_078,
    scalar_of_check scalarCheck_078⟩

end Erdos1038.HighKPlatformConstantTableChunk78
