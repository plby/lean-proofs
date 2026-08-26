import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 25 through 25. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk25

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_025 :
    geometryCheck (table.cell ⟨25, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_025 :
    crossingCheck (table.cell ⟨25, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_025 :
    scalarCheck (table.cell ⟨25, by decide⟩) = true := by
  kernel_decide

theorem certificate_025 :
    Certificate (table.cell ⟨25, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_025,
    crossing_of_check crossingCheck_025,
    scalar_of_check scalarCheck_025⟩

end Erdos1038.HighKPlatformConstantTableChunk25
