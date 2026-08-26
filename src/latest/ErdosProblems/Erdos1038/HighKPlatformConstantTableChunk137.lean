import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 137 through 137. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk137

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_137 :
    geometryCheck (table.cell ⟨137, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_137 :
    crossingCheck (table.cell ⟨137, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_137 :
    scalarCheck (table.cell ⟨137, by decide⟩) = true := by
  kernel_decide

theorem certificate_137 :
    Certificate (table.cell ⟨137, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_137,
    crossing_of_check crossingCheck_137,
    scalar_of_check scalarCheck_137⟩

end Erdos1038.HighKPlatformConstantTableChunk137
