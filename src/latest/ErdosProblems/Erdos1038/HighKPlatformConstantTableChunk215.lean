import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 215 through 215. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk215

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_215 :
    geometryCheck (table.cell ⟨215, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_215 :
    crossingCheck (table.cell ⟨215, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_215 :
    scalarCheck (table.cell ⟨215, by decide⟩) = true := by
  kernel_decide

theorem certificate_215 :
    Certificate (table.cell ⟨215, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_215,
    crossing_of_check crossingCheck_215,
    scalar_of_check scalarCheck_215⟩

end Erdos1038.HighKPlatformConstantTableChunk215
