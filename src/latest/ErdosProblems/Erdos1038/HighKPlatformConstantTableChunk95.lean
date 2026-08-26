import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 95 through 95. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk95

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_095 :
    geometryCheck (table.cell ⟨95, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_095 :
    crossingCheck (table.cell ⟨95, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_095 :
    scalarCheck (table.cell ⟨95, by decide⟩) = true := by
  kernel_decide

theorem certificate_095 :
    Certificate (table.cell ⟨95, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_095,
    crossing_of_check crossingCheck_095,
    scalar_of_check scalarCheck_095⟩

end Erdos1038.HighKPlatformConstantTableChunk95
