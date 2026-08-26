import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 143 through 143. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk143

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_143 :
    geometryCheck (table.cell ⟨143, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_143 :
    crossingCheck (table.cell ⟨143, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_143 :
    scalarCheck (table.cell ⟨143, by decide⟩) = true := by
  kernel_decide

theorem certificate_143 :
    Certificate (table.cell ⟨143, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_143,
    crossing_of_check crossingCheck_143,
    scalar_of_check scalarCheck_143⟩

end Erdos1038.HighKPlatformConstantTableChunk143
