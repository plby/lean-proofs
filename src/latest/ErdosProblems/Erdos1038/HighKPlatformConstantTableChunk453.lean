import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 453 through 453. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk453

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_453 :
    geometryCheck (table.cell ⟨453, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_453 :
    crossingCheck (table.cell ⟨453, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_453 :
    scalarCheck (table.cell ⟨453, by decide⟩) = true := by
  kernel_decide

theorem certificate_453 :
    Certificate (table.cell ⟨453, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_453,
    crossing_of_check crossingCheck_453,
    scalar_of_check scalarCheck_453⟩

end Erdos1038.HighKPlatformConstantTableChunk453
