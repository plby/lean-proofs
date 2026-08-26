import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 559 through 559. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk559

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_559 :
    geometryCheck (table.cell ⟨559, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_559 :
    crossingCheck (table.cell ⟨559, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_559 :
    scalarCheck (table.cell ⟨559, by decide⟩) = true := by
  kernel_decide

theorem certificate_559 :
    Certificate (table.cell ⟨559, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_559,
    crossing_of_check crossingCheck_559,
    scalar_of_check scalarCheck_559⟩

end Erdos1038.HighKPlatformConstantTableChunk559
