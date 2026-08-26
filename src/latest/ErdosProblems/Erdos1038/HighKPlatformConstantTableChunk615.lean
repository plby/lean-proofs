import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 615 through 615. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk615

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_615 :
    geometryCheck (table.cell ⟨615, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_615 :
    crossingCheck (table.cell ⟨615, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_615 :
    scalarCheck (table.cell ⟨615, by decide⟩) = true := by
  kernel_decide

theorem certificate_615 :
    Certificate (table.cell ⟨615, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_615,
    crossing_of_check crossingCheck_615,
    scalar_of_check scalarCheck_615⟩

end Erdos1038.HighKPlatformConstantTableChunk615
