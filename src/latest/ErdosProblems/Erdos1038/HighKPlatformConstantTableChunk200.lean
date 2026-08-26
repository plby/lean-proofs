import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 200 through 200. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk200

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_200 :
    geometryCheck (table.cell ⟨200, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_200 :
    crossingCheck (table.cell ⟨200, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_200 :
    scalarCheck (table.cell ⟨200, by decide⟩) = true := by
  kernel_decide

theorem certificate_200 :
    Certificate (table.cell ⟨200, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_200,
    crossing_of_check crossingCheck_200,
    scalar_of_check scalarCheck_200⟩

end Erdos1038.HighKPlatformConstantTableChunk200
