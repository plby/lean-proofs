import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 468 through 468. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk468

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_468 :
    geometryCheck (table.cell ⟨468, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_468 :
    crossingCheck (table.cell ⟨468, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_468 :
    scalarCheck (table.cell ⟨468, by decide⟩) = true := by
  kernel_decide

theorem certificate_468 :
    Certificate (table.cell ⟨468, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_468,
    crossing_of_check crossingCheck_468,
    scalar_of_check scalarCheck_468⟩

end Erdos1038.HighKPlatformConstantTableChunk468
