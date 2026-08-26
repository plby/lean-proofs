import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 390 through 390. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk390

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_390 :
    geometryCheck (table.cell ⟨390, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_390 :
    crossingCheck (table.cell ⟨390, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_390 :
    scalarCheck (table.cell ⟨390, by decide⟩) = true := by
  kernel_decide

theorem certificate_390 :
    Certificate (table.cell ⟨390, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_390,
    crossing_of_check crossingCheck_390,
    scalar_of_check scalarCheck_390⟩

end Erdos1038.HighKPlatformConstantTableChunk390
