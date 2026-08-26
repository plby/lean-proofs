import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 544 through 544. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk544

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_544 :
    geometryCheck (table.cell ⟨544, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_544 :
    crossingCheck (table.cell ⟨544, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_544 :
    scalarCheck (table.cell ⟨544, by decide⟩) = true := by
  kernel_decide

theorem certificate_544 :
    Certificate (table.cell ⟨544, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_544,
    crossing_of_check crossingCheck_544,
    scalar_of_check scalarCheck_544⟩

end Erdos1038.HighKPlatformConstantTableChunk544
