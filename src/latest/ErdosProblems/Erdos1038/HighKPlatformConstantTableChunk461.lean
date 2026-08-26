import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 461 through 461. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk461

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_461 :
    geometryCheck (table.cell ⟨461, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_461 :
    crossingCheck (table.cell ⟨461, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_461 :
    scalarCheck (table.cell ⟨461, by decide⟩) = true := by
  kernel_decide

theorem certificate_461 :
    Certificate (table.cell ⟨461, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_461,
    crossing_of_check crossingCheck_461,
    scalar_of_check scalarCheck_461⟩

end Erdos1038.HighKPlatformConstantTableChunk461
