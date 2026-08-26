import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 311 through 311. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk311

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_311 :
    geometryCheck (table.cell ⟨311, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_311 :
    crossingCheck (table.cell ⟨311, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_311 :
    scalarCheck (table.cell ⟨311, by decide⟩) = true := by
  kernel_decide

theorem certificate_311 :
    Certificate (table.cell ⟨311, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_311,
    crossing_of_check crossingCheck_311,
    scalar_of_check scalarCheck_311⟩

end Erdos1038.HighKPlatformConstantTableChunk311
