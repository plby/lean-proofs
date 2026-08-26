import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 319 through 319. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk319

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_319 :
    geometryCheck (table.cell ⟨319, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_319 :
    crossingCheck (table.cell ⟨319, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_319 :
    scalarCheck (table.cell ⟨319, by decide⟩) = true := by
  kernel_decide

theorem certificate_319 :
    Certificate (table.cell ⟨319, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_319,
    crossing_of_check crossingCheck_319,
    scalar_of_check scalarCheck_319⟩

end Erdos1038.HighKPlatformConstantTableChunk319
