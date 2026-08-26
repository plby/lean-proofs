import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 397 through 397. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk397

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_397 :
    geometryCheck (table.cell ⟨397, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_397 :
    crossingCheck (table.cell ⟨397, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_397 :
    scalarCheck (table.cell ⟨397, by decide⟩) = true := by
  kernel_decide

theorem certificate_397 :
    Certificate (table.cell ⟨397, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_397,
    crossing_of_check crossingCheck_397,
    scalar_of_check scalarCheck_397⟩

end Erdos1038.HighKPlatformConstantTableChunk397
