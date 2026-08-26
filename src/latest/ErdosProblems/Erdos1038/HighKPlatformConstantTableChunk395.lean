import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 395 through 395. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk395

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_395 :
    geometryCheck (table.cell ⟨395, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_395 :
    crossingCheck (table.cell ⟨395, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_395 :
    scalarCheck (table.cell ⟨395, by decide⟩) = true := by
  kernel_decide

theorem certificate_395 :
    Certificate (table.cell ⟨395, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_395,
    crossing_of_check crossingCheck_395,
    scalar_of_check scalarCheck_395⟩

end Erdos1038.HighKPlatformConstantTableChunk395
