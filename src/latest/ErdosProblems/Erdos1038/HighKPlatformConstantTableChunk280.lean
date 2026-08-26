import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 280 through 280. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk280

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_280 :
    geometryCheck (table.cell ⟨280, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_280 :
    crossingCheck (table.cell ⟨280, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_280 :
    scalarCheck (table.cell ⟨280, by decide⟩) = true := by
  kernel_decide

theorem certificate_280 :
    Certificate (table.cell ⟨280, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_280,
    crossing_of_check crossingCheck_280,
    scalar_of_check scalarCheck_280⟩

end Erdos1038.HighKPlatformConstantTableChunk280
