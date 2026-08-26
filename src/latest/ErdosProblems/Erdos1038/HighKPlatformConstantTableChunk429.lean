import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 429 through 429. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk429

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_429 :
    geometryCheck (table.cell ⟨429, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_429 :
    crossingCheck (table.cell ⟨429, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_429 :
    scalarCheck (table.cell ⟨429, by decide⟩) = true := by
  kernel_decide

theorem certificate_429 :
    Certificate (table.cell ⟨429, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_429,
    crossing_of_check crossingCheck_429,
    scalar_of_check scalarCheck_429⟩

end Erdos1038.HighKPlatformConstantTableChunk429
