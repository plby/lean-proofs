import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 333 through 333. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk333

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_333 :
    geometryCheck (table.cell ⟨333, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_333 :
    crossingCheck (table.cell ⟨333, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_333 :
    scalarCheck (table.cell ⟨333, by decide⟩) = true := by
  kernel_decide

theorem certificate_333 :
    Certificate (table.cell ⟨333, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_333,
    crossing_of_check crossingCheck_333,
    scalar_of_check scalarCheck_333⟩

end Erdos1038.HighKPlatformConstantTableChunk333
