import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 100 through 100. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk100

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_100 :
    geometryCheck (table.cell ⟨100, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_100 :
    crossingCheck (table.cell ⟨100, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_100 :
    scalarCheck (table.cell ⟨100, by decide⟩) = true := by
  kernel_decide

theorem certificate_100 :
    Certificate (table.cell ⟨100, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_100,
    crossing_of_check crossingCheck_100,
    scalar_of_check scalarCheck_100⟩

end Erdos1038.HighKPlatformConstantTableChunk100
