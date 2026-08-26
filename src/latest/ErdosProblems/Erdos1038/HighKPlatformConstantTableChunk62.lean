import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 62 through 62. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk62

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_062 :
    geometryCheck (table.cell ⟨62, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_062 :
    crossingCheck (table.cell ⟨62, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_062 :
    scalarCheck (table.cell ⟨62, by decide⟩) = true := by
  kernel_decide

theorem certificate_062 :
    Certificate (table.cell ⟨62, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_062,
    crossing_of_check crossingCheck_062,
    scalar_of_check scalarCheck_062⟩

end Erdos1038.HighKPlatformConstantTableChunk62
