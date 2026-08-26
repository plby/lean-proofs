import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 176 through 176. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk176

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_176 :
    geometryCheck (table.cell ⟨176, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_176 :
    crossingCheck (table.cell ⟨176, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_176 :
    scalarCheck (table.cell ⟨176, by decide⟩) = true := by
  kernel_decide

theorem certificate_176 :
    Certificate (table.cell ⟨176, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_176,
    crossing_of_check crossingCheck_176,
    scalar_of_check scalarCheck_176⟩

end Erdos1038.HighKPlatformConstantTableChunk176
