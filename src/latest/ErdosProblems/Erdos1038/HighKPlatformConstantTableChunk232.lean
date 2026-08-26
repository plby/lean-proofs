import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 232 through 232. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk232

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_232 :
    geometryCheck (table.cell ⟨232, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_232 :
    crossingCheck (table.cell ⟨232, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_232 :
    scalarCheck (table.cell ⟨232, by decide⟩) = true := by
  kernel_decide

theorem certificate_232 :
    Certificate (table.cell ⟨232, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_232,
    crossing_of_check crossingCheck_232,
    scalar_of_check scalarCheck_232⟩

end Erdos1038.HighKPlatformConstantTableChunk232
