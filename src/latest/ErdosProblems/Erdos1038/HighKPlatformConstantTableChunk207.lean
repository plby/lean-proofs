import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 207 through 207. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk207

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_207 :
    geometryCheck (table.cell ⟨207, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_207 :
    crossingCheck (table.cell ⟨207, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_207 :
    scalarCheck (table.cell ⟨207, by decide⟩) = true := by
  kernel_decide

theorem certificate_207 :
    Certificate (table.cell ⟨207, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_207,
    crossing_of_check crossingCheck_207,
    scalar_of_check scalarCheck_207⟩

end Erdos1038.HighKPlatformConstantTableChunk207
