import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 195 through 195. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk195

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_195 :
    geometryCheck (table.cell ⟨195, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_195 :
    crossingCheck (table.cell ⟨195, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_195 :
    scalarCheck (table.cell ⟨195, by decide⟩) = true := by
  kernel_decide

theorem certificate_195 :
    Certificate (table.cell ⟨195, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_195,
    crossing_of_check crossingCheck_195,
    scalar_of_check scalarCheck_195⟩

end Erdos1038.HighKPlatformConstantTableChunk195
