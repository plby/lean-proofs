import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 133 through 133. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk133

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_133 :
    geometryCheck (table.cell ⟨133, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_133 :
    crossingCheck (table.cell ⟨133, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_133 :
    scalarCheck (table.cell ⟨133, by decide⟩) = true := by
  kernel_decide

theorem certificate_133 :
    Certificate (table.cell ⟨133, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_133,
    crossing_of_check crossingCheck_133,
    scalar_of_check scalarCheck_133⟩

end Erdos1038.HighKPlatformConstantTableChunk133
