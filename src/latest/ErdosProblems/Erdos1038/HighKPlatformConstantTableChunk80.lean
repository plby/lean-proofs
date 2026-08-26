import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 80 through 80. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk80

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_080 :
    geometryCheck (table.cell ⟨80, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_080 :
    crossingCheck (table.cell ⟨80, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_080 :
    scalarCheck (table.cell ⟨80, by decide⟩) = true := by
  kernel_decide

theorem certificate_080 :
    Certificate (table.cell ⟨80, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_080,
    crossing_of_check crossingCheck_080,
    scalar_of_check scalarCheck_080⟩

end Erdos1038.HighKPlatformConstantTableChunk80
