import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 138 through 138. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk138

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_138 :
    geometryCheck (table.cell ⟨138, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_138 :
    crossingCheck (table.cell ⟨138, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_138 :
    scalarCheck (table.cell ⟨138, by decide⟩) = true := by
  kernel_decide

theorem certificate_138 :
    Certificate (table.cell ⟨138, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_138,
    crossing_of_check crossingCheck_138,
    scalar_of_check scalarCheck_138⟩

end Erdos1038.HighKPlatformConstantTableChunk138
