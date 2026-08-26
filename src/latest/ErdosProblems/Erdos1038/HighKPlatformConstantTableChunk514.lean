import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 514 through 514. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk514

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_514 :
    geometryCheck (table.cell ⟨514, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_514 :
    crossingCheck (table.cell ⟨514, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_514 :
    scalarCheck (table.cell ⟨514, by decide⟩) = true := by
  kernel_decide

theorem certificate_514 :
    Certificate (table.cell ⟨514, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_514,
    crossing_of_check crossingCheck_514,
    scalar_of_check scalarCheck_514⟩

end Erdos1038.HighKPlatformConstantTableChunk514
