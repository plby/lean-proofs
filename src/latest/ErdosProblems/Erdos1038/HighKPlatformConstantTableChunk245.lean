import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 245 through 245. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk245

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_245 :
    geometryCheck (table.cell ⟨245, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_245 :
    crossingCheck (table.cell ⟨245, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_245 :
    scalarCheck (table.cell ⟨245, by decide⟩) = true := by
  kernel_decide

theorem certificate_245 :
    Certificate (table.cell ⟨245, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_245,
    crossing_of_check crossingCheck_245,
    scalar_of_check scalarCheck_245⟩

end Erdos1038.HighKPlatformConstantTableChunk245
