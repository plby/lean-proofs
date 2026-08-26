import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 466 through 466. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk466

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_466 :
    geometryCheck (table.cell ⟨466, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_466 :
    crossingCheck (table.cell ⟨466, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_466 :
    scalarCheck (table.cell ⟨466, by decide⟩) = true := by
  kernel_decide

theorem certificate_466 :
    Certificate (table.cell ⟨466, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_466,
    crossing_of_check crossingCheck_466,
    scalar_of_check scalarCheck_466⟩

end Erdos1038.HighKPlatformConstantTableChunk466
