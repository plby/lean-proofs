import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 523 through 523. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk523

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_523 :
    geometryCheck (table.cell ⟨523, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_523 :
    crossingCheck (table.cell ⟨523, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_523 :
    scalarCheck (table.cell ⟨523, by decide⟩) = true := by
  kernel_decide

theorem certificate_523 :
    Certificate (table.cell ⟨523, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_523,
    crossing_of_check crossingCheck_523,
    scalar_of_check scalarCheck_523⟩

end Erdos1038.HighKPlatformConstantTableChunk523
