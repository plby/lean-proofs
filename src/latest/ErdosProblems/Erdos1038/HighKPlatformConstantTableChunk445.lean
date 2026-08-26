import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 445 through 445. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk445

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_445 :
    geometryCheck (table.cell ⟨445, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_445 :
    crossingCheck (table.cell ⟨445, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_445 :
    scalarCheck (table.cell ⟨445, by decide⟩) = true := by
  kernel_decide

theorem certificate_445 :
    Certificate (table.cell ⟨445, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_445,
    crossing_of_check crossingCheck_445,
    scalar_of_check scalarCheck_445⟩

end Erdos1038.HighKPlatformConstantTableChunk445
