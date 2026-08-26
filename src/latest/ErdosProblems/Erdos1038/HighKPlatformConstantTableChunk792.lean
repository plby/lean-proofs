import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 792 through 792. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk792

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_792 :
    geometryCheck (table.cell ⟨792, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_792 :
    crossingCheck (table.cell ⟨792, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_792 :
    scalarCheck (table.cell ⟨792, by decide⟩) = true := by
  kernel_decide

theorem certificate_792 :
    Certificate (table.cell ⟨792, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_792,
    crossing_of_check crossingCheck_792,
    scalar_of_check scalarCheck_792⟩

end Erdos1038.HighKPlatformConstantTableChunk792
