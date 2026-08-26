import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 616 through 616. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk616

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_616 :
    geometryCheck (table.cell ⟨616, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_616 :
    crossingCheck (table.cell ⟨616, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_616 :
    scalarCheck (table.cell ⟨616, by decide⟩) = true := by
  kernel_decide

theorem certificate_616 :
    Certificate (table.cell ⟨616, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_616,
    crossing_of_check crossingCheck_616,
    scalar_of_check scalarCheck_616⟩

end Erdos1038.HighKPlatformConstantTableChunk616
