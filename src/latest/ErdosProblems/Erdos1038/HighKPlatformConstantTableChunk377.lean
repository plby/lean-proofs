import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 377 through 377. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk377

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_377 :
    geometryCheck (table.cell ⟨377, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_377 :
    crossingCheck (table.cell ⟨377, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_377 :
    scalarCheck (table.cell ⟨377, by decide⟩) = true := by
  kernel_decide

theorem certificate_377 :
    Certificate (table.cell ⟨377, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_377,
    crossing_of_check crossingCheck_377,
    scalar_of_check scalarCheck_377⟩

end Erdos1038.HighKPlatformConstantTableChunk377
