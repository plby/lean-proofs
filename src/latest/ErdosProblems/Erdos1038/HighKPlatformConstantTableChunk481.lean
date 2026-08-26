import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 481 through 481. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk481

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_481 :
    geometryCheck (table.cell ⟨481, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_481 :
    crossingCheck (table.cell ⟨481, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_481 :
    scalarCheck (table.cell ⟨481, by decide⟩) = true := by
  kernel_decide

theorem certificate_481 :
    Certificate (table.cell ⟨481, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_481,
    crossing_of_check crossingCheck_481,
    scalar_of_check scalarCheck_481⟩

end Erdos1038.HighKPlatformConstantTableChunk481
