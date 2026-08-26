import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 749 through 749. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk749

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_749 :
    geometryCheck (table.cell ⟨749, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_749 :
    crossingCheck (table.cell ⟨749, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_749 :
    scalarCheck (table.cell ⟨749, by decide⟩) = true := by
  kernel_decide

theorem certificate_749 :
    Certificate (table.cell ⟨749, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_749,
    crossing_of_check crossingCheck_749,
    scalar_of_check scalarCheck_749⟩

end Erdos1038.HighKPlatformConstantTableChunk749
