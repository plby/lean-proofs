import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 555 through 555. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk555

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_555 :
    geometryCheck (table.cell ⟨555, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_555 :
    crossingCheck (table.cell ⟨555, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_555 :
    scalarCheck (table.cell ⟨555, by decide⟩) = true := by
  kernel_decide

theorem certificate_555 :
    Certificate (table.cell ⟨555, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_555,
    crossing_of_check crossingCheck_555,
    scalar_of_check scalarCheck_555⟩

end Erdos1038.HighKPlatformConstantTableChunk555
