import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 442 through 442. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk442

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_442 :
    geometryCheck (table.cell ⟨442, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_442 :
    crossingCheck (table.cell ⟨442, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_442 :
    scalarCheck (table.cell ⟨442, by decide⟩) = true := by
  kernel_decide

theorem certificate_442 :
    Certificate (table.cell ⟨442, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_442,
    crossing_of_check crossingCheck_442,
    scalar_of_check scalarCheck_442⟩

end Erdos1038.HighKPlatformConstantTableChunk442
