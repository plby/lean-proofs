import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 647 through 647. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk647

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_647 :
    geometryCheck (table.cell ⟨647, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_647 :
    crossingCheck (table.cell ⟨647, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_647 :
    scalarCheck (table.cell ⟨647, by decide⟩) = true := by
  kernel_decide

theorem certificate_647 :
    Certificate (table.cell ⟨647, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_647,
    crossing_of_check crossingCheck_647,
    scalar_of_check scalarCheck_647⟩

end Erdos1038.HighKPlatformConstantTableChunk647
