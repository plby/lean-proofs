import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 667 through 667. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk667

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_667 :
    geometryCheck (table.cell ⟨667, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_667 :
    crossingCheck (table.cell ⟨667, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_667 :
    scalarCheck (table.cell ⟨667, by decide⟩) = true := by
  kernel_decide

theorem certificate_667 :
    Certificate (table.cell ⟨667, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_667,
    crossing_of_check crossingCheck_667,
    scalar_of_check scalarCheck_667⟩

end Erdos1038.HighKPlatformConstantTableChunk667
