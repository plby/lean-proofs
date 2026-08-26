import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 599 through 599. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk599

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_599 :
    geometryCheck (table.cell ⟨599, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_599 :
    crossingCheck (table.cell ⟨599, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_599 :
    scalarCheck (table.cell ⟨599, by decide⟩) = true := by
  kernel_decide

theorem certificate_599 :
    Certificate (table.cell ⟨599, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_599,
    crossing_of_check crossingCheck_599,
    scalar_of_check scalarCheck_599⟩

end Erdos1038.HighKPlatformConstantTableChunk599
