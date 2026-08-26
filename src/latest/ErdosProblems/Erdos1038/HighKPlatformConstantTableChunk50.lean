import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 50 through 50. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk50

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_050 :
    geometryCheck (table.cell ⟨50, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_050 :
    crossingCheck (table.cell ⟨50, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_050 :
    scalarCheck (table.cell ⟨50, by decide⟩) = true := by
  kernel_decide

theorem certificate_050 :
    Certificate (table.cell ⟨50, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_050,
    crossing_of_check crossingCheck_050,
    scalar_of_check scalarCheck_050⟩

end Erdos1038.HighKPlatformConstantTableChunk50
