import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 150 through 150. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk150

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_150 :
    geometryCheck (table.cell ⟨150, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_150 :
    crossingCheck (table.cell ⟨150, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_150 :
    scalarCheck (table.cell ⟨150, by decide⟩) = true := by
  kernel_decide

theorem certificate_150 :
    Certificate (table.cell ⟨150, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_150,
    crossing_of_check crossingCheck_150,
    scalar_of_check scalarCheck_150⟩

end Erdos1038.HighKPlatformConstantTableChunk150
