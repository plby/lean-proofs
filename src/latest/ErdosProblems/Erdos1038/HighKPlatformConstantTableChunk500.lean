import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 500 through 500. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk500

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_500 :
    geometryCheck (table.cell ⟨500, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_500 :
    crossingCheck (table.cell ⟨500, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_500 :
    scalarCheck (table.cell ⟨500, by decide⟩) = true := by
  kernel_decide

theorem certificate_500 :
    Certificate (table.cell ⟨500, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_500,
    crossing_of_check crossingCheck_500,
    scalar_of_check scalarCheck_500⟩

end Erdos1038.HighKPlatformConstantTableChunk500
