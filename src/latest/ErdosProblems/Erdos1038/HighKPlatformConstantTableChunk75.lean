import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 75 through 75. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk75

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_075 :
    geometryCheck (table.cell ⟨75, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_075 :
    crossingCheck (table.cell ⟨75, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_075 :
    scalarCheck (table.cell ⟨75, by decide⟩) = true := by
  kernel_decide

theorem certificate_075 :
    Certificate (table.cell ⟨75, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_075,
    crossing_of_check crossingCheck_075,
    scalar_of_check scalarCheck_075⟩

end Erdos1038.HighKPlatformConstantTableChunk75
