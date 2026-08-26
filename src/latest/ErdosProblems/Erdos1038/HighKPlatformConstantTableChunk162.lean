import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 162 through 162. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk162

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_162 :
    geometryCheck (table.cell ⟨162, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_162 :
    crossingCheck (table.cell ⟨162, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_162 :
    scalarCheck (table.cell ⟨162, by decide⟩) = true := by
  kernel_decide

theorem certificate_162 :
    Certificate (table.cell ⟨162, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_162,
    crossing_of_check crossingCheck_162,
    scalar_of_check scalarCheck_162⟩

end Erdos1038.HighKPlatformConstantTableChunk162
