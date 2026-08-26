import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 223 through 223. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk223

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_223 :
    geometryCheck (table.cell ⟨223, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_223 :
    crossingCheck (table.cell ⟨223, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_223 :
    scalarCheck (table.cell ⟨223, by decide⟩) = true := by
  kernel_decide

theorem certificate_223 :
    Certificate (table.cell ⟨223, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_223,
    crossing_of_check crossingCheck_223,
    scalar_of_check scalarCheck_223⟩

end Erdos1038.HighKPlatformConstantTableChunk223
