import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 318 through 318. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk318

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_318 :
    geometryCheck (table.cell ⟨318, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_318 :
    crossingCheck (table.cell ⟨318, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_318 :
    scalarCheck (table.cell ⟨318, by decide⟩) = true := by
  kernel_decide

theorem certificate_318 :
    Certificate (table.cell ⟨318, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_318,
    crossing_of_check crossingCheck_318,
    scalar_of_check scalarCheck_318⟩

end Erdos1038.HighKPlatformConstantTableChunk318
