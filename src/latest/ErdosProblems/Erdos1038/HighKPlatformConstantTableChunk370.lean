import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 370 through 370. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk370

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_370 :
    geometryCheck (table.cell ⟨370, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_370 :
    crossingCheck (table.cell ⟨370, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_370 :
    scalarCheck (table.cell ⟨370, by decide⟩) = true := by
  kernel_decide

theorem certificate_370 :
    Certificate (table.cell ⟨370, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_370,
    crossing_of_check crossingCheck_370,
    scalar_of_check scalarCheck_370⟩

end Erdos1038.HighKPlatformConstantTableChunk370
