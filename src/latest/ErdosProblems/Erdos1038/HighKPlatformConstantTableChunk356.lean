import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 356 through 356. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk356

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_356 :
    geometryCheck (table.cell ⟨356, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_356 :
    crossingCheck (table.cell ⟨356, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_356 :
    scalarCheck (table.cell ⟨356, by decide⟩) = true := by
  kernel_decide

theorem certificate_356 :
    Certificate (table.cell ⟨356, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_356,
    crossing_of_check crossingCheck_356,
    scalar_of_check scalarCheck_356⟩

end Erdos1038.HighKPlatformConstantTableChunk356
