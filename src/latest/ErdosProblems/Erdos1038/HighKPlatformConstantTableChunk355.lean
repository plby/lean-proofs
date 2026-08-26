import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 355 through 355. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk355

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_355 :
    geometryCheck (table.cell ⟨355, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_355 :
    crossingCheck (table.cell ⟨355, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_355 :
    scalarCheck (table.cell ⟨355, by decide⟩) = true := by
  kernel_decide

theorem certificate_355 :
    Certificate (table.cell ⟨355, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_355,
    crossing_of_check crossingCheck_355,
    scalar_of_check scalarCheck_355⟩

end Erdos1038.HighKPlatformConstantTableChunk355
