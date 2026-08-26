import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 437 through 437. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk437

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_437 :
    geometryCheck (table.cell ⟨437, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_437 :
    crossingCheck (table.cell ⟨437, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_437 :
    scalarCheck (table.cell ⟨437, by decide⟩) = true := by
  kernel_decide

theorem certificate_437 :
    Certificate (table.cell ⟨437, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_437,
    crossing_of_check crossingCheck_437,
    scalar_of_check scalarCheck_437⟩

end Erdos1038.HighKPlatformConstantTableChunk437
