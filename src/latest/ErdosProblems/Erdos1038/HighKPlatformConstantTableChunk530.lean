import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 530 through 530. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk530

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_530 :
    geometryCheck (table.cell ⟨530, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_530 :
    crossingCheck (table.cell ⟨530, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_530 :
    scalarCheck (table.cell ⟨530, by decide⟩) = true := by
  kernel_decide

theorem certificate_530 :
    Certificate (table.cell ⟨530, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_530,
    crossing_of_check crossingCheck_530,
    scalar_of_check scalarCheck_530⟩

end Erdos1038.HighKPlatformConstantTableChunk530
