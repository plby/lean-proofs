import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 58 through 58. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk58

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_058 :
    geometryCheck (table.cell ⟨58, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_058 :
    crossingCheck (table.cell ⟨58, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_058 :
    scalarCheck (table.cell ⟨58, by decide⟩) = true := by
  kernel_decide

theorem certificate_058 :
    Certificate (table.cell ⟨58, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_058,
    crossing_of_check crossingCheck_058,
    scalar_of_check scalarCheck_058⟩

end Erdos1038.HighKPlatformConstantTableChunk58
