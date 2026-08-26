import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 158 through 158. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk158

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_158 :
    geometryCheck (table.cell ⟨158, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_158 :
    crossingCheck (table.cell ⟨158, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_158 :
    scalarCheck (table.cell ⟨158, by decide⟩) = true := by
  kernel_decide

theorem certificate_158 :
    Certificate (table.cell ⟨158, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_158,
    crossing_of_check crossingCheck_158,
    scalar_of_check scalarCheck_158⟩

end Erdos1038.HighKPlatformConstantTableChunk158
