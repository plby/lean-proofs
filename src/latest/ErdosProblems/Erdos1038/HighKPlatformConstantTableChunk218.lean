import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 218 through 218. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk218

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_218 :
    geometryCheck (table.cell ⟨218, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_218 :
    crossingCheck (table.cell ⟨218, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_218 :
    scalarCheck (table.cell ⟨218, by decide⟩) = true := by
  kernel_decide

theorem certificate_218 :
    Certificate (table.cell ⟨218, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_218,
    crossing_of_check crossingCheck_218,
    scalar_of_check scalarCheck_218⟩

end Erdos1038.HighKPlatformConstantTableChunk218
