import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 601 through 601. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk601

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_601 :
    geometryCheck (table.cell ⟨601, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_601 :
    crossingCheck (table.cell ⟨601, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_601 :
    scalarCheck (table.cell ⟨601, by decide⟩) = true := by
  kernel_decide

theorem certificate_601 :
    Certificate (table.cell ⟨601, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_601,
    crossing_of_check crossingCheck_601,
    scalar_of_check scalarCheck_601⟩

end Erdos1038.HighKPlatformConstantTableChunk601
