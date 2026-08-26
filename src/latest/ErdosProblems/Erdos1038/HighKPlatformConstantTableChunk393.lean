import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 393 through 393. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk393

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_393 :
    geometryCheck (table.cell ⟨393, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_393 :
    crossingCheck (table.cell ⟨393, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_393 :
    scalarCheck (table.cell ⟨393, by decide⟩) = true := by
  kernel_decide

theorem certificate_393 :
    Certificate (table.cell ⟨393, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_393,
    crossing_of_check crossingCheck_393,
    scalar_of_check scalarCheck_393⟩

end Erdos1038.HighKPlatformConstantTableChunk393
