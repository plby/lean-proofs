import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 82 through 82. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk82

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_082 :
    geometryCheck (table.cell ⟨82, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_082 :
    crossingCheck (table.cell ⟨82, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_082 :
    scalarCheck (table.cell ⟨82, by decide⟩) = true := by
  kernel_decide

theorem certificate_082 :
    Certificate (table.cell ⟨82, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_082,
    crossing_of_check crossingCheck_082,
    scalar_of_check scalarCheck_082⟩

end Erdos1038.HighKPlatformConstantTableChunk82
