import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 122 through 122. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk122

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_122 :
    geometryCheck (table.cell ⟨122, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_122 :
    crossingCheck (table.cell ⟨122, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_122 :
    scalarCheck (table.cell ⟨122, by decide⟩) = true := by
  kernel_decide

theorem certificate_122 :
    Certificate (table.cell ⟨122, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_122,
    crossing_of_check crossingCheck_122,
    scalar_of_check scalarCheck_122⟩

end Erdos1038.HighKPlatformConstantTableChunk122
