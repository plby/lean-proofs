import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 10 through 10. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk10

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_010 :
    geometryCheck (table.cell ⟨10, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_010 :
    crossingCheck (table.cell ⟨10, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_010 :
    scalarCheck (table.cell ⟨10, by decide⟩) = true := by
  kernel_decide

theorem certificate_010 :
    Certificate (table.cell ⟨10, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_010,
    crossing_of_check crossingCheck_010,
    scalar_of_check scalarCheck_010⟩

end Erdos1038.HighKPlatformConstantTableChunk10
