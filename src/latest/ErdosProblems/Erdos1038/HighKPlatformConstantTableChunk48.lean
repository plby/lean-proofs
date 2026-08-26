import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 48 through 48. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk48

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_048 :
    geometryCheck (table.cell ⟨48, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_048 :
    crossingCheck (table.cell ⟨48, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_048 :
    scalarCheck (table.cell ⟨48, by decide⟩) = true := by
  kernel_decide

theorem certificate_048 :
    Certificate (table.cell ⟨48, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_048,
    crossing_of_check crossingCheck_048,
    scalar_of_check scalarCheck_048⟩

end Erdos1038.HighKPlatformConstantTableChunk48
