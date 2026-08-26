import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 787 through 787. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk787

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_787 :
    geometryCheck (table.cell ⟨787, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_787 :
    crossingCheck (table.cell ⟨787, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_787 :
    scalarCheck (table.cell ⟨787, by decide⟩) = true := by
  kernel_decide

theorem certificate_787 :
    Certificate (table.cell ⟨787, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_787,
    crossing_of_check crossingCheck_787,
    scalar_of_check scalarCheck_787⟩

end Erdos1038.HighKPlatformConstantTableChunk787
