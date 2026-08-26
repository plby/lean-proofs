import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 668 through 668. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk668

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_668 :
    geometryCheck (table.cell ⟨668, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_668 :
    crossingCheck (table.cell ⟨668, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_668 :
    scalarCheck (table.cell ⟨668, by decide⟩) = true := by
  kernel_decide

theorem certificate_668 :
    Certificate (table.cell ⟨668, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_668,
    crossing_of_check crossingCheck_668,
    scalar_of_check scalarCheck_668⟩

end Erdos1038.HighKPlatformConstantTableChunk668
