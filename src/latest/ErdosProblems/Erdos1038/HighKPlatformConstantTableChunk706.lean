import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 706 through 706. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk706

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_706 :
    geometryCheck (table.cell ⟨706, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_706 :
    crossingCheck (table.cell ⟨706, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_706 :
    scalarCheck (table.cell ⟨706, by decide⟩) = true := by
  kernel_decide

theorem certificate_706 :
    Certificate (table.cell ⟨706, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_706,
    crossing_of_check crossingCheck_706,
    scalar_of_check scalarCheck_706⟩

end Erdos1038.HighKPlatformConstantTableChunk706
