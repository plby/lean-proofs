import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 17 through 17. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk17

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_017 :
    geometryCheck (table.cell ⟨17, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_017 :
    crossingCheck (table.cell ⟨17, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_017 :
    scalarCheck (table.cell ⟨17, by decide⟩) = true := by
  kernel_decide

theorem certificate_017 :
    Certificate (table.cell ⟨17, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_017,
    crossing_of_check crossingCheck_017,
    scalar_of_check scalarCheck_017⟩

end Erdos1038.HighKPlatformConstantTableChunk17
