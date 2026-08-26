import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 745 through 745. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk745

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_745 :
    geometryCheck (table.cell ⟨745, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_745 :
    crossingCheck (table.cell ⟨745, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_745 :
    scalarCheck (table.cell ⟨745, by decide⟩) = true := by
  kernel_decide

theorem certificate_745 :
    Certificate (table.cell ⟨745, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_745,
    crossing_of_check crossingCheck_745,
    scalar_of_check scalarCheck_745⟩

end Erdos1038.HighKPlatformConstantTableChunk745
