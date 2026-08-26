import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 300 through 300. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk300

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_300 :
    geometryCheck (table.cell ⟨300, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_300 :
    crossingCheck (table.cell ⟨300, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_300 :
    scalarCheck (table.cell ⟨300, by decide⟩) = true := by
  kernel_decide

theorem certificate_300 :
    Certificate (table.cell ⟨300, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_300,
    crossing_of_check crossingCheck_300,
    scalar_of_check scalarCheck_300⟩

end Erdos1038.HighKPlatformConstantTableChunk300
