import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 65 through 65. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk65

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_065 :
    geometryCheck (table.cell ⟨65, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_065 :
    crossingCheck (table.cell ⟨65, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_065 :
    scalarCheck (table.cell ⟨65, by decide⟩) = true := by
  kernel_decide

theorem certificate_065 :
    Certificate (table.cell ⟨65, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_065,
    crossing_of_check crossingCheck_065,
    scalar_of_check scalarCheck_065⟩

end Erdos1038.HighKPlatformConstantTableChunk65
