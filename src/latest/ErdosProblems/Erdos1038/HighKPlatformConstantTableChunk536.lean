import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 536 through 536. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk536

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_536 :
    geometryCheck (table.cell ⟨536, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_536 :
    crossingCheck (table.cell ⟨536, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_536 :
    scalarCheck (table.cell ⟨536, by decide⟩) = true := by
  kernel_decide

theorem certificate_536 :
    Certificate (table.cell ⟨536, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_536,
    crossing_of_check crossingCheck_536,
    scalar_of_check scalarCheck_536⟩

end Erdos1038.HighKPlatformConstantTableChunk536
