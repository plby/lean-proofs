import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 427 through 427. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk427

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_427 :
    geometryCheck (table.cell ⟨427, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_427 :
    crossingCheck (table.cell ⟨427, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_427 :
    scalarCheck (table.cell ⟨427, by decide⟩) = true := by
  kernel_decide

theorem certificate_427 :
    Certificate (table.cell ⟨427, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_427,
    crossing_of_check crossingCheck_427,
    scalar_of_check scalarCheck_427⟩

end Erdos1038.HighKPlatformConstantTableChunk427
