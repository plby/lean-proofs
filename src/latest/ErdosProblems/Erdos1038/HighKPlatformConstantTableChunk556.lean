import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 556 through 556. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk556

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_556 :
    geometryCheck (table.cell ⟨556, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_556 :
    crossingCheck (table.cell ⟨556, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_556 :
    scalarCheck (table.cell ⟨556, by decide⟩) = true := by
  kernel_decide

theorem certificate_556 :
    Certificate (table.cell ⟨556, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_556,
    crossing_of_check crossingCheck_556,
    scalar_of_check scalarCheck_556⟩

end Erdos1038.HighKPlatformConstantTableChunk556
