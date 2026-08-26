import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 662 through 662. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk662

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_662 :
    geometryCheck (table.cell ⟨662, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_662 :
    crossingCheck (table.cell ⟨662, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_662 :
    scalarCheck (table.cell ⟨662, by decide⟩) = true := by
  kernel_decide

theorem certificate_662 :
    Certificate (table.cell ⟨662, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_662,
    crossing_of_check crossingCheck_662,
    scalar_of_check scalarCheck_662⟩

end Erdos1038.HighKPlatformConstantTableChunk662
