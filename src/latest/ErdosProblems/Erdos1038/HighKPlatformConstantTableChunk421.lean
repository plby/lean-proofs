import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 421 through 421. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk421

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_421 :
    geometryCheck (table.cell ⟨421, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_421 :
    crossingCheck (table.cell ⟨421, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_421 :
    scalarCheck (table.cell ⟨421, by decide⟩) = true := by
  kernel_decide

theorem certificate_421 :
    Certificate (table.cell ⟨421, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_421,
    crossing_of_check crossingCheck_421,
    scalar_of_check scalarCheck_421⟩

end Erdos1038.HighKPlatformConstantTableChunk421
