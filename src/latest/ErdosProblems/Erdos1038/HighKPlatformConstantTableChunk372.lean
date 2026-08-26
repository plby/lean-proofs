import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 372 through 372. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk372

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_372 :
    geometryCheck (table.cell ⟨372, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_372 :
    crossingCheck (table.cell ⟨372, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_372 :
    scalarCheck (table.cell ⟨372, by decide⟩) = true := by
  kernel_decide

theorem certificate_372 :
    Certificate (table.cell ⟨372, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_372,
    crossing_of_check crossingCheck_372,
    scalar_of_check scalarCheck_372⟩

end Erdos1038.HighKPlatformConstantTableChunk372
