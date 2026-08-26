import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 60 through 60. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk60

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_060 :
    geometryCheck (table.cell ⟨60, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_060 :
    crossingCheck (table.cell ⟨60, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_060 :
    scalarCheck (table.cell ⟨60, by decide⟩) = true := by
  kernel_decide

theorem certificate_060 :
    Certificate (table.cell ⟨60, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_060,
    crossing_of_check crossingCheck_060,
    scalar_of_check scalarCheck_060⟩

end Erdos1038.HighKPlatformConstantTableChunk60
