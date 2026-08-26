import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 713 through 713. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk713

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_713 :
    geometryCheck (table.cell ⟨713, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_713 :
    crossingCheck (table.cell ⟨713, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_713 :
    scalarCheck (table.cell ⟨713, by decide⟩) = true := by
  kernel_decide

theorem certificate_713 :
    Certificate (table.cell ⟨713, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_713,
    crossing_of_check crossingCheck_713,
    scalar_of_check scalarCheck_713⟩

end Erdos1038.HighKPlatformConstantTableChunk713
