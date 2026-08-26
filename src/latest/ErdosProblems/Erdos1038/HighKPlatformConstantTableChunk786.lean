import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 786 through 786. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk786

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_786 :
    geometryCheck (table.cell ⟨786, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_786 :
    crossingCheck (table.cell ⟨786, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_786 :
    scalarCheck (table.cell ⟨786, by decide⟩) = true := by
  kernel_decide

theorem certificate_786 :
    Certificate (table.cell ⟨786, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_786,
    crossing_of_check crossingCheck_786,
    scalar_of_check scalarCheck_786⟩

end Erdos1038.HighKPlatformConstantTableChunk786
