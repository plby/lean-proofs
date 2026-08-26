import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 774 through 774. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk774

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_774 :
    geometryCheck (table.cell ⟨774, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_774 :
    crossingCheck (table.cell ⟨774, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_774 :
    scalarCheck (table.cell ⟨774, by decide⟩) = true := by
  kernel_decide

theorem certificate_774 :
    Certificate (table.cell ⟨774, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_774,
    crossing_of_check crossingCheck_774,
    scalar_of_check scalarCheck_774⟩

end Erdos1038.HighKPlatformConstantTableChunk774
