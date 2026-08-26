import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 171 through 171. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk171

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_171 :
    geometryCheck (table.cell ⟨171, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_171 :
    crossingCheck (table.cell ⟨171, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_171 :
    scalarCheck (table.cell ⟨171, by decide⟩) = true := by
  kernel_decide

theorem certificate_171 :
    Certificate (table.cell ⟨171, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_171,
    crossing_of_check crossingCheck_171,
    scalar_of_check scalarCheck_171⟩

end Erdos1038.HighKPlatformConstantTableChunk171
