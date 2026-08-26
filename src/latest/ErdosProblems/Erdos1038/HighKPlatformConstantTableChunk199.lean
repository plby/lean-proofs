import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 199 through 199. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk199

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_199 :
    geometryCheck (table.cell ⟨199, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_199 :
    crossingCheck (table.cell ⟨199, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_199 :
    scalarCheck (table.cell ⟨199, by decide⟩) = true := by
  kernel_decide

theorem certificate_199 :
    Certificate (table.cell ⟨199, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_199,
    crossing_of_check crossingCheck_199,
    scalar_of_check scalarCheck_199⟩

end Erdos1038.HighKPlatformConstantTableChunk199
