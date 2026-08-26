import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 230 through 230. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk230

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_230 :
    geometryCheck (table.cell ⟨230, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_230 :
    crossingCheck (table.cell ⟨230, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_230 :
    scalarCheck (table.cell ⟨230, by decide⟩) = true := by
  kernel_decide

theorem certificate_230 :
    Certificate (table.cell ⟨230, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_230,
    crossing_of_check crossingCheck_230,
    scalar_of_check scalarCheck_230⟩

end Erdos1038.HighKPlatformConstantTableChunk230
