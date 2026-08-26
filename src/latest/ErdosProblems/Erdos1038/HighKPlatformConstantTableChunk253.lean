import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 253 through 253. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk253

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_253 :
    geometryCheck (table.cell ⟨253, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_253 :
    crossingCheck (table.cell ⟨253, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_253 :
    scalarCheck (table.cell ⟨253, by decide⟩) = true := by
  kernel_decide

theorem certificate_253 :
    Certificate (table.cell ⟨253, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_253,
    crossing_of_check crossingCheck_253,
    scalar_of_check scalarCheck_253⟩

end Erdos1038.HighKPlatformConstantTableChunk253
