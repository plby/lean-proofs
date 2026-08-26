import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 229 through 229. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk229

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_229 :
    geometryCheck (table.cell ⟨229, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_229 :
    crossingCheck (table.cell ⟨229, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_229 :
    scalarCheck (table.cell ⟨229, by decide⟩) = true := by
  kernel_decide

theorem certificate_229 :
    Certificate (table.cell ⟨229, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_229,
    crossing_of_check crossingCheck_229,
    scalar_of_check scalarCheck_229⟩

end Erdos1038.HighKPlatformConstantTableChunk229
