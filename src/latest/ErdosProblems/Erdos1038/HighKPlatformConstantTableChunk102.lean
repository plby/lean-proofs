import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 102 through 102. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk102

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_102 :
    geometryCheck (table.cell ⟨102, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_102 :
    crossingCheck (table.cell ⟨102, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_102 :
    scalarCheck (table.cell ⟨102, by decide⟩) = true := by
  kernel_decide

theorem certificate_102 :
    Certificate (table.cell ⟨102, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_102,
    crossing_of_check crossingCheck_102,
    scalar_of_check scalarCheck_102⟩

end Erdos1038.HighKPlatformConstantTableChunk102
