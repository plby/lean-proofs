import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 211 through 211. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk211

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_211 :
    geometryCheck (table.cell ⟨211, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_211 :
    crossingCheck (table.cell ⟨211, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_211 :
    scalarCheck (table.cell ⟨211, by decide⟩) = true := by
  kernel_decide

theorem certificate_211 :
    Certificate (table.cell ⟨211, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_211,
    crossing_of_check crossingCheck_211,
    scalar_of_check scalarCheck_211⟩

end Erdos1038.HighKPlatformConstantTableChunk211
