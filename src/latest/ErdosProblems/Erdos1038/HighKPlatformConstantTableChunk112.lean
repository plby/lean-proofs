import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 112 through 112. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk112

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_112 :
    geometryCheck (table.cell ⟨112, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_112 :
    crossingCheck (table.cell ⟨112, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_112 :
    scalarCheck (table.cell ⟨112, by decide⟩) = true := by
  kernel_decide

theorem certificate_112 :
    Certificate (table.cell ⟨112, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_112,
    crossing_of_check crossingCheck_112,
    scalar_of_check scalarCheck_112⟩

end Erdos1038.HighKPlatformConstantTableChunk112
