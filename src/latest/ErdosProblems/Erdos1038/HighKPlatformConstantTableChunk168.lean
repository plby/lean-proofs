import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 168 through 168. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk168

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_168 :
    geometryCheck (table.cell ⟨168, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_168 :
    crossingCheck (table.cell ⟨168, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_168 :
    scalarCheck (table.cell ⟨168, by decide⟩) = true := by
  kernel_decide

theorem certificate_168 :
    Certificate (table.cell ⟨168, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_168,
    crossing_of_check crossingCheck_168,
    scalar_of_check scalarCheck_168⟩

end Erdos1038.HighKPlatformConstantTableChunk168
