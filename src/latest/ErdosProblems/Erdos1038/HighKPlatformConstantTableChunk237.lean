import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 237 through 237. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk237

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_237 :
    geometryCheck (table.cell ⟨237, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_237 :
    crossingCheck (table.cell ⟨237, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_237 :
    scalarCheck (table.cell ⟨237, by decide⟩) = true := by
  kernel_decide

theorem certificate_237 :
    Certificate (table.cell ⟨237, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_237,
    crossing_of_check crossingCheck_237,
    scalar_of_check scalarCheck_237⟩

end Erdos1038.HighKPlatformConstantTableChunk237
