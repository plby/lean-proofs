import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 239 through 239. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk239

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_239 :
    geometryCheck (table.cell ⟨239, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_239 :
    crossingCheck (table.cell ⟨239, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_239 :
    scalarCheck (table.cell ⟨239, by decide⟩) = true := by
  kernel_decide

theorem certificate_239 :
    Certificate (table.cell ⟨239, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_239,
    crossing_of_check crossingCheck_239,
    scalar_of_check scalarCheck_239⟩

end Erdos1038.HighKPlatformConstantTableChunk239
