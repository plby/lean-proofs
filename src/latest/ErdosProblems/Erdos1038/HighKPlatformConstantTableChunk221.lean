import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 221 through 221. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk221

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_221 :
    geometryCheck (table.cell ⟨221, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_221 :
    crossingCheck (table.cell ⟨221, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_221 :
    scalarCheck (table.cell ⟨221, by decide⟩) = true := by
  kernel_decide

theorem certificate_221 :
    Certificate (table.cell ⟨221, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_221,
    crossing_of_check crossingCheck_221,
    scalar_of_check scalarCheck_221⟩

end Erdos1038.HighKPlatformConstantTableChunk221
