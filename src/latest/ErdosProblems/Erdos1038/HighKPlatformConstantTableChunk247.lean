import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 247 through 247. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk247

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_247 :
    geometryCheck (table.cell ⟨247, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_247 :
    crossingCheck (table.cell ⟨247, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_247 :
    scalarCheck (table.cell ⟨247, by decide⟩) = true := by
  kernel_decide

theorem certificate_247 :
    Certificate (table.cell ⟨247, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_247,
    crossing_of_check crossingCheck_247,
    scalar_of_check scalarCheck_247⟩

end Erdos1038.HighKPlatformConstantTableChunk247
