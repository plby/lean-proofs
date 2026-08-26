import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 273 through 273. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk273

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_273 :
    geometryCheck (table.cell ⟨273, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_273 :
    crossingCheck (table.cell ⟨273, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_273 :
    scalarCheck (table.cell ⟨273, by decide⟩) = true := by
  kernel_decide

theorem certificate_273 :
    Certificate (table.cell ⟨273, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_273,
    crossing_of_check crossingCheck_273,
    scalar_of_check scalarCheck_273⟩

end Erdos1038.HighKPlatformConstantTableChunk273
