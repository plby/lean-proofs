import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 271 through 271. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk271

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_271 :
    geometryCheck (table.cell ⟨271, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_271 :
    crossingCheck (table.cell ⟨271, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_271 :
    scalarCheck (table.cell ⟨271, by decide⟩) = true := by
  kernel_decide

theorem certificate_271 :
    Certificate (table.cell ⟨271, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_271,
    crossing_of_check crossingCheck_271,
    scalar_of_check scalarCheck_271⟩

end Erdos1038.HighKPlatformConstantTableChunk271
