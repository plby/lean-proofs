import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 252 through 252. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk252

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_252 :
    geometryCheck (table.cell ⟨252, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_252 :
    crossingCheck (table.cell ⟨252, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_252 :
    scalarCheck (table.cell ⟨252, by decide⟩) = true := by
  kernel_decide

theorem certificate_252 :
    Certificate (table.cell ⟨252, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_252,
    crossing_of_check crossingCheck_252,
    scalar_of_check scalarCheck_252⟩

end Erdos1038.HighKPlatformConstantTableChunk252
