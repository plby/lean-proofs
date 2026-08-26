import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 349 through 349. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk349

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_349 :
    geometryCheck (table.cell ⟨349, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_349 :
    crossingCheck (table.cell ⟨349, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_349 :
    scalarCheck (table.cell ⟨349, by decide⟩) = true := by
  kernel_decide

theorem certificate_349 :
    Certificate (table.cell ⟨349, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_349,
    crossing_of_check crossingCheck_349,
    scalar_of_check scalarCheck_349⟩

end Erdos1038.HighKPlatformConstantTableChunk349
