import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 447 through 447. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk447

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_447 :
    geometryCheck (table.cell ⟨447, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_447 :
    crossingCheck (table.cell ⟨447, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_447 :
    scalarCheck (table.cell ⟨447, by decide⟩) = true := by
  kernel_decide

theorem certificate_447 :
    Certificate (table.cell ⟨447, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_447,
    crossing_of_check crossingCheck_447,
    scalar_of_check scalarCheck_447⟩

end Erdos1038.HighKPlatformConstantTableChunk447
