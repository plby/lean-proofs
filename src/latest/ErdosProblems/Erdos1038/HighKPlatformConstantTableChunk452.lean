import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 452 through 452. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk452

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_452 :
    geometryCheck (table.cell ⟨452, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_452 :
    crossingCheck (table.cell ⟨452, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_452 :
    scalarCheck (table.cell ⟨452, by decide⟩) = true := by
  kernel_decide

theorem certificate_452 :
    Certificate (table.cell ⟨452, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_452,
    crossing_of_check crossingCheck_452,
    scalar_of_check scalarCheck_452⟩

end Erdos1038.HighKPlatformConstantTableChunk452
