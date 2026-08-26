import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 551 through 551. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk551

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_551 :
    geometryCheck (table.cell ⟨551, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_551 :
    crossingCheck (table.cell ⟨551, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_551 :
    scalarCheck (table.cell ⟨551, by decide⟩) = true := by
  kernel_decide

theorem certificate_551 :
    Certificate (table.cell ⟨551, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_551,
    crossing_of_check crossingCheck_551,
    scalar_of_check scalarCheck_551⟩

end Erdos1038.HighKPlatformConstantTableChunk551
