import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 455 through 455. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk455

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_455 :
    geometryCheck (table.cell ⟨455, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_455 :
    crossingCheck (table.cell ⟨455, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_455 :
    scalarCheck (table.cell ⟨455, by decide⟩) = true := by
  kernel_decide

theorem certificate_455 :
    Certificate (table.cell ⟨455, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_455,
    crossing_of_check crossingCheck_455,
    scalar_of_check scalarCheck_455⟩

end Erdos1038.HighKPlatformConstantTableChunk455
