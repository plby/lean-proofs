import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 576 through 576. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk576

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_576 :
    geometryCheck (table.cell ⟨576, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_576 :
    crossingCheck (table.cell ⟨576, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_576 :
    scalarCheck (table.cell ⟨576, by decide⟩) = true := by
  kernel_decide

theorem certificate_576 :
    Certificate (table.cell ⟨576, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_576,
    crossing_of_check crossingCheck_576,
    scalar_of_check scalarCheck_576⟩

end Erdos1038.HighKPlatformConstantTableChunk576
