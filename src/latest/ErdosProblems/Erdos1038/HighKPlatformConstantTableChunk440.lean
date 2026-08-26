import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 440 through 440. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk440

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_440 :
    geometryCheck (table.cell ⟨440, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_440 :
    crossingCheck (table.cell ⟨440, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_440 :
    scalarCheck (table.cell ⟨440, by decide⟩) = true := by
  kernel_decide

theorem certificate_440 :
    Certificate (table.cell ⟨440, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_440,
    crossing_of_check crossingCheck_440,
    scalar_of_check scalarCheck_440⟩

end Erdos1038.HighKPlatformConstantTableChunk440
