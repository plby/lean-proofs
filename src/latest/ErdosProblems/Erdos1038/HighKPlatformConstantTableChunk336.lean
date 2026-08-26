import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 336 through 336. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk336

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_336 :
    geometryCheck (table.cell ⟨336, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_336 :
    crossingCheck (table.cell ⟨336, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_336 :
    scalarCheck (table.cell ⟨336, by decide⟩) = true := by
  kernel_decide

theorem certificate_336 :
    Certificate (table.cell ⟨336, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_336,
    crossing_of_check crossingCheck_336,
    scalar_of_check scalarCheck_336⟩

end Erdos1038.HighKPlatformConstantTableChunk336
