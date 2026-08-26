import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 369 through 369. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk369

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_369 :
    geometryCheck (table.cell ⟨369, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_369 :
    crossingCheck (table.cell ⟨369, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_369 :
    scalarCheck (table.cell ⟨369, by decide⟩) = true := by
  kernel_decide

theorem certificate_369 :
    Certificate (table.cell ⟨369, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_369,
    crossing_of_check crossingCheck_369,
    scalar_of_check scalarCheck_369⟩

end Erdos1038.HighKPlatformConstantTableChunk369
