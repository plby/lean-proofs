import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 420 through 420. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk420

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_420 :
    geometryCheck (table.cell ⟨420, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_420 :
    crossingCheck (table.cell ⟨420, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_420 :
    scalarCheck (table.cell ⟨420, by decide⟩) = true := by
  kernel_decide

theorem certificate_420 :
    Certificate (table.cell ⟨420, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_420,
    crossing_of_check crossingCheck_420,
    scalar_of_check scalarCheck_420⟩

end Erdos1038.HighKPlatformConstantTableChunk420
