import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 343 through 343. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk343

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_343 :
    geometryCheck (table.cell ⟨343, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_343 :
    crossingCheck (table.cell ⟨343, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_343 :
    scalarCheck (table.cell ⟨343, by decide⟩) = true := by
  kernel_decide

theorem certificate_343 :
    Certificate (table.cell ⟨343, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_343,
    crossing_of_check crossingCheck_343,
    scalar_of_check scalarCheck_343⟩

end Erdos1038.HighKPlatformConstantTableChunk343
