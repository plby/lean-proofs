import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 391 through 391. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk391

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_391 :
    geometryCheck (table.cell ⟨391, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_391 :
    crossingCheck (table.cell ⟨391, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_391 :
    scalarCheck (table.cell ⟨391, by decide⟩) = true := by
  kernel_decide

theorem certificate_391 :
    Certificate (table.cell ⟨391, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_391,
    crossing_of_check crossingCheck_391,
    scalar_of_check scalarCheck_391⟩

end Erdos1038.HighKPlatformConstantTableChunk391
