import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 87 through 87. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk87

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_087 :
    geometryCheck (table.cell ⟨87, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_087 :
    crossingCheck (table.cell ⟨87, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_087 :
    scalarCheck (table.cell ⟨87, by decide⟩) = true := by
  kernel_decide

theorem certificate_087 :
    Certificate (table.cell ⟨87, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_087,
    crossing_of_check crossingCheck_087,
    scalar_of_check scalarCheck_087⟩

end Erdos1038.HighKPlatformConstantTableChunk87
