import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 186 through 186. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk186

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_186 :
    geometryCheck (table.cell ⟨186, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_186 :
    crossingCheck (table.cell ⟨186, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_186 :
    scalarCheck (table.cell ⟨186, by decide⟩) = true := by
  kernel_decide

theorem certificate_186 :
    Certificate (table.cell ⟨186, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_186,
    crossing_of_check crossingCheck_186,
    scalar_of_check scalarCheck_186⟩

end Erdos1038.HighKPlatformConstantTableChunk186
