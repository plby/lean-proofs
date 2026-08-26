import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 40 through 40. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk40

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_040 :
    geometryCheck (table.cell ⟨40, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_040 :
    crossingCheck (table.cell ⟨40, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_040 :
    scalarCheck (table.cell ⟨40, by decide⟩) = true := by
  kernel_decide

theorem certificate_040 :
    Certificate (table.cell ⟨40, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_040,
    crossing_of_check crossingCheck_040,
    scalar_of_check scalarCheck_040⟩

end Erdos1038.HighKPlatformConstantTableChunk40
