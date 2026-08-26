import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 472 through 472. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk472

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_472 :
    geometryCheck (table.cell ⟨472, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_472 :
    crossingCheck (table.cell ⟨472, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_472 :
    scalarCheck (table.cell ⟨472, by decide⟩) = true := by
  kernel_decide

theorem certificate_472 :
    Certificate (table.cell ⟨472, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_472,
    crossing_of_check crossingCheck_472,
    scalar_of_check scalarCheck_472⟩

end Erdos1038.HighKPlatformConstantTableChunk472
