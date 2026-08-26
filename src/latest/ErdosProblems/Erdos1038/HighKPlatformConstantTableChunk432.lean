import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 432 through 432. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk432

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_432 :
    geometryCheck (table.cell ⟨432, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_432 :
    crossingCheck (table.cell ⟨432, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_432 :
    scalarCheck (table.cell ⟨432, by decide⟩) = true := by
  kernel_decide

theorem certificate_432 :
    Certificate (table.cell ⟨432, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_432,
    crossing_of_check crossingCheck_432,
    scalar_of_check scalarCheck_432⟩

end Erdos1038.HighKPlatformConstantTableChunk432
