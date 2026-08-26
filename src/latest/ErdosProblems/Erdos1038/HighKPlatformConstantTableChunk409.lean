import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 409 through 409. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk409

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_409 :
    geometryCheck (table.cell ⟨409, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_409 :
    crossingCheck (table.cell ⟨409, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_409 :
    scalarCheck (table.cell ⟨409, by decide⟩) = true := by
  kernel_decide

theorem certificate_409 :
    Certificate (table.cell ⟨409, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_409,
    crossing_of_check crossingCheck_409,
    scalar_of_check scalarCheck_409⟩

end Erdos1038.HighKPlatformConstantTableChunk409
