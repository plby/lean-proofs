import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 422 through 422. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk422

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_422 :
    geometryCheck (table.cell ⟨422, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_422 :
    crossingCheck (table.cell ⟨422, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_422 :
    scalarCheck (table.cell ⟨422, by decide⟩) = true := by
  kernel_decide

theorem certificate_422 :
    Certificate (table.cell ⟨422, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_422,
    crossing_of_check crossingCheck_422,
    scalar_of_check scalarCheck_422⟩

end Erdos1038.HighKPlatformConstantTableChunk422
