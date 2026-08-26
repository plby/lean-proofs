import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 574 through 574. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk574

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_574 :
    geometryCheck (table.cell ⟨574, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_574 :
    crossingCheck (table.cell ⟨574, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_574 :
    scalarCheck (table.cell ⟨574, by decide⟩) = true := by
  kernel_decide

theorem certificate_574 :
    Certificate (table.cell ⟨574, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_574,
    crossing_of_check crossingCheck_574,
    scalar_of_check scalarCheck_574⟩

end Erdos1038.HighKPlatformConstantTableChunk574
