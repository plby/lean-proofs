import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 791 through 791. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk791

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_791 :
    geometryCheck (table.cell ⟨791, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_791 :
    crossingCheck (table.cell ⟨791, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_791 :
    scalarCheck (table.cell ⟨791, by decide⟩) = true := by
  kernel_decide

theorem certificate_791 :
    Certificate (table.cell ⟨791, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_791,
    crossing_of_check crossingCheck_791,
    scalar_of_check scalarCheck_791⟩

end Erdos1038.HighKPlatformConstantTableChunk791
