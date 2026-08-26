import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 754 through 754. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk754

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_754 :
    geometryCheck (table.cell ⟨754, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_754 :
    crossingCheck (table.cell ⟨754, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_754 :
    scalarCheck (table.cell ⟨754, by decide⟩) = true := by
  kernel_decide

theorem certificate_754 :
    Certificate (table.cell ⟨754, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_754,
    crossing_of_check crossingCheck_754,
    scalar_of_check scalarCheck_754⟩

end Erdos1038.HighKPlatformConstantTableChunk754
