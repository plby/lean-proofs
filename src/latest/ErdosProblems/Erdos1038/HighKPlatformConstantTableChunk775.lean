import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 775 through 775. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk775

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_775 :
    geometryCheck (table.cell ⟨775, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_775 :
    crossingCheck (table.cell ⟨775, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_775 :
    scalarCheck (table.cell ⟨775, by decide⟩) = true := by
  kernel_decide

theorem certificate_775 :
    Certificate (table.cell ⟨775, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_775,
    crossing_of_check crossingCheck_775,
    scalar_of_check scalarCheck_775⟩

end Erdos1038.HighKPlatformConstantTableChunk775
