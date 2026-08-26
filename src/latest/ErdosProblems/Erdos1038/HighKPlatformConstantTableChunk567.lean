import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 567 through 567. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk567

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_567 :
    geometryCheck (table.cell ⟨567, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_567 :
    crossingCheck (table.cell ⟨567, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_567 :
    scalarCheck (table.cell ⟨567, by decide⟩) = true := by
  kernel_decide

theorem certificate_567 :
    Certificate (table.cell ⟨567, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_567,
    crossing_of_check crossingCheck_567,
    scalar_of_check scalarCheck_567⟩

end Erdos1038.HighKPlatformConstantTableChunk567
