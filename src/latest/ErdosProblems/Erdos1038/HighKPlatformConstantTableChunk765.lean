import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 765 through 765. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk765

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_765 :
    geometryCheck (table.cell ⟨765, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_765 :
    crossingCheck (table.cell ⟨765, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_765 :
    scalarCheck (table.cell ⟨765, by decide⟩) = true := by
  kernel_decide

theorem certificate_765 :
    Certificate (table.cell ⟨765, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_765,
    crossing_of_check crossingCheck_765,
    scalar_of_check scalarCheck_765⟩

end Erdos1038.HighKPlatformConstantTableChunk765
