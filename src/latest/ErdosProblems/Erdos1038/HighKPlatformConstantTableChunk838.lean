import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 838 through 838. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk838

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_838 :
    geometryCheck (table.cell ⟨838, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_838 :
    crossingCheck (table.cell ⟨838, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_838 :
    scalarCheck (table.cell ⟨838, by decide⟩) = true := by
  kernel_decide

theorem certificate_838 :
    Certificate (table.cell ⟨838, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_838,
    crossing_of_check crossingCheck_838,
    scalar_of_check scalarCheck_838⟩

end Erdos1038.HighKPlatformConstantTableChunk838
