import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 681 through 681. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk681

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_681 :
    geometryCheck (table.cell ⟨681, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_681 :
    crossingCheck (table.cell ⟨681, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_681 :
    scalarCheck (table.cell ⟨681, by decide⟩) = true := by
  kernel_decide

theorem certificate_681 :
    Certificate (table.cell ⟨681, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_681,
    crossing_of_check crossingCheck_681,
    scalar_of_check scalarCheck_681⟩

end Erdos1038.HighKPlatformConstantTableChunk681
