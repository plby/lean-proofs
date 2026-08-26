import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 739 through 739. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk739

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_739 :
    geometryCheck (table.cell ⟨739, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_739 :
    crossingCheck (table.cell ⟨739, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_739 :
    scalarCheck (table.cell ⟨739, by decide⟩) = true := by
  kernel_decide

theorem certificate_739 :
    Certificate (table.cell ⟨739, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_739,
    crossing_of_check crossingCheck_739,
    scalar_of_check scalarCheck_739⟩

end Erdos1038.HighKPlatformConstantTableChunk739
