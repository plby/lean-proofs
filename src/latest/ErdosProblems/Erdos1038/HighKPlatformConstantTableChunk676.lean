import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 676 through 676. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk676

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_676 :
    geometryCheck (table.cell ⟨676, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_676 :
    crossingCheck (table.cell ⟨676, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_676 :
    scalarCheck (table.cell ⟨676, by decide⟩) = true := by
  kernel_decide

theorem certificate_676 :
    Certificate (table.cell ⟨676, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_676,
    crossing_of_check crossingCheck_676,
    scalar_of_check scalarCheck_676⟩

end Erdos1038.HighKPlatformConstantTableChunk676
