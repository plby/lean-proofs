import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 755 through 755. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk755

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_755 :
    geometryCheck (table.cell ⟨755, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_755 :
    crossingCheck (table.cell ⟨755, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_755 :
    scalarCheck (table.cell ⟨755, by decide⟩) = true := by
  kernel_decide

theorem certificate_755 :
    Certificate (table.cell ⟨755, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_755,
    crossing_of_check crossingCheck_755,
    scalar_of_check scalarCheck_755⟩

end Erdos1038.HighKPlatformConstantTableChunk755
