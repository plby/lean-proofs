import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 688 through 688. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk688

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_688 :
    geometryCheck (table.cell ⟨688, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_688 :
    crossingCheck (table.cell ⟨688, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_688 :
    scalarCheck (table.cell ⟨688, by decide⟩) = true := by
  kernel_decide

theorem certificate_688 :
    Certificate (table.cell ⟨688, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_688,
    crossing_of_check crossingCheck_688,
    scalar_of_check scalarCheck_688⟩

end Erdos1038.HighKPlatformConstantTableChunk688
