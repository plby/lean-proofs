import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 560 through 560. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk560

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_560 :
    geometryCheck (table.cell ⟨560, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_560 :
    crossingCheck (table.cell ⟨560, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_560 :
    scalarCheck (table.cell ⟨560, by decide⟩) = true := by
  kernel_decide

theorem certificate_560 :
    Certificate (table.cell ⟨560, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_560,
    crossing_of_check crossingCheck_560,
    scalar_of_check scalarCheck_560⟩

end Erdos1038.HighKPlatformConstantTableChunk560
