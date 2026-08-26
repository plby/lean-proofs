import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 511 through 511. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk511

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_511 :
    geometryCheck (table.cell ⟨511, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_511 :
    crossingCheck (table.cell ⟨511, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_511 :
    scalarCheck (table.cell ⟨511, by decide⟩) = true := by
  kernel_decide

theorem certificate_511 :
    Certificate (table.cell ⟨511, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_511,
    crossing_of_check crossingCheck_511,
    scalar_of_check scalarCheck_511⟩

end Erdos1038.HighKPlatformConstantTableChunk511
