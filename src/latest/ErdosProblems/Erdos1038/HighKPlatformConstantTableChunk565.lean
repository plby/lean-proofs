import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 565 through 565. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk565

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_565 :
    geometryCheck (table.cell ⟨565, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_565 :
    crossingCheck (table.cell ⟨565, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_565 :
    scalarCheck (table.cell ⟨565, by decide⟩) = true := by
  kernel_decide

theorem certificate_565 :
    Certificate (table.cell ⟨565, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_565,
    crossing_of_check crossingCheck_565,
    scalar_of_check scalarCheck_565⟩

end Erdos1038.HighKPlatformConstantTableChunk565
