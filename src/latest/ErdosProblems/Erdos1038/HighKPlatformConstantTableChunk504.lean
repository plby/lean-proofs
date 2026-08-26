import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 504 through 504. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk504

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_504 :
    geometryCheck (table.cell ⟨504, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_504 :
    crossingCheck (table.cell ⟨504, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_504 :
    scalarCheck (table.cell ⟨504, by decide⟩) = true := by
  kernel_decide

theorem certificate_504 :
    Certificate (table.cell ⟨504, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_504,
    crossing_of_check crossingCheck_504,
    scalar_of_check scalarCheck_504⟩

end Erdos1038.HighKPlatformConstantTableChunk504
