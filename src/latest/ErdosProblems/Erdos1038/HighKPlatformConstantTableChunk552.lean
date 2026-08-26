import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 552 through 552. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk552

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_552 :
    geometryCheck (table.cell ⟨552, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_552 :
    crossingCheck (table.cell ⟨552, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_552 :
    scalarCheck (table.cell ⟨552, by decide⟩) = true := by
  kernel_decide

theorem certificate_552 :
    Certificate (table.cell ⟨552, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_552,
    crossing_of_check crossingCheck_552,
    scalar_of_check scalarCheck_552⟩

end Erdos1038.HighKPlatformConstantTableChunk552
