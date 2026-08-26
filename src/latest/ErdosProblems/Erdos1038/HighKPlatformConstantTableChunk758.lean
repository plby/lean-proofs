import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 758 through 758. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk758

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_758 :
    geometryCheck (table.cell ⟨758, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_758 :
    crossingCheck (table.cell ⟨758, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_758 :
    scalarCheck (table.cell ⟨758, by decide⟩) = true := by
  kernel_decide

theorem certificate_758 :
    Certificate (table.cell ⟨758, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_758,
    crossing_of_check crossingCheck_758,
    scalar_of_check scalarCheck_758⟩

end Erdos1038.HighKPlatformConstantTableChunk758
