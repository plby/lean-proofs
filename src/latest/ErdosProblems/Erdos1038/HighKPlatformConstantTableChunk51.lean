import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 51 through 51. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk51

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_051 :
    geometryCheck (table.cell ⟨51, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_051 :
    crossingCheck (table.cell ⟨51, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_051 :
    scalarCheck (table.cell ⟨51, by decide⟩) = true := by
  kernel_decide

theorem certificate_051 :
    Certificate (table.cell ⟨51, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_051,
    crossing_of_check crossingCheck_051,
    scalar_of_check scalarCheck_051⟩

end Erdos1038.HighKPlatformConstantTableChunk51
