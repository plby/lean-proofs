import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 7 through 7. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk07

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_007 :
    geometryCheck (table.cell ⟨7, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_007 :
    crossingCheck (table.cell ⟨7, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_007 :
    scalarCheck (table.cell ⟨7, by decide⟩) = true := by
  kernel_decide

theorem certificate_007 :
    Certificate (table.cell ⟨7, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_007,
    crossing_of_check crossingCheck_007,
    scalar_of_check scalarCheck_007⟩

end Erdos1038.HighKPlatformConstantTableChunk07
