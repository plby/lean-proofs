import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 801 through 801. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk801

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_801 :
    geometryCheck (table.cell ⟨801, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_801 :
    crossingCheck (table.cell ⟨801, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_801 :
    scalarCheck (table.cell ⟨801, by decide⟩) = true := by
  kernel_decide

theorem certificate_801 :
    Certificate (table.cell ⟨801, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_801,
    crossing_of_check crossingCheck_801,
    scalar_of_check scalarCheck_801⟩

end Erdos1038.HighKPlatformConstantTableChunk801
