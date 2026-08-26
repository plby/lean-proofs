import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 360 through 360. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk360

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_360 :
    geometryCheck (table.cell ⟨360, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_360 :
    crossingCheck (table.cell ⟨360, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_360 :
    scalarCheck (table.cell ⟨360, by decide⟩) = true := by
  kernel_decide

theorem certificate_360 :
    Certificate (table.cell ⟨360, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_360,
    crossing_of_check crossingCheck_360,
    scalar_of_check scalarCheck_360⟩

end Erdos1038.HighKPlatformConstantTableChunk360
