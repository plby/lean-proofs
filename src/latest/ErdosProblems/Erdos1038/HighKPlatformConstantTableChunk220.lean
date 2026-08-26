import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 220 through 220. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk220

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_220 :
    geometryCheck (table.cell ⟨220, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_220 :
    crossingCheck (table.cell ⟨220, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_220 :
    scalarCheck (table.cell ⟨220, by decide⟩) = true := by
  kernel_decide

theorem certificate_220 :
    Certificate (table.cell ⟨220, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_220,
    crossing_of_check crossingCheck_220,
    scalar_of_check scalarCheck_220⟩

end Erdos1038.HighKPlatformConstantTableChunk220
