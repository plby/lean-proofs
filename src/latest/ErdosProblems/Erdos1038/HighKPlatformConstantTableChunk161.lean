import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 161 through 161. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk161

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_161 :
    geometryCheck (table.cell ⟨161, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_161 :
    crossingCheck (table.cell ⟨161, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_161 :
    scalarCheck (table.cell ⟨161, by decide⟩) = true := by
  kernel_decide

theorem certificate_161 :
    Certificate (table.cell ⟨161, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_161,
    crossing_of_check crossingCheck_161,
    scalar_of_check scalarCheck_161⟩

end Erdos1038.HighKPlatformConstantTableChunk161
