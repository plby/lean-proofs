import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 208 through 208. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk208

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_208 :
    geometryCheck (table.cell ⟨208, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_208 :
    crossingCheck (table.cell ⟨208, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_208 :
    scalarCheck (table.cell ⟨208, by decide⟩) = true := by
  kernel_decide

theorem certificate_208 :
    Certificate (table.cell ⟨208, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_208,
    crossing_of_check crossingCheck_208,
    scalar_of_check scalarCheck_208⟩

end Erdos1038.HighKPlatformConstantTableChunk208
