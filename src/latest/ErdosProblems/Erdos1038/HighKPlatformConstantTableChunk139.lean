import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 139 through 139. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk139

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_139 :
    geometryCheck (table.cell ⟨139, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_139 :
    crossingCheck (table.cell ⟨139, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_139 :
    scalarCheck (table.cell ⟨139, by decide⟩) = true := by
  kernel_decide

theorem certificate_139 :
    Certificate (table.cell ⟨139, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_139,
    crossing_of_check crossingCheck_139,
    scalar_of_check scalarCheck_139⟩

end Erdos1038.HighKPlatformConstantTableChunk139
