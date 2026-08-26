import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 185 through 185. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk185

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_185 :
    geometryCheck (table.cell ⟨185, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_185 :
    crossingCheck (table.cell ⟨185, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_185 :
    scalarCheck (table.cell ⟨185, by decide⟩) = true := by
  kernel_decide

theorem certificate_185 :
    Certificate (table.cell ⟨185, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_185,
    crossing_of_check crossingCheck_185,
    scalar_of_check scalarCheck_185⟩

end Erdos1038.HighKPlatformConstantTableChunk185
