import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 266 through 266. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk266

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_266 :
    geometryCheck (table.cell ⟨266, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_266 :
    crossingCheck (table.cell ⟨266, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_266 :
    scalarCheck (table.cell ⟨266, by decide⟩) = true := by
  kernel_decide

theorem certificate_266 :
    Certificate (table.cell ⟨266, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_266,
    crossing_of_check crossingCheck_266,
    scalar_of_check scalarCheck_266⟩

end Erdos1038.HighKPlatformConstantTableChunk266
