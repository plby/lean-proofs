import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 194 through 194. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk194

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_194 :
    geometryCheck (table.cell ⟨194, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_194 :
    crossingCheck (table.cell ⟨194, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_194 :
    scalarCheck (table.cell ⟨194, by decide⟩) = true := by
  kernel_decide

theorem certificate_194 :
    Certificate (table.cell ⟨194, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_194,
    crossing_of_check crossingCheck_194,
    scalar_of_check scalarCheck_194⟩

end Erdos1038.HighKPlatformConstantTableChunk194
