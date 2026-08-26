import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 205 through 205. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk205

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_205 :
    geometryCheck (table.cell ⟨205, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_205 :
    crossingCheck (table.cell ⟨205, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_205 :
    scalarCheck (table.cell ⟨205, by decide⟩) = true := by
  kernel_decide

theorem certificate_205 :
    Certificate (table.cell ⟨205, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_205,
    crossing_of_check crossingCheck_205,
    scalar_of_check scalarCheck_205⟩

end Erdos1038.HighKPlatformConstantTableChunk205
