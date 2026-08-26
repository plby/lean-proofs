import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 259 through 259. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk259

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_259 :
    geometryCheck (table.cell ⟨259, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_259 :
    crossingCheck (table.cell ⟨259, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_259 :
    scalarCheck (table.cell ⟨259, by decide⟩) = true := by
  kernel_decide

theorem certificate_259 :
    Certificate (table.cell ⟨259, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_259,
    crossing_of_check crossingCheck_259,
    scalar_of_check scalarCheck_259⟩

end Erdos1038.HighKPlatformConstantTableChunk259
