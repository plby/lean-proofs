import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 302 through 302. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk302

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_302 :
    geometryCheck (table.cell ⟨302, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_302 :
    crossingCheck (table.cell ⟨302, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_302 :
    scalarCheck (table.cell ⟨302, by decide⟩) = true := by
  kernel_decide

theorem certificate_302 :
    Certificate (table.cell ⟨302, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_302,
    crossing_of_check crossingCheck_302,
    scalar_of_check scalarCheck_302⟩

end Erdos1038.HighKPlatformConstantTableChunk302
