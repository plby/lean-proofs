import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 331 through 331. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk331

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_331 :
    geometryCheck (table.cell ⟨331, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_331 :
    crossingCheck (table.cell ⟨331, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_331 :
    scalarCheck (table.cell ⟨331, by decide⟩) = true := by
  kernel_decide

theorem certificate_331 :
    Certificate (table.cell ⟨331, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_331,
    crossing_of_check crossingCheck_331,
    scalar_of_check scalarCheck_331⟩

end Erdos1038.HighKPlatformConstantTableChunk331
