import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 49 through 49. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk49

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_049 :
    geometryCheck (table.cell ⟨49, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_049 :
    crossingCheck (table.cell ⟨49, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_049 :
    scalarCheck (table.cell ⟨49, by decide⟩) = true := by
  kernel_decide

theorem certificate_049 :
    Certificate (table.cell ⟨49, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_049,
    crossing_of_check crossingCheck_049,
    scalar_of_check scalarCheck_049⟩

end Erdos1038.HighKPlatformConstantTableChunk49
