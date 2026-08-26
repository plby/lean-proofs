import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 18 through 18. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk18

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_018 :
    geometryCheck (table.cell ⟨18, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_018 :
    crossingCheck (table.cell ⟨18, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_018 :
    scalarCheck (table.cell ⟨18, by decide⟩) = true := by
  kernel_decide

theorem certificate_018 :
    Certificate (table.cell ⟨18, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_018,
    crossing_of_check crossingCheck_018,
    scalar_of_check scalarCheck_018⟩

end Erdos1038.HighKPlatformConstantTableChunk18
