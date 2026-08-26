import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 5 through 5. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk05

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_005 :
    geometryCheck (table.cell ⟨5, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_005 :
    crossingCheck (table.cell ⟨5, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_005 :
    scalarCheck (table.cell ⟨5, by decide⟩) = true := by
  kernel_decide

theorem certificate_005 :
    Certificate (table.cell ⟨5, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_005,
    crossing_of_check crossingCheck_005,
    scalar_of_check scalarCheck_005⟩

end Erdos1038.HighKPlatformConstantTableChunk05
