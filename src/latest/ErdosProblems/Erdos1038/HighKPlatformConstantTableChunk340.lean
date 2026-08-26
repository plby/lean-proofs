import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 340 through 340. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk340

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_340 :
    geometryCheck (table.cell ⟨340, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_340 :
    crossingCheck (table.cell ⟨340, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_340 :
    scalarCheck (table.cell ⟨340, by decide⟩) = true := by
  kernel_decide

theorem certificate_340 :
    Certificate (table.cell ⟨340, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_340,
    crossing_of_check crossingCheck_340,
    scalar_of_check scalarCheck_340⟩

end Erdos1038.HighKPlatformConstantTableChunk340
