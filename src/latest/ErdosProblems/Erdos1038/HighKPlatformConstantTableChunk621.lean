import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 621 through 621. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk621

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_621 :
    geometryCheck (table.cell ⟨621, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_621 :
    crossingCheck (table.cell ⟨621, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_621 :
    scalarCheck (table.cell ⟨621, by decide⟩) = true := by
  kernel_decide

theorem certificate_621 :
    Certificate (table.cell ⟨621, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_621,
    crossing_of_check crossingCheck_621,
    scalar_of_check scalarCheck_621⟩

end Erdos1038.HighKPlatformConstantTableChunk621
