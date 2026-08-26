import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 321 through 321. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk321

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_321 :
    geometryCheck (table.cell ⟨321, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_321 :
    crossingCheck (table.cell ⟨321, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_321 :
    scalarCheck (table.cell ⟨321, by decide⟩) = true := by
  kernel_decide

theorem certificate_321 :
    Certificate (table.cell ⟨321, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_321,
    crossing_of_check crossingCheck_321,
    scalar_of_check scalarCheck_321⟩

end Erdos1038.HighKPlatformConstantTableChunk321
