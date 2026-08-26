import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 645 through 645. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk645

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_645 :
    geometryCheck (table.cell ⟨645, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_645 :
    crossingCheck (table.cell ⟨645, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_645 :
    scalarCheck (table.cell ⟨645, by decide⟩) = true := by
  kernel_decide

theorem certificate_645 :
    Certificate (table.cell ⟨645, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_645,
    crossing_of_check crossingCheck_645,
    scalar_of_check scalarCheck_645⟩

end Erdos1038.HighKPlatformConstantTableChunk645
