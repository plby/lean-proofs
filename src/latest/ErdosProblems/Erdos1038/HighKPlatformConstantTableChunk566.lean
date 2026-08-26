import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 566 through 566. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk566

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_566 :
    geometryCheck (table.cell ⟨566, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_566 :
    crossingCheck (table.cell ⟨566, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_566 :
    scalarCheck (table.cell ⟨566, by decide⟩) = true := by
  kernel_decide

theorem certificate_566 :
    Certificate (table.cell ⟨566, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_566,
    crossing_of_check crossingCheck_566,
    scalar_of_check scalarCheck_566⟩

end Erdos1038.HighKPlatformConstantTableChunk566
