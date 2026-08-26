import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 344 through 344. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk344

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_344 :
    geometryCheck (table.cell ⟨344, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_344 :
    crossingCheck (table.cell ⟨344, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_344 :
    scalarCheck (table.cell ⟨344, by decide⟩) = true := by
  kernel_decide

theorem certificate_344 :
    Certificate (table.cell ⟨344, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_344,
    crossing_of_check crossingCheck_344,
    scalar_of_check scalarCheck_344⟩

end Erdos1038.HighKPlatformConstantTableChunk344
