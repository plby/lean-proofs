import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 317 through 317. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk317

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_317 :
    geometryCheck (table.cell ⟨317, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_317 :
    crossingCheck (table.cell ⟨317, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_317 :
    scalarCheck (table.cell ⟨317, by decide⟩) = true := by
  kernel_decide

theorem certificate_317 :
    Certificate (table.cell ⟨317, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_317,
    crossing_of_check crossingCheck_317,
    scalar_of_check scalarCheck_317⟩

end Erdos1038.HighKPlatformConstantTableChunk317
