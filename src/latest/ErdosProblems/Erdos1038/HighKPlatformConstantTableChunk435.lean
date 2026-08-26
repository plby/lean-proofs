import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 435 through 435. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk435

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_435 :
    geometryCheck (table.cell ⟨435, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_435 :
    crossingCheck (table.cell ⟨435, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_435 :
    scalarCheck (table.cell ⟨435, by decide⟩) = true := by
  kernel_decide

theorem certificate_435 :
    Certificate (table.cell ⟨435, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_435,
    crossing_of_check crossingCheck_435,
    scalar_of_check scalarCheck_435⟩

end Erdos1038.HighKPlatformConstantTableChunk435
