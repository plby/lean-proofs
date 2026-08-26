import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 604 through 604. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk604

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_604 :
    geometryCheck (table.cell ⟨604, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_604 :
    crossingCheck (table.cell ⟨604, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_604 :
    scalarCheck (table.cell ⟨604, by decide⟩) = true := by
  kernel_decide

theorem certificate_604 :
    Certificate (table.cell ⟨604, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_604,
    crossing_of_check crossingCheck_604,
    scalar_of_check scalarCheck_604⟩

end Erdos1038.HighKPlatformConstantTableChunk604
