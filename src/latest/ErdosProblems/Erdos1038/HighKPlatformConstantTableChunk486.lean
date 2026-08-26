import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 486 through 486. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk486

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_486 :
    geometryCheck (table.cell ⟨486, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_486 :
    crossingCheck (table.cell ⟨486, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_486 :
    scalarCheck (table.cell ⟨486, by decide⟩) = true := by
  kernel_decide

theorem certificate_486 :
    Certificate (table.cell ⟨486, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_486,
    crossing_of_check crossingCheck_486,
    scalar_of_check scalarCheck_486⟩

end Erdos1038.HighKPlatformConstantTableChunk486
