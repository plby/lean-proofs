import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 541 through 541. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk541

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_541 :
    geometryCheck (table.cell ⟨541, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_541 :
    crossingCheck (table.cell ⟨541, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_541 :
    scalarCheck (table.cell ⟨541, by decide⟩) = true := by
  kernel_decide

theorem certificate_541 :
    Certificate (table.cell ⟨541, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_541,
    crossing_of_check crossingCheck_541,
    scalar_of_check scalarCheck_541⟩

end Erdos1038.HighKPlatformConstantTableChunk541
