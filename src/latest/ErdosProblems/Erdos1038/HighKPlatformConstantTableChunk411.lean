import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 411 through 411. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk411

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_411 :
    geometryCheck (table.cell ⟨411, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_411 :
    crossingCheck (table.cell ⟨411, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_411 :
    scalarCheck (table.cell ⟨411, by decide⟩) = true := by
  kernel_decide

theorem certificate_411 :
    Certificate (table.cell ⟨411, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_411,
    crossing_of_check crossingCheck_411,
    scalar_of_check scalarCheck_411⟩

end Erdos1038.HighKPlatformConstantTableChunk411
