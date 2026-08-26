import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 538 through 538. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk538

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_538 :
    geometryCheck (table.cell ⟨538, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_538 :
    crossingCheck (table.cell ⟨538, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_538 :
    scalarCheck (table.cell ⟨538, by decide⟩) = true := by
  kernel_decide

theorem certificate_538 :
    Certificate (table.cell ⟨538, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_538,
    crossing_of_check crossingCheck_538,
    scalar_of_check scalarCheck_538⟩

end Erdos1038.HighKPlatformConstantTableChunk538
