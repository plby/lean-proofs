import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 464 through 464. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk464

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_464 :
    geometryCheck (table.cell ⟨464, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_464 :
    crossingCheck (table.cell ⟨464, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_464 :
    scalarCheck (table.cell ⟨464, by decide⟩) = true := by
  kernel_decide

theorem certificate_464 :
    Certificate (table.cell ⟨464, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_464,
    crossing_of_check crossingCheck_464,
    scalar_of_check scalarCheck_464⟩

end Erdos1038.HighKPlatformConstantTableChunk464
