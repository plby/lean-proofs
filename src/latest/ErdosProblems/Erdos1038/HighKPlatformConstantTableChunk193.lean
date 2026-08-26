import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 193 through 193. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk193

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_193 :
    geometryCheck (table.cell ⟨193, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_193 :
    crossingCheck (table.cell ⟨193, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_193 :
    scalarCheck (table.cell ⟨193, by decide⟩) = true := by
  kernel_decide

theorem certificate_193 :
    Certificate (table.cell ⟨193, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_193,
    crossing_of_check crossingCheck_193,
    scalar_of_check scalarCheck_193⟩

end Erdos1038.HighKPlatformConstantTableChunk193
