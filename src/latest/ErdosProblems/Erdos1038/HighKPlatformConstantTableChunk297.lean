import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 297 through 297. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk297

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_297 :
    geometryCheck (table.cell ⟨297, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_297 :
    crossingCheck (table.cell ⟨297, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_297 :
    scalarCheck (table.cell ⟨297, by decide⟩) = true := by
  kernel_decide

theorem certificate_297 :
    Certificate (table.cell ⟨297, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_297,
    crossing_of_check crossingCheck_297,
    scalar_of_check scalarCheck_297⟩

end Erdos1038.HighKPlatformConstantTableChunk297
