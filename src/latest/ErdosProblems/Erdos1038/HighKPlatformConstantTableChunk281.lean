import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 281 through 281. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk281

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_281 :
    geometryCheck (table.cell ⟨281, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_281 :
    crossingCheck (table.cell ⟨281, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_281 :
    scalarCheck (table.cell ⟨281, by decide⟩) = true := by
  kernel_decide

theorem certificate_281 :
    Certificate (table.cell ⟨281, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_281,
    crossing_of_check crossingCheck_281,
    scalar_of_check scalarCheck_281⟩

end Erdos1038.HighKPlatformConstantTableChunk281
