import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 408 through 408. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk408

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_408 :
    geometryCheck (table.cell ⟨408, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_408 :
    crossingCheck (table.cell ⟨408, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_408 :
    scalarCheck (table.cell ⟨408, by decide⟩) = true := by
  kernel_decide

theorem certificate_408 :
    Certificate (table.cell ⟨408, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_408,
    crossing_of_check crossingCheck_408,
    scalar_of_check scalarCheck_408⟩

end Erdos1038.HighKPlatformConstantTableChunk408
