import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 240 through 240. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk240

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_240 :
    geometryCheck (table.cell ⟨240, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_240 :
    crossingCheck (table.cell ⟨240, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_240 :
    scalarCheck (table.cell ⟨240, by decide⟩) = true := by
  kernel_decide

theorem certificate_240 :
    Certificate (table.cell ⟨240, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_240,
    crossing_of_check crossingCheck_240,
    scalar_of_check scalarCheck_240⟩

end Erdos1038.HighKPlatformConstantTableChunk240
