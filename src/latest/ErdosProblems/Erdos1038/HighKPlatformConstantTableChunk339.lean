import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 339 through 339. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk339

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_339 :
    geometryCheck (table.cell ⟨339, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_339 :
    crossingCheck (table.cell ⟨339, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_339 :
    scalarCheck (table.cell ⟨339, by decide⟩) = true := by
  kernel_decide

theorem certificate_339 :
    Certificate (table.cell ⟨339, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_339,
    crossing_of_check crossingCheck_339,
    scalar_of_check scalarCheck_339⟩

end Erdos1038.HighKPlatformConstantTableChunk339
