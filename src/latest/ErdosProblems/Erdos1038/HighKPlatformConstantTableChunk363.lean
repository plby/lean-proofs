import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 363 through 363. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk363

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_363 :
    geometryCheck (table.cell ⟨363, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_363 :
    crossingCheck (table.cell ⟨363, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_363 :
    scalarCheck (table.cell ⟨363, by decide⟩) = true := by
  kernel_decide

theorem certificate_363 :
    Certificate (table.cell ⟨363, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_363,
    crossing_of_check crossingCheck_363,
    scalar_of_check scalarCheck_363⟩

end Erdos1038.HighKPlatformConstantTableChunk363
