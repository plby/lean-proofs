import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 295 through 295. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk295

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_295 :
    geometryCheck (table.cell ⟨295, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_295 :
    crossingCheck (table.cell ⟨295, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_295 :
    scalarCheck (table.cell ⟨295, by decide⟩) = true := by
  kernel_decide

theorem certificate_295 :
    Certificate (table.cell ⟨295, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_295,
    crossing_of_check crossingCheck_295,
    scalar_of_check scalarCheck_295⟩

end Erdos1038.HighKPlatformConstantTableChunk295
