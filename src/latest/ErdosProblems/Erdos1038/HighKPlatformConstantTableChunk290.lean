import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 290 through 290. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk290

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_290 :
    geometryCheck (table.cell ⟨290, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_290 :
    crossingCheck (table.cell ⟨290, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_290 :
    scalarCheck (table.cell ⟨290, by decide⟩) = true := by
  kernel_decide

theorem certificate_290 :
    Certificate (table.cell ⟨290, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_290,
    crossing_of_check crossingCheck_290,
    scalar_of_check scalarCheck_290⟩

end Erdos1038.HighKPlatformConstantTableChunk290
