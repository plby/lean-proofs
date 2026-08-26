import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 381 through 381. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk381

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_381 :
    geometryCheck (table.cell ⟨381, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_381 :
    crossingCheck (table.cell ⟨381, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_381 :
    scalarCheck (table.cell ⟨381, by decide⟩) = true := by
  kernel_decide

theorem certificate_381 :
    Certificate (table.cell ⟨381, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_381,
    crossing_of_check crossingCheck_381,
    scalar_of_check scalarCheck_381⟩

end Erdos1038.HighKPlatformConstantTableChunk381
