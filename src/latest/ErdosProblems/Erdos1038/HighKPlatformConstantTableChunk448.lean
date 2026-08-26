import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 448 through 448. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk448

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_448 :
    geometryCheck (table.cell ⟨448, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_448 :
    crossingCheck (table.cell ⟨448, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_448 :
    scalarCheck (table.cell ⟨448, by decide⟩) = true := by
  kernel_decide

theorem certificate_448 :
    Certificate (table.cell ⟨448, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_448,
    crossing_of_check crossingCheck_448,
    scalar_of_check scalarCheck_448⟩

end Erdos1038.HighKPlatformConstantTableChunk448
