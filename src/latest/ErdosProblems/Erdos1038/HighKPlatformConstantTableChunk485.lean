import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 485 through 485. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk485

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_485 :
    geometryCheck (table.cell ⟨485, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_485 :
    crossingCheck (table.cell ⟨485, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_485 :
    scalarCheck (table.cell ⟨485, by decide⟩) = true := by
  kernel_decide

theorem certificate_485 :
    Certificate (table.cell ⟨485, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_485,
    crossing_of_check crossingCheck_485,
    scalar_of_check scalarCheck_485⟩

end Erdos1038.HighKPlatformConstantTableChunk485
