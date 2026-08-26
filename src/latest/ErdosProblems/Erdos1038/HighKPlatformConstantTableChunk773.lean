import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 773 through 773. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk773

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_773 :
    geometryCheck (table.cell ⟨773, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_773 :
    crossingCheck (table.cell ⟨773, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_773 :
    scalarCheck (table.cell ⟨773, by decide⟩) = true := by
  kernel_decide

theorem certificate_773 :
    Certificate (table.cell ⟨773, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_773,
    crossing_of_check crossingCheck_773,
    scalar_of_check scalarCheck_773⟩

end Erdos1038.HighKPlatformConstantTableChunk773
