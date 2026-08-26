import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 708 through 708. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk708

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_708 :
    geometryCheck (table.cell ⟨708, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_708 :
    crossingCheck (table.cell ⟨708, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_708 :
    scalarCheck (table.cell ⟨708, by decide⟩) = true := by
  kernel_decide

theorem certificate_708 :
    Certificate (table.cell ⟨708, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_708,
    crossing_of_check crossingCheck_708,
    scalar_of_check scalarCheck_708⟩

end Erdos1038.HighKPlatformConstantTableChunk708
