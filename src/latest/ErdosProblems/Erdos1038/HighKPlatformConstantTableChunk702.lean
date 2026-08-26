import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 702 through 702. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk702

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_702 :
    geometryCheck (table.cell ⟨702, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_702 :
    crossingCheck (table.cell ⟨702, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_702 :
    scalarCheck (table.cell ⟨702, by decide⟩) = true := by
  kernel_decide

theorem certificate_702 :
    Certificate (table.cell ⟨702, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_702,
    crossing_of_check crossingCheck_702,
    scalar_of_check scalarCheck_702⟩

end Erdos1038.HighKPlatformConstantTableChunk702
