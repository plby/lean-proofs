import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 736 through 736. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk736

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_736 :
    geometryCheck (table.cell ⟨736, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_736 :
    crossingCheck (table.cell ⟨736, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_736 :
    scalarCheck (table.cell ⟨736, by decide⟩) = true := by
  kernel_decide

theorem certificate_736 :
    Certificate (table.cell ⟨736, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_736,
    crossing_of_check crossingCheck_736,
    scalar_of_check scalarCheck_736⟩

end Erdos1038.HighKPlatformConstantTableChunk736
