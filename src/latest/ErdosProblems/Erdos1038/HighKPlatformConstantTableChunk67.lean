import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 67 through 67. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk67

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_067 :
    geometryCheck (table.cell ⟨67, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_067 :
    crossingCheck (table.cell ⟨67, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_067 :
    scalarCheck (table.cell ⟨67, by decide⟩) = true := by
  kernel_decide

theorem certificate_067 :
    Certificate (table.cell ⟨67, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_067,
    crossing_of_check crossingCheck_067,
    scalar_of_check scalarCheck_067⟩

end Erdos1038.HighKPlatformConstantTableChunk67
