import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 30 through 30. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk30

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_030 :
    geometryCheck (table.cell ⟨30, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_030 :
    crossingCheck (table.cell ⟨30, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_030 :
    scalarCheck (table.cell ⟨30, by decide⟩) = true := by
  kernel_decide

theorem certificate_030 :
    Certificate (table.cell ⟨30, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_030,
    crossing_of_check crossingCheck_030,
    scalar_of_check scalarCheck_030⟩

end Erdos1038.HighKPlatformConstantTableChunk30
