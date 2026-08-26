import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 96 through 96. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk96

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_096 :
    geometryCheck (table.cell ⟨96, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_096 :
    crossingCheck (table.cell ⟨96, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_096 :
    scalarCheck (table.cell ⟨96, by decide⟩) = true := by
  kernel_decide

theorem certificate_096 :
    Certificate (table.cell ⟨96, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_096,
    crossing_of_check crossingCheck_096,
    scalar_of_check scalarCheck_096⟩

end Erdos1038.HighKPlatformConstantTableChunk96
