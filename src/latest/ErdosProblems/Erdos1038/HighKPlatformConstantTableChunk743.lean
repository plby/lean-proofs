import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 743 through 743. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk743

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_743 :
    geometryCheck (table.cell ⟨743, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_743 :
    crossingCheck (table.cell ⟨743, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_743 :
    scalarCheck (table.cell ⟨743, by decide⟩) = true := by
  kernel_decide

theorem certificate_743 :
    Certificate (table.cell ⟨743, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_743,
    crossing_of_check crossingCheck_743,
    scalar_of_check scalarCheck_743⟩

end Erdos1038.HighKPlatformConstantTableChunk743
