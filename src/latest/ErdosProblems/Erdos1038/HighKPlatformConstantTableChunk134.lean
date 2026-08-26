import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 134 through 134. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk134

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_134 :
    geometryCheck (table.cell ⟨134, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_134 :
    crossingCheck (table.cell ⟨134, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_134 :
    scalarCheck (table.cell ⟨134, by decide⟩) = true := by
  kernel_decide

theorem certificate_134 :
    Certificate (table.cell ⟨134, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_134,
    crossing_of_check crossingCheck_134,
    scalar_of_check scalarCheck_134⟩

end Erdos1038.HighKPlatformConstantTableChunk134
