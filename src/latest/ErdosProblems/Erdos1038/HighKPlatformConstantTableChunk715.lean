import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 715 through 715. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk715

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_715 :
    geometryCheck (table.cell ⟨715, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_715 :
    crossingCheck (table.cell ⟨715, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_715 :
    scalarCheck (table.cell ⟨715, by decide⟩) = true := by
  kernel_decide

theorem certificate_715 :
    Certificate (table.cell ⟨715, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_715,
    crossing_of_check crossingCheck_715,
    scalar_of_check scalarCheck_715⟩

end Erdos1038.HighKPlatformConstantTableChunk715
