import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 588 through 588. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk588

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_588 :
    geometryCheck (table.cell ⟨588, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_588 :
    crossingCheck (table.cell ⟨588, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_588 :
    scalarCheck (table.cell ⟨588, by decide⟩) = true := by
  kernel_decide

theorem certificate_588 :
    Certificate (table.cell ⟨588, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_588,
    crossing_of_check crossingCheck_588,
    scalar_of_check scalarCheck_588⟩

end Erdos1038.HighKPlatformConstantTableChunk588
