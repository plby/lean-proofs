import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 759 through 759. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk759

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_759 :
    geometryCheck (table.cell ⟨759, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_759 :
    crossingCheck (table.cell ⟨759, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_759 :
    scalarCheck (table.cell ⟨759, by decide⟩) = true := by
  kernel_decide

theorem certificate_759 :
    Certificate (table.cell ⟨759, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_759,
    crossing_of_check crossingCheck_759,
    scalar_of_check scalarCheck_759⟩

end Erdos1038.HighKPlatformConstantTableChunk759
