import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 690 through 690. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk690

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_690 :
    geometryCheck (table.cell ⟨690, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_690 :
    crossingCheck (table.cell ⟨690, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_690 :
    scalarCheck (table.cell ⟨690, by decide⟩) = true := by
  kernel_decide

theorem certificate_690 :
    Certificate (table.cell ⟨690, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_690,
    crossing_of_check crossingCheck_690,
    scalar_of_check scalarCheck_690⟩

end Erdos1038.HighKPlatformConstantTableChunk690
