import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 804 through 804. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk804

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_804 :
    geometryCheck (table.cell ⟨804, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_804 :
    crossingCheck (table.cell ⟨804, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_804 :
    scalarCheck (table.cell ⟨804, by decide⟩) = true := by
  kernel_decide

theorem certificate_804 :
    Certificate (table.cell ⟨804, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_804,
    crossing_of_check crossingCheck_804,
    scalar_of_check scalarCheck_804⟩

end Erdos1038.HighKPlatformConstantTableChunk804
