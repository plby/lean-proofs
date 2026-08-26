import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 153 through 153. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk153

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_153 :
    geometryCheck (table.cell ⟨153, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_153 :
    crossingCheck (table.cell ⟨153, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_153 :
    scalarCheck (table.cell ⟨153, by decide⟩) = true := by
  kernel_decide

theorem certificate_153 :
    Certificate (table.cell ⟨153, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_153,
    crossing_of_check crossingCheck_153,
    scalar_of_check scalarCheck_153⟩

end Erdos1038.HighKPlatformConstantTableChunk153
