import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 628 through 628. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk628

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_628 :
    geometryCheck (table.cell ⟨628, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_628 :
    crossingCheck (table.cell ⟨628, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_628 :
    scalarCheck (table.cell ⟨628, by decide⟩) = true := by
  kernel_decide

theorem certificate_628 :
    Certificate (table.cell ⟨628, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_628,
    crossing_of_check crossingCheck_628,
    scalar_of_check scalarCheck_628⟩

end Erdos1038.HighKPlatformConstantTableChunk628
