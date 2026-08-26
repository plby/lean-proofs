import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 79 through 79. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk79

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_079 :
    geometryCheck (table.cell ⟨79, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_079 :
    crossingCheck (table.cell ⟨79, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_079 :
    scalarCheck (table.cell ⟨79, by decide⟩) = true := by
  kernel_decide

theorem certificate_079 :
    Certificate (table.cell ⟨79, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_079,
    crossing_of_check crossingCheck_079,
    scalar_of_check scalarCheck_079⟩

end Erdos1038.HighKPlatformConstantTableChunk79
