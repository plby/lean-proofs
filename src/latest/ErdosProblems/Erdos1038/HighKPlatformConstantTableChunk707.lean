import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 707 through 707. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk707

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_707 :
    geometryCheck (table.cell ⟨707, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_707 :
    crossingCheck (table.cell ⟨707, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_707 :
    scalarCheck (table.cell ⟨707, by decide⟩) = true := by
  kernel_decide

theorem certificate_707 :
    Certificate (table.cell ⟨707, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_707,
    crossing_of_check crossingCheck_707,
    scalar_of_check scalarCheck_707⟩

end Erdos1038.HighKPlatformConstantTableChunk707
