import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 613 through 613. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk613

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_613 :
    geometryCheck (table.cell ⟨613, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_613 :
    crossingCheck (table.cell ⟨613, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_613 :
    scalarCheck (table.cell ⟨613, by decide⟩) = true := by
  kernel_decide

theorem certificate_613 :
    Certificate (table.cell ⟨613, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_613,
    crossing_of_check crossingCheck_613,
    scalar_of_check scalarCheck_613⟩

end Erdos1038.HighKPlatformConstantTableChunk613
