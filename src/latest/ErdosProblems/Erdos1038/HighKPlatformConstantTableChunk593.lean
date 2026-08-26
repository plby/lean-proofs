import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 593 through 593. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk593

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_593 :
    geometryCheck (table.cell ⟨593, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_593 :
    crossingCheck (table.cell ⟨593, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_593 :
    scalarCheck (table.cell ⟨593, by decide⟩) = true := by
  kernel_decide

theorem certificate_593 :
    Certificate (table.cell ⟨593, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_593,
    crossing_of_check crossingCheck_593,
    scalar_of_check scalarCheck_593⟩

end Erdos1038.HighKPlatformConstantTableChunk593
