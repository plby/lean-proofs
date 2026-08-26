import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 45 through 45. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk45

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_045 :
    geometryCheck (table.cell ⟨45, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_045 :
    crossingCheck (table.cell ⟨45, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_045 :
    scalarCheck (table.cell ⟨45, by decide⟩) = true := by
  kernel_decide

theorem certificate_045 :
    Certificate (table.cell ⟨45, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_045,
    crossing_of_check crossingCheck_045,
    scalar_of_check scalarCheck_045⟩

end Erdos1038.HighKPlatformConstantTableChunk45
