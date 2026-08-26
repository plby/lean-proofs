import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 467 through 467. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk467

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_467 :
    geometryCheck (table.cell ⟨467, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_467 :
    crossingCheck (table.cell ⟨467, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_467 :
    scalarCheck (table.cell ⟨467, by decide⟩) = true := by
  kernel_decide

theorem certificate_467 :
    Certificate (table.cell ⟨467, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_467,
    crossing_of_check crossingCheck_467,
    scalar_of_check scalarCheck_467⟩

end Erdos1038.HighKPlatformConstantTableChunk467
