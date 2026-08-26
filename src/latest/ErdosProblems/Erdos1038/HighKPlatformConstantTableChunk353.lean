import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 353 through 353. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk353

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_353 :
    geometryCheck (table.cell ⟨353, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_353 :
    crossingCheck (table.cell ⟨353, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_353 :
    scalarCheck (table.cell ⟨353, by decide⟩) = true := by
  kernel_decide

theorem certificate_353 :
    Certificate (table.cell ⟨353, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_353,
    crossing_of_check crossingCheck_353,
    scalar_of_check scalarCheck_353⟩

end Erdos1038.HighKPlatformConstantTableChunk353
