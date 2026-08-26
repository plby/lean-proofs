import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 419 through 419. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk419

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_419 :
    geometryCheck (table.cell ⟨419, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_419 :
    crossingCheck (table.cell ⟨419, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_419 :
    scalarCheck (table.cell ⟨419, by decide⟩) = true := by
  kernel_decide

theorem certificate_419 :
    Certificate (table.cell ⟨419, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_419,
    crossing_of_check crossingCheck_419,
    scalar_of_check scalarCheck_419⟩

end Erdos1038.HighKPlatformConstantTableChunk419
