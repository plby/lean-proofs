import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 459 through 459. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk459

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_459 :
    geometryCheck (table.cell ⟨459, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_459 :
    crossingCheck (table.cell ⟨459, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_459 :
    scalarCheck (table.cell ⟨459, by decide⟩) = true := by
  kernel_decide

theorem certificate_459 :
    Certificate (table.cell ⟨459, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_459,
    crossing_of_check crossingCheck_459,
    scalar_of_check scalarCheck_459⟩

end Erdos1038.HighKPlatformConstantTableChunk459
