import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 348 through 348. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk348

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_348 :
    geometryCheck (table.cell ⟨348, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_348 :
    crossingCheck (table.cell ⟨348, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_348 :
    scalarCheck (table.cell ⟨348, by decide⟩) = true := by
  kernel_decide

theorem certificate_348 :
    Certificate (table.cell ⟨348, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_348,
    crossing_of_check crossingCheck_348,
    scalar_of_check scalarCheck_348⟩

end Erdos1038.HighKPlatformConstantTableChunk348
