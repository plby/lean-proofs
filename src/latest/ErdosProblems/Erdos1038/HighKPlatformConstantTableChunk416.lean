import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 416 through 416. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk416

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_416 :
    geometryCheck (table.cell ⟨416, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_416 :
    crossingCheck (table.cell ⟨416, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_416 :
    scalarCheck (table.cell ⟨416, by decide⟩) = true := by
  kernel_decide

theorem certificate_416 :
    Certificate (table.cell ⟨416, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_416,
    crossing_of_check crossingCheck_416,
    scalar_of_check scalarCheck_416⟩

end Erdos1038.HighKPlatformConstantTableChunk416
