import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 276 through 276. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk276

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_276 :
    geometryCheck (table.cell ⟨276, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_276 :
    crossingCheck (table.cell ⟨276, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_276 :
    scalarCheck (table.cell ⟨276, by decide⟩) = true := by
  kernel_decide

theorem certificate_276 :
    Certificate (table.cell ⟨276, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_276,
    crossing_of_check crossingCheck_276,
    scalar_of_check scalarCheck_276⟩

end Erdos1038.HighKPlatformConstantTableChunk276
