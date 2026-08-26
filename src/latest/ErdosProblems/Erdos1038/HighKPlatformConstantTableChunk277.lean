import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 277 through 277. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk277

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_277 :
    geometryCheck (table.cell ⟨277, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_277 :
    crossingCheck (table.cell ⟨277, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_277 :
    scalarCheck (table.cell ⟨277, by decide⟩) = true := by
  kernel_decide

theorem certificate_277 :
    Certificate (table.cell ⟨277, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_277,
    crossing_of_check crossingCheck_277,
    scalar_of_check scalarCheck_277⟩

end Erdos1038.HighKPlatformConstantTableChunk277
