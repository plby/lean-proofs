import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 196 through 196. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk196

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_196 :
    geometryCheck (table.cell ⟨196, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_196 :
    crossingCheck (table.cell ⟨196, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_196 :
    scalarCheck (table.cell ⟨196, by decide⟩) = true := by
  kernel_decide

theorem certificate_196 :
    Certificate (table.cell ⟨196, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_196,
    crossing_of_check crossingCheck_196,
    scalar_of_check scalarCheck_196⟩

end Erdos1038.HighKPlatformConstantTableChunk196
