import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 136 through 136. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk136

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_136 :
    geometryCheck (table.cell ⟨136, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_136 :
    crossingCheck (table.cell ⟨136, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_136 :
    scalarCheck (table.cell ⟨136, by decide⟩) = true := by
  kernel_decide

theorem certificate_136 :
    Certificate (table.cell ⟨136, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_136,
    crossing_of_check crossingCheck_136,
    scalar_of_check scalarCheck_136⟩

end Erdos1038.HighKPlatformConstantTableChunk136
