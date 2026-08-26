import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 272 through 272. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk272

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_272 :
    geometryCheck (table.cell ⟨272, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_272 :
    crossingCheck (table.cell ⟨272, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_272 :
    scalarCheck (table.cell ⟨272, by decide⟩) = true := by
  kernel_decide

theorem certificate_272 :
    Certificate (table.cell ⟨272, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_272,
    crossing_of_check crossingCheck_272,
    scalar_of_check scalarCheck_272⟩

end Erdos1038.HighKPlatformConstantTableChunk272
