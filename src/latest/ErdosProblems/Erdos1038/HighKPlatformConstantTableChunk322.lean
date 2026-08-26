import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 322 through 322. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk322

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_322 :
    geometryCheck (table.cell ⟨322, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_322 :
    crossingCheck (table.cell ⟨322, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_322 :
    scalarCheck (table.cell ⟨322, by decide⟩) = true := by
  kernel_decide

theorem certificate_322 :
    Certificate (table.cell ⟨322, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_322,
    crossing_of_check crossingCheck_322,
    scalar_of_check scalarCheck_322⟩

end Erdos1038.HighKPlatformConstantTableChunk322
