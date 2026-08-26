import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 383 through 383. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk383

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_383 :
    geometryCheck (table.cell ⟨383, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_383 :
    crossingCheck (table.cell ⟨383, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_383 :
    scalarCheck (table.cell ⟨383, by decide⟩) = true := by
  kernel_decide

theorem certificate_383 :
    Certificate (table.cell ⟨383, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_383,
    crossing_of_check crossingCheck_383,
    scalar_of_check scalarCheck_383⟩

end Erdos1038.HighKPlatformConstantTableChunk383
