import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 324 through 324. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk324

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_324 :
    geometryCheck (table.cell ⟨324, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_324 :
    crossingCheck (table.cell ⟨324, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_324 :
    scalarCheck (table.cell ⟨324, by decide⟩) = true := by
  kernel_decide

theorem certificate_324 :
    Certificate (table.cell ⟨324, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_324,
    crossing_of_check crossingCheck_324,
    scalar_of_check scalarCheck_324⟩

end Erdos1038.HighKPlatformConstantTableChunk324
