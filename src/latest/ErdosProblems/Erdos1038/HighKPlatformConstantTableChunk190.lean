import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 190 through 190. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk190

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_190 :
    geometryCheck (table.cell ⟨190, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_190 :
    crossingCheck (table.cell ⟨190, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_190 :
    scalarCheck (table.cell ⟨190, by decide⟩) = true := by
  kernel_decide

theorem certificate_190 :
    Certificate (table.cell ⟨190, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_190,
    crossing_of_check crossingCheck_190,
    scalar_of_check scalarCheck_190⟩

end Erdos1038.HighKPlatformConstantTableChunk190
