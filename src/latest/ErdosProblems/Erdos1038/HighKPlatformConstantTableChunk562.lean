import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 562 through 562. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk562

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_562 :
    geometryCheck (table.cell ⟨562, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_562 :
    crossingCheck (table.cell ⟨562, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_562 :
    scalarCheck (table.cell ⟨562, by decide⟩) = true := by
  kernel_decide

theorem certificate_562 :
    Certificate (table.cell ⟨562, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_562,
    crossing_of_check crossingCheck_562,
    scalar_of_check scalarCheck_562⟩

end Erdos1038.HighKPlatformConstantTableChunk562
