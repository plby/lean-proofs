import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 587 through 587. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk587

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_587 :
    geometryCheck (table.cell ⟨587, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_587 :
    crossingCheck (table.cell ⟨587, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_587 :
    scalarCheck (table.cell ⟨587, by decide⟩) = true := by
  kernel_decide

theorem certificate_587 :
    Certificate (table.cell ⟨587, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_587,
    crossing_of_check crossingCheck_587,
    scalar_of_check scalarCheck_587⟩

end Erdos1038.HighKPlatformConstantTableChunk587
