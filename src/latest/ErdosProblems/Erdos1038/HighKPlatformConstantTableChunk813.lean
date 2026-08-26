import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 813 through 813. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk813

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_813 :
    geometryCheck (table.cell ⟨813, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_813 :
    crossingCheck (table.cell ⟨813, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_813 :
    scalarCheck (table.cell ⟨813, by decide⟩) = true := by
  kernel_decide

theorem certificate_813 :
    Certificate (table.cell ⟨813, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_813,
    crossing_of_check crossingCheck_813,
    scalar_of_check scalarCheck_813⟩

end Erdos1038.HighKPlatformConstantTableChunk813
