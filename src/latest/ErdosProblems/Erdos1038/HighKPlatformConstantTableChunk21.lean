import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 21 through 21. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk21

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_021 :
    geometryCheck (table.cell ⟨21, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_021 :
    crossingCheck (table.cell ⟨21, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_021 :
    scalarCheck (table.cell ⟨21, by decide⟩) = true := by
  kernel_decide

theorem certificate_021 :
    Certificate (table.cell ⟨21, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_021,
    crossing_of_check crossingCheck_021,
    scalar_of_check scalarCheck_021⟩

end Erdos1038.HighKPlatformConstantTableChunk21
