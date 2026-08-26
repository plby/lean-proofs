import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 446 through 446. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk446

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_446 :
    geometryCheck (table.cell ⟨446, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_446 :
    crossingCheck (table.cell ⟨446, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_446 :
    scalarCheck (table.cell ⟨446, by decide⟩) = true := by
  kernel_decide

theorem certificate_446 :
    Certificate (table.cell ⟨446, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_446,
    crossing_of_check crossingCheck_446,
    scalar_of_check scalarCheck_446⟩

end Erdos1038.HighKPlatformConstantTableChunk446
