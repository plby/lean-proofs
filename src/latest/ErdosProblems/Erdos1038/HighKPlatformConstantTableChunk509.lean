import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 509 through 509. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk509

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_509 :
    geometryCheck (table.cell ⟨509, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_509 :
    crossingCheck (table.cell ⟨509, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_509 :
    scalarCheck (table.cell ⟨509, by decide⟩) = true := by
  kernel_decide

theorem certificate_509 :
    Certificate (table.cell ⟨509, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_509,
    crossing_of_check crossingCheck_509,
    scalar_of_check scalarCheck_509⟩

end Erdos1038.HighKPlatformConstantTableChunk509
