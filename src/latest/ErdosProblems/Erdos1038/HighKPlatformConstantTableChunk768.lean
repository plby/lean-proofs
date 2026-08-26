import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 768 through 768. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk768

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_768 :
    geometryCheck (table.cell ⟨768, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_768 :
    crossingCheck (table.cell ⟨768, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_768 :
    scalarCheck (table.cell ⟨768, by decide⟩) = true := by
  kernel_decide

theorem certificate_768 :
    Certificate (table.cell ⟨768, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_768,
    crossing_of_check crossingCheck_768,
    scalar_of_check scalarCheck_768⟩

end Erdos1038.HighKPlatformConstantTableChunk768
