import ErdosProblems.Erdos1038.HighKPlatformConstantTableData
import ErdosProblems.Erdos1038.KernelDecision

/-! Proof-producing constant-edge cells 130 through 130. -/

set_option warningAsError false
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace Erdos1038.HighKPlatformConstantTableChunk130

open Erdos1038
open Erdos1038.HighKPlatformConstantCell
open Erdos1038.HighKPlatformConstantTableData

theorem geometryCheck_130 :
    geometryCheck (table.cell ⟨130, by decide⟩) = true := by
  kernel_decide

theorem crossingCheck_130 :
    crossingCheck (table.cell ⟨130, by decide⟩) = true := by
  kernel_decide

theorem scalarCheck_130 :
    scalarCheck (table.cell ⟨130, by decide⟩) = true := by
  kernel_decide

theorem certificate_130 :
    Certificate (table.cell ⟨130, by decide⟩) :=
  ⟨geometry_of_check geometryCheck_130,
    crossing_of_check crossingCheck_130,
    scalar_of_check scalarCheck_130⟩

end Erdos1038.HighKPlatformConstantTableChunk130
